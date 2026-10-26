import V185TrunkScan23Chunk0096

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_575397 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 8]
def baseStart_575397 : Nat := 118140960795 + 575397 * 2 ^ 59
def prefixEnd_575397 : Nat := 4983230072969 + 3 ^ 40 * 575397 * 2
def baseEnd_575397 : Nat := 295455228155190490291303

theorem tailTrace_575397 : CollatzResearch.WordTrace tailWord_575397 prefixEnd_575397 295455228155190490291303 := by
  unfold tailWord_575397
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986452696442413829036445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13990968464294942552690963 20986452696442413829036445)
  ·
    refine ⟨7869919761165905185888667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20986452696442413829036445 7869919761165905185888667)
    ·
      refine ⟨11804879641748857778833001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7869919761165905185888667 11804879641748857778833001)
      ·
        refine ⟨8853659731311643334124751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11804879641748857778833001 8853659731311643334124751)
        ·
          refine ⟨13280489596967465001187127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8853659731311643334124751 13280489596967465001187127)
          ·
            refine ⟨19920734395451197501780691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13280489596967465001187127 19920734395451197501780691)
            ·
              refine ⟨29881101593176796252671037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19920734395451197501780691 29881101593176796252671037)
              ·
                refine ⟨11205413097441298594751639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29881101593176796252671037 11205413097441298594751639)
                ·
                  refine ⟨16808119646161947892127459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11205413097441298594751639 16808119646161947892127459)
                  ·
                    refine ⟨25212179469242921838191189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16808119646161947892127459 25212179469242921838191189)
                    ·
                      refine ⟨295455228155190490291303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 25212179469242921838191189 295455228155190490291303)
                      ·
                        rfl

theorem cell23_575397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_575397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575397 prefixEnd_575397 := by exact prefixLift 575397
  have htrace : WordTrace (prefixWord ++ tailWord_575397) baseStart_575397 baseEnd_575397 := by
    simpa [prefixWord, tailWord_575397, baseEnd_575397] using wordTrace_append hprefix tailTrace_575397
  have hstable : (prefixWord ++ tailWord_575397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575397).length < 2 ^ (prefixWord ++ tailWord_575397).sum := by decide
  have hdescent : baseEnd_575397 < baseStart_575397 := by decide
  rcases family_descends (prefixWord ++ tailWord_575397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575424 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_575424 : Nat := 118140960795 + 575424 * 2 ^ 59
def prefixEnd_575424 : Nat := 4983230072969 + 3 ^ 40 * 575424 * 2
def baseEnd_575424 : Nat := 98489697377620628217893

theorem tailTrace_575424 : CollatzResearch.WordTrace tailWord_575424 prefixEnd_575424 98489697377620628217893 := by
  unfold tailWord_575424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493718733672298720134663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13991624978229731626846217 10493718733672298720134663)
  ·
    refine ⟨15740578100508448080201995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10493718733672298720134663 15740578100508448080201995)
    ·
      refine ⟨23610867150762672120302993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15740578100508448080201995 23610867150762672120302993)
      ·
        refine ⟨17708150363072004090227245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23610867150762672120302993 17708150363072004090227245)
        ·
          refine ⟨6640556386152001533835217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17708150363072004090227245 6640556386152001533835217)
          ·
            refine ⟨4980417289614001150376413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6640556386152001533835217 4980417289614001150376413)
            ·
              refine ⟨1867656483605250431391155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4980417289614001150376413 1867656483605250431391155)
              ·
                refine ⟨2801484725407875647086733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867656483605250431391155 2801484725407875647086733)
                ·
                  refine ⟨1050556772027953367657525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2801484725407875647086733 1050556772027953367657525)
                  ·
                    refine ⟨98489697377620628217893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1050556772027953367657525 98489697377620628217893)
                    ·
                      rfl

theorem cell23_575424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_575424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575424 prefixEnd_575424 := by exact prefixLift 575424
  have htrace : WordTrace (prefixWord ++ tailWord_575424) baseStart_575424 baseEnd_575424 := by
    simpa [prefixWord, tailWord_575424, baseEnd_575424] using wordTrace_append hprefix tailTrace_575424
  have hstable : (prefixWord ++ tailWord_575424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575424).length < 2 ^ (prefixWord ++ tailWord_575424).sum := by decide
  have hdescent : baseEnd_575424 < baseStart_575424 := by decide
  rcases family_descends (prefixWord ++ tailWord_575424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575455 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 1, 1, 3]
def baseStart_575455 : Nat := 118140960795 + 575455 * 2 ^ 59
def prefixEnd_575455 : Nat := 4983230072969 + 3 ^ 40 * 575455 * 2
def baseEnd_575455 : Nat := 295485010033151263366037

theorem tailTrace_575455 : CollatzResearch.WordTrace tailWord_575455 prefixEnd_575455 295485010033151263366037 := by
  unfold tailWord_575455
  simp only [CollatzResearch.WordTrace]
  refine ⟨20988568130232289734647819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13992378753488193156431879 20988568130232289734647819)
  ·
    refine ⟨31482852195348434601971729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20988568130232289734647819 31482852195348434601971729)
    ·
      refine ⟨23612139146511325951478797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31482852195348434601971729 23612139146511325951478797)
      ·
        refine ⟨8854552179941747231804549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23612139146511325951478797 8854552179941747231804549)
        ·
          refine ⟨1660228533739077605963353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8854552179941747231804549 1660228533739077605963353)
          ·
            refine ⟨1245171400304308204472515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1660228533739077605963353 1245171400304308204472515)
            ·
              refine ⟨1867757100456462306708773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245171400304308204472515 1867757100456462306708773)
              ·
                refine ⟨350204456335586682507895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1867757100456462306708773 350204456335586682507895)
                ·
                  refine ⟨525306684503380023761843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350204456335586682507895 525306684503380023761843)
                  ·
                    refine ⟨787960026755070035642765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 525306684503380023761843 787960026755070035642765)
                    ·
                      refine ⟨295485010033151263366037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787960026755070035642765 295485010033151263366037)
                      ·
                        rfl

theorem cell23_575455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_575455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575455 prefixEnd_575455 := by exact prefixLift 575455
  have htrace : WordTrace (prefixWord ++ tailWord_575455) baseStart_575455 baseEnd_575455 := by
    simpa [prefixWord, tailWord_575455, baseEnd_575455] using wordTrace_append hprefix tailTrace_575455
  have hstable : (prefixWord ++ tailWord_575455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575455).length < 2 ^ (prefixWord ++ tailWord_575455).sum := by decide
  have hdescent : baseEnd_575455 < baseStart_575455 := by decide
  rcases family_descends (prefixWord ++ tailWord_575455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575464 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_575464 : Nat := 118140960795 + 575464 * 2 ^ 59
def prefixEnd_575464 : Nat := 4983230072969 + 3 ^ 40 * 575464 * 2
def baseEnd_575464 : Nat := 295489631359041728153495

theorem tailTrace_575464 : CollatzResearch.WordTrace tailWord_575464 prefixEnd_575464 295489631359041728153495 := by
  unfold tailWord_575464
  simp only [CollatzResearch.WordTrace]
  refine ⟨10494448193599842135862723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13992597591466456181150297 10494448193599842135862723)
  ·
    refine ⟨15741672290399763203794085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10494448193599842135862723 15741672290399763203794085)
    ·
      refine ⟨2951563554449955600711391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15741672290399763203794085 2951563554449955600711391)
      ·
        refine ⟨4427345331674933401067087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951563554449955600711391 4427345331674933401067087)
        ·
          refine ⟨6641017997512400101600631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4427345331674933401067087 6641017997512400101600631)
          ·
            refine ⟨9961526996268600152400947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641017997512400101600631 9961526996268600152400947)
            ·
              refine ⟨14942290494402900228601421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9961526996268600152400947 14942290494402900228601421)
              ·
                refine ⟨5603358935401087585725533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14942290494402900228601421 5603358935401087585725533)
                ·
                  refine ⟨2101259600775407844647075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5603358935401087585725533 2101259600775407844647075)
                  ·
                    refine ⟨3151889401163111766970613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2101259600775407844647075 3151889401163111766970613)
                    ·
                      refine ⟨295489631359041728153495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3151889401163111766970613 295489631359041728153495)
                      ·
                        rfl

theorem cell23_575464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_575464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575464 prefixEnd_575464 := by exact prefixLift 575464
  have htrace : WordTrace (prefixWord ++ tailWord_575464) baseStart_575464 baseEnd_575464 := by
    simpa [prefixWord, tailWord_575464, baseEnd_575464] using wordTrace_append hprefix tailTrace_575464
  have hstable : (prefixWord ++ tailWord_575464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575464).length < 2 ^ (prefixWord ++ tailWord_575464).sum := by decide
  have hdescent : baseEnd_575464 < baseStart_575464 := by decide
  rcases family_descends (prefixWord ++ tailWord_575464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575471 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 2, 4]
def baseStart_575471 : Nat := 118140960795 + 575471 * 2 ^ 59
def prefixEnd_575471 : Nat := 4983230072969 + 3 ^ 40 * 575471 * 2
def baseEnd_575471 : Nat := 98497741907874400255321

theorem tailTrace_575471 : CollatzResearch.WordTrace tailWord_575471 prefixEnd_575471 98497741907874400255321 := by
  unfold tailWord_575471
  simp only [CollatzResearch.WordTrace]
  refine ⟨20989151698174324467230267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13992767798782882978153511 20989151698174324467230267)
  ·
    refine ⟨31483727547261486700845401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20989151698174324467230267 31483727547261486700845401)
    ·
      refine ⟨23612795660446115025634051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31483727547261486700845401 23612795660446115025634051)
      ·
        refine ⟨35419193490669172538451077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23612795660446115025634051 35419193490669172538451077)
        ·
          refine ⟨6641098779500469850959577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35419193490669172538451077 6641098779500469850959577)
          ·
            refine ⟨4980824084625352388219683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6641098779500469850959577 4980824084625352388219683)
            ·
              refine ⟨7471236126938028582329525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980824084625352388219683 7471236126938028582329525)
              ·
                refine ⟨700428386900440179593393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7471236126938028582329525 700428386900440179593393)
                ·
                  refine ⟨525321290175330134695045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 700428386900440179593393 525321290175330134695045)
                  ·
                    refine ⟨98497741907874400255321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525321290175330134695045 98497741907874400255321)
                    ·
                      rfl

theorem cell23_575471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_575471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575471 prefixEnd_575471 := by exact prefixLift 575471
  have htrace : WordTrace (prefixWord ++ tailWord_575471) baseStart_575471 baseEnd_575471 := by
    simpa [prefixWord, tailWord_575471, baseEnd_575471] using wordTrace_append hprefix tailTrace_575471
  have hstable : (prefixWord ++ tailWord_575471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575471).length < 2 ^ (prefixWord ++ tailWord_575471).sum := by decide
  have hdescent : baseEnd_575471 < baseStart_575471 := by decide
  rcases family_descends (prefixWord ++ tailWord_575471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575481 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_575481 : Nat := 118140960795 + 575481 * 2 ^ 59
def prefixEnd_575481 : Nat := 4983230072969 + 3 ^ 40 * 575481 * 2
def baseEnd_575481 : Nat := 295498360530168161640917

theorem tailTrace_575481 : CollatzResearch.WordTrace tailWord_575481 prefixEnd_575481 295498360530168161640917 := by
  unfold tailWord_575481
  simp only [CollatzResearch.WordTrace]
  refine ⟨20989516428138096175094297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13993010952092064116729531 20989516428138096175094297)
  ·
    refine ⟨15742137321103572131320723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20989516428138096175094297 15742137321103572131320723)
    ·
      refine ⟨23613205981655358196981085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15742137321103572131320723 23613205981655358196981085)
      ·
        refine ⟨8854952243120759323867907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23613205981655358196981085 8854952243120759323867907)
        ·
          refine ⟨13282428364681138985801861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8854952243120759323867907 13282428364681138985801861)
          ·
            refine ⟨2490455318377713559837849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13282428364681138985801861 2490455318377713559837849)
            ·
              refine ⟨1867841488783285169878387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2490455318377713559837849 1867841488783285169878387)
              ·
                refine ⟨2801762233174927754817581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1867841488783285169878387 2801762233174927754817581)
                ·
                  refine ⟨1050660837440597908056593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2801762233174927754817581 1050660837440597908056593)
                  ·
                    refine ⟨787995628080448431042445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1050660837440597908056593 787995628080448431042445)
                    ·
                      refine ⟨295498360530168161640917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 787995628080448431042445 295498360530168161640917)
                      ·
                        rfl

theorem cell23_575481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_575481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575481 prefixEnd_575481 := by exact prefixLift 575481
  have htrace : WordTrace (prefixWord ++ tailWord_575481) baseStart_575481 baseEnd_575481 := by
    simpa [prefixWord, tailWord_575481, baseEnd_575481] using wordTrace_append hprefix tailTrace_575481
  have hstable : (prefixWord ++ tailWord_575481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575481).length < 2 ^ (prefixWord ++ tailWord_575481).sum := by decide
  have hdescent : baseEnd_575481 < baseStart_575481 := by decide
  rcases family_descends (prefixWord ++ tailWord_575481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575492 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_575492 : Nat := 118140960795 + 575492 * 2 ^ 59
def prefixEnd_575492 : Nat := 4983230072969 + 3 ^ 40 * 575492 * 2
def baseEnd_575492 : Nat := 98501336272455872867789

theorem tailTrace_575492 : CollatzResearch.WordTrace tailWord_575492 prefixEnd_575492 98501336272455872867789 := by
  unfold tailWord_575492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10494958815549122526872365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13993278420732163369163153 10494958815549122526872365)
  ·
    refine ⟨3935609555830920947577137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10494958815549122526872365 3935609555830920947577137)
    ·
      refine ⟨2951707166873190710682853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3935609555830920947577137 2951707166873190710682853)
      ·
        refine ⟨553445093788723258253035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2951707166873190710682853 553445093788723258253035)
        ·
          refine ⟨830167640683084887379553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553445093788723258253035 830167640683084887379553)
          ·
            refine ⟨622625730512313665534665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830167640683084887379553 622625730512313665534665)
            ·
              refine ⟨466969297884235249150999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622625730512313665534665 466969297884235249150999)
              ·
                refine ⟨700453946826352873726499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466969297884235249150999 700453946826352873726499)
                ·
                  refine ⟨1050680920239529310589749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700453946826352873726499 1050680920239529310589749)
                  ·
                    refine ⟨98501336272455872867789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1050680920239529310589749 98501336272455872867789)
                    ·
                      rfl

theorem cell23_575492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_575492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575492 prefixEnd_575492 := by exact prefixLift 575492
  have htrace : WordTrace (prefixWord ++ tailWord_575492) baseStart_575492 baseEnd_575492 := by
    simpa [prefixWord, tailWord_575492, baseEnd_575492] using wordTrace_append hprefix tailTrace_575492
  have hstable : (prefixWord ++ tailWord_575492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575492).length < 2 ^ (prefixWord ++ tailWord_575492).sum := by decide
  have hdescent : baseEnd_575492 < baseStart_575492 := by decide
  rcases family_descends (prefixWord ++ tailWord_575492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575495 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_575495 : Nat := 118140960795 + 575495 * 2 ^ 59
def prefixEnd_575495 : Nat := 4983230072969 + 3 ^ 40 * 575495 * 2
def baseEnd_575495 : Nat := 295505549259331106865853

theorem tailTrace_575495 : CollatzResearch.WordTrace tailWord_575495 prefixEnd_575495 295505549259331106865853 := by
  unfold tailWord_575495
  simp only [CollatzResearch.WordTrace]
  refine ⟨20990027050087376566103939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13993351366724917710735959 20990027050087376566103939)
  ·
    refine ⟨31485040575131064849155909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20990027050087376566103939 31485040575131064849155909)
    ·
      refine ⟨5903445107837074659216733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31485040575131064849155909 5903445107837074659216733)
      ·
        refine ⟨2213791915438902997206275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5903445107837074659216733 2213791915438902997206275)
        ·
          refine ⟨3320687873158354495809413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2213791915438902997206275 3320687873158354495809413)
          ·
            refine ⟨622628976217191467964265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3320687873158354495809413 622628976217191467964265)
            ·
              refine ⟨466971732162893600973199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622628976217191467964265 466971732162893600973199)
              ·
                refine ⟨700457598244340401459799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466971732162893600973199 700457598244340401459799)
                ·
                  refine ⟨1050686397366510602189699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700457598244340401459799 1050686397366510602189699)
                  ·
                    refine ⟨1576029596049765903284549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050686397366510602189699 1576029596049765903284549)
                    ·
                      refine ⟨295505549259331106865853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1576029596049765903284549 295505549259331106865853)
                      ·
                        rfl

theorem cell23_575495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_575495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575495 prefixEnd_575495 := by exact prefixLift 575495
  have htrace : WordTrace (prefixWord ++ tailWord_575495) baseStart_575495 baseEnd_575495 := by
    simpa [prefixWord, tailWord_575495, baseEnd_575495] using wordTrace_append hprefix tailTrace_575495
  have hstable : (prefixWord ++ tailWord_575495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575495).length < 2 ^ (prefixWord ++ tailWord_575495).sum := by decide
  have hdescent : baseEnd_575495 < baseStart_575495 := by decide
  rcases family_descends (prefixWord ++ tailWord_575495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575558 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_575558 : Nat := 118140960795 + 575558 * 2 ^ 59
def prefixEnd_575558 : Nat := 4983230072969 + 3 ^ 40 * 575558 * 2
def baseEnd_575558 : Nat := 295537898540564360378063

theorem tailTrace_575558 : CollatzResearch.WordTrace tailWord_575558 prefixEnd_575558 295537898540564360378063 := by
  unfold tailWord_575558
  simp only [CollatzResearch.WordTrace]
  refine ⟨656010151526848072676479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13994883232572758883764885 656010151526848072676479)
  ·
    refine ⟨984015227290272109014719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 656010151526848072676479 984015227290272109014719)
    ·
      refine ⟨1476022840935408163522079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984015227290272109014719 1476022840935408163522079)
      ·
        refine ⟨2214034261403112245283119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476022840935408163522079 2214034261403112245283119)
        ·
          refine ⟨3321051392104668367924679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214034261403112245283119 3321051392104668367924679)
          ·
            refine ⟨4981577088157002551887019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321051392104668367924679 4981577088157002551887019)
            ·
              refine ⟨7472365632235503827830529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981577088157002551887019 7472365632235503827830529)
              ·
                refine ⟨5604274224176627870872897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7472365632235503827830529 5604274224176627870872897)
                ·
                  refine ⟨4203205668132470903154673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5604274224176627870872897 4203205668132470903154673)
                  ·
                    refine ⟨3152404251099353177366005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4203205668132470903154673 3152404251099353177366005)
                    ·
                      refine ⟨295537898540564360378063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3152404251099353177366005 295537898540564360378063)
                      ·
                        rfl

theorem cell23_575558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_575558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575558 prefixEnd_575558 := by exact prefixLift 575558
  have htrace : WordTrace (prefixWord ++ tailWord_575558) baseStart_575558 baseEnd_575558 := by
    simpa [prefixWord, tailWord_575558, baseEnd_575558] using wordTrace_append hprefix tailTrace_575558
  have hstable : (prefixWord ++ tailWord_575558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575558).length < 2 ^ (prefixWord ++ tailWord_575558).sum := by decide
  have hdescent : baseEnd_575558 < baseStart_575558 := by decide
  rcases family_descends (prefixWord ++ tailWord_575558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575641 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_575641 : Nat := 118140960795 + 575641 * 2 ^ 59
def prefixEnd_575641 : Nat := 4983230072969 + 3 ^ 40 * 575641 * 2
def baseEnd_575641 : Nat := 295580517434887535640181

theorem tailTrace_575641 : CollatzResearch.WordTrace tailWord_575641 prefixEnd_575641 295580517434887535640181 := by
  unfold tailWord_575641
  simp only [CollatzResearch.WordTrace]
  refine ⟨20995352107558443500918777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13996901405038962333945851 20995352107558443500918777)
  ·
    refine ⟨15746514080668832625689083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20995352107558443500918777 15746514080668832625689083)
    ·
      refine ⟨23619771121003248938533625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15746514080668832625689083 23619771121003248938533625)
      ·
        refine ⟨17714828340752436703900219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23619771121003248938533625 17714828340752436703900219)
        ·
          refine ⟨26572242511128655055850329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17714828340752436703900219 26572242511128655055850329)
          ·
            refine ⟨19929181883346491291887747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26572242511128655055850329 19929181883346491291887747)
            ·
              refine ⟨29893772825019736937831621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19929181883346491291887747 29893772825019736937831621)
              ·
                refine ⟨5605082404691200675843429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29893772825019736937831621 5605082404691200675843429)
                ·
                  refine ⟨1050952950879600126720643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5605082404691200675843429 1050952950879600126720643)
                  ·
                    refine ⟨1576429426319400190080965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1050952950879600126720643 1576429426319400190080965)
                    ·
                      refine ⟨295580517434887535640181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1576429426319400190080965 295580517434887535640181)
                      ·
                        rfl

theorem cell23_575641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_575641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575641 prefixEnd_575641 := by exact prefixLift 575641
  have htrace : WordTrace (prefixWord ++ tailWord_575641) baseStart_575641 baseEnd_575641 := by
    simpa [prefixWord, tailWord_575641, baseEnd_575641] using wordTrace_append hprefix tailTrace_575641
  have hstable : (prefixWord ++ tailWord_575641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575641).length < 2 ^ (prefixWord ++ tailWord_575641).sum := by decide
  have hdescent : baseEnd_575641 < baseStart_575641 := by decide
  rcases family_descends (prefixWord ++ tailWord_575641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575671 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_575671 : Nat := 118140960795 + 575671 * 2 ^ 59
def prefixEnd_575671 : Nat := 4983230072969 + 3 ^ 40 * 575671 * 2
def baseEnd_575671 : Nat := 295595921854522418265043

theorem tailTrace_575671 : CollatzResearch.WordTrace tailWord_575671 prefixEnd_575671 295595921854522418265043 := by
  unfold tailWord_575671
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996446297449758624510867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13997630864966505749673911 20996446297449758624510867)
  ·
    refine ⟨31494669446174637936766301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20996446297449758624510867 31494669446174637936766301)
    ·
      refine ⟨11810501042315489226287363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31494669446174637936766301 11810501042315489226287363)
      ·
        refine ⟨17715751563473233839431045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11810501042315489226287363 17715751563473233839431045)
        ·
          refine ⟨3321703418151231344893321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17715751563473233839431045 3321703418151231344893321)
          ·
            refine ⟨2491277563613423508669991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3321703418151231344893321 2491277563613423508669991)
            ·
              refine ⟨3736916345420135263004987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491277563613423508669991 3736916345420135263004987)
              ·
                refine ⟨5605374518130202894507481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736916345420135263004987 5605374518130202894507481)
                ·
                  refine ⟨4204030888597652170880611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605374518130202894507481 4204030888597652170880611)
                  ·
                    refine ⟨6306046332896478256320917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204030888597652170880611 6306046332896478256320917)
                    ·
                      refine ⟨295595921854522418265043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6306046332896478256320917 295595921854522418265043)
                      ·
                        rfl

theorem cell23_575671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_575671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575671 prefixEnd_575671 := by exact prefixLift 575671
  have htrace : WordTrace (prefixWord ++ tailWord_575671) baseStart_575671 baseEnd_575671 := by
    simpa [prefixWord, tailWord_575671, baseEnd_575671] using wordTrace_append hprefix tailTrace_575671
  have hstable : (prefixWord ++ tailWord_575671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575671).length < 2 ^ (prefixWord ++ tailWord_575671).sum := by decide
  have hdescent : baseEnd_575671 < baseStart_575671 := by decide
  rcases family_descends (prefixWord ++ tailWord_575671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575685 : List Nat := [1, 3, 1, 1, 1, 1, 6, 4, 1, 4]
def baseStart_575685 : Nat := 118140960795 + 575685 * 2 ^ 59
def prefixEnd_575685 : Nat := 4983230072969 + 3 ^ 40 * 575685 * 2
def baseEnd_575685 : Nat := 98534370194561787829993

theorem tailTrace_575685 : CollatzResearch.WordTrace tailWord_575685 prefixEnd_575685 98534370194561787829993 := by
  unfold tailWord_575685
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996956919399039015520509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13997971279599359343680339 20996956919399039015520509)
  ·
    refine ⟨7873858844774639630820191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20996956919399039015520509 7873858844774639630820191)
    ·
      refine ⟨11810788267161959446230287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7873858844774639630820191 11810788267161959446230287)
      ·
        refine ⟨17716182400742939169345431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11810788267161959446230287 17716182400742939169345431)
        ·
          refine ⟨26574273601114408754018147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17716182400742939169345431 26574273601114408754018147)
          ·
            refine ⟨39861410401671613131027221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26574273601114408754018147 39861410401671613131027221)
            ·
              refine ⟨1868503612578356865516901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39861410401671613131027221 1868503612578356865516901)
              ·
                refine ⟨350344427358441912284419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1868503612578356865516901 350344427358441912284419)
                ·
                  refine ⟨525516641037662868426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350344427358441912284419 525516641037662868426629)
                  ·
                    refine ⟨98534370194561787829993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525516641037662868426629 98534370194561787829993)
                    ·
                      rfl

theorem cell23_575685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 1, 4].length) (baseStart_575685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575685 prefixEnd_575685 := by exact prefixLift 575685
  have htrace : WordTrace (prefixWord ++ tailWord_575685) baseStart_575685 baseEnd_575685 := by
    simpa [prefixWord, tailWord_575685, baseEnd_575685] using wordTrace_append hprefix tailTrace_575685
  have hstable : (prefixWord ++ tailWord_575685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575685).length < 2 ^ (prefixWord ++ tailWord_575685).sum := by decide
  have hdescent : baseEnd_575685 < baseStart_575685 := by decide
  rcases family_descends (prefixWord ++ tailWord_575685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575702 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_575702 : Nat := 118140960795 + 575702 * 2 ^ 59
def prefixEnd_575702 : Nat := 4983230072969 + 3 ^ 40 * 575702 * 2
def baseEnd_575702 : Nat := 98537279918270598992467

theorem tailTrace_575702 : CollatzResearch.WordTrace tailWord_575702 prefixEnd_575702 98537279918270598992467 := by
  unfold tailWord_575702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312348560021090682430585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13998384640224967279259573 1312348560021090682430585)
  ·
    refine ⟨984261420015818011822939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1312348560021090682430585 984261420015818011822939)
    ·
      refine ⟨1476392130023727017734409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984261420015818011822939 1476392130023727017734409)
      ·
        refine ⟨1107294097517795263300807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1476392130023727017734409 1107294097517795263300807)
        ·
          refine ⟨1660941146276692894951211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107294097517795263300807 1660941146276692894951211)
          ·
            refine ⟨2491411719415039342426817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660941146276692894951211 2491411719415039342426817)
            ·
              refine ⟨1868558789561279506820113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491411719415039342426817 1868558789561279506820113)
              ·
                refine ⟨1401419092170959630115085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1868558789561279506820113 1401419092170959630115085)
                ·
                  refine ⟨525532159564109861293157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1401419092170959630115085 525532159564109861293157)
                  ·
                    refine ⟨98537279918270598992467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525532159564109861293157 98537279918270598992467)
                    ·
                      rfl

theorem cell23_575702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_575702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575702 prefixEnd_575702 := by exact prefixLift 575702
  have htrace : WordTrace (prefixWord ++ tailWord_575702) baseStart_575702 baseEnd_575702 := by
    simpa [prefixWord, tailWord_575702, baseEnd_575702] using wordTrace_append hprefix tailTrace_575702
  have hstable : (prefixWord ++ tailWord_575702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575702).length < 2 ^ (prefixWord ++ tailWord_575702).sum := by decide
  have hdescent : baseEnd_575702 < baseStart_575702 := by decide
  rcases family_descends (prefixWord ++ tailWord_575702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575719 : List Nat := [1, 1, 5, 3, 1, 3, 1, 3, 1, 4]
def baseStart_575719 : Nat := 118140960795 + 575719 * 2 ^ 59
def prefixEnd_575719 : Nat := 4983230072969 + 3 ^ 40 * 575719 * 2
def baseEnd_575719 : Nat := 98540189641979410154941

theorem tailTrace_575719 : CollatzResearch.WordTrace tailWord_575719 prefixEnd_575719 98540189641979410154941 := by
  unfold tailWord_575719
  simp only [CollatzResearch.WordTrace]
  refine ⟨20998197001275862822258211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13998798000850575214838807 20998197001275862822258211)
  ·
    refine ⟨31497295501913794233387317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20998197001275862822258211 31497295501913794233387317)
    ·
      refine ⟨2952871453304418209380061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31497295501913794233387317 2952871453304418209380061)
      ·
        refine ⟨1107326794989156828517523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2952871453304418209380061 1107326794989156828517523)
        ·
          refine ⟨1660990192483735242776285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107326794989156828517523 1660990192483735242776285)
          ·
            refine ⟨622871322181400716041107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1660990192483735242776285 622871322181400716041107)
            ·
              refine ⟨934306983272101074061661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622871322181400716041107 934306983272101074061661)
              ·
                refine ⟨350365118727037902773123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934306983272101074061661 350365118727037902773123)
                ·
                  refine ⟨525547678090556854159685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350365118727037902773123 525547678090556854159685)
                  ·
                    refine ⟨98540189641979410154941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 525547678090556854159685 98540189641979410154941)
                    ·
                      rfl

theorem cell23_575719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_575719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575719 prefixEnd_575719 := by exact prefixLift 575719
  have htrace : WordTrace (prefixWord ++ tailWord_575719) baseStart_575719 baseEnd_575719 := by
    simpa [prefixWord, tailWord_575719, baseEnd_575719] using wordTrace_append hprefix tailTrace_575719
  have hstable : (prefixWord ++ tailWord_575719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575719).length < 2 ^ (prefixWord ++ tailWord_575719).sum := by decide
  have hdescent : baseEnd_575719 < baseStart_575719 := by decide
  rcases family_descends (prefixWord ++ tailWord_575719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575758 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_575758 : Nat := 118140960795 + 575758 * 2 ^ 59
def prefixEnd_575758 : Nat := 4983230072969 + 3 ^ 40 * 575758 * 2
def baseEnd_575758 : Nat := 98546864890487859292381

theorem tailTrace_575758 : CollatzResearch.WordTrace tailWord_575758 prefixEnd_575758 98546864890487859292381 := by
  unfold tailWord_575758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2624952431016821560365991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13999746298756381655285285 2624952431016821560365991)
  ·
    refine ⟨3937428646525232340548987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2624952431016821560365991 3937428646525232340548987)
    ·
      refine ⟨5906142969787848510823481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3937428646525232340548987 5906142969787848510823481)
      ·
        refine ⟨4429607227340886383117611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5906142969787848510823481 4429607227340886383117611)
        ·
          refine ⟨6644410841011329574676417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429607227340886383117611 6644410841011329574676417)
          ·
            refine ⟨4983308130758497181007313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6644410841011329574676417 4983308130758497181007313)
            ·
              refine ⟨3737481098068872885755485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4983308130758497181007313 3737481098068872885755485)
              ·
                refine ⟨1401555411775827332158307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3737481098068872885755485 1401555411775827332158307)
                ·
                  refine ⟨2102333117663740998237461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401555411775827332158307 2102333117663740998237461)
                  ·
                    refine ⟨98546864890487859292381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2102333117663740998237461 98546864890487859292381)
                    ·
                      rfl

theorem cell23_575758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_575758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575758 prefixEnd_575758 := by exact prefixLift 575758
  have htrace : WordTrace (prefixWord ++ tailWord_575758) baseStart_575758 baseEnd_575758 := by
    simpa [prefixWord, tailWord_575758, baseEnd_575758] using wordTrace_append hprefix tailTrace_575758
  have hstable : (prefixWord ++ tailWord_575758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575758).length < 2 ^ (prefixWord ++ tailWord_575758).sum := by decide
  have hdescent : baseEnd_575758 < baseStart_575758 := by decide
  rcases family_descends (prefixWord ++ tailWord_575758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575765 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 4]
def baseStart_575765 : Nat := 118140960795 + 575765 * 2 ^ 59
def prefixEnd_575765 : Nat := 4983230072969 + 3 ^ 40 * 575765 * 2
def baseEnd_575765 : Nat := 295644189036045050489611

theorem tailTrace_575765 : CollatzResearch.WordTrace tailWord_575765 prefixEnd_575765 295644189036045050489611 := by
  unfold tailWord_575765
  simp only [CollatzResearch.WordTrace]
  refine ⟨20999874759109212678432749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13999916506072808452288499 20999874759109212678432749)
  ·
    refine ⟨7874953034665954754412281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20999874759109212678432749 7874953034665954754412281)
    ·
      refine ⟨5906214775999466065809211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7874953034665954754412281 5906214775999466065809211)
      ·
        refine ⟨8859322163999199098713817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906214775999466065809211 8859322163999199098713817)
        ·
          refine ⟨6644491622999399324035363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8859322163999199098713817 6644491622999399324035363)
          ·
            refine ⟨9966737434499098986053045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644491622999399324035363 9966737434499098986053045)
            ·
              refine ⟨934381634484290529942473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9966737434499098986053045 934381634484290529942473)
              ·
                refine ⟨700786225863217897456855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934381634484290529942473 700786225863217897456855)
                ·
                  refine ⟨1051179338794826846185283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 700786225863217897456855 1051179338794826846185283)
                  ·
                    refine ⟨1576769008192240269277925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1051179338794826846185283 1576769008192240269277925)
                    ·
                      refine ⟨295644189036045050489611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1576769008192240269277925 295644189036045050489611)
                      ·
                        rfl

theorem cell23_575765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_575765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575765 prefixEnd_575765 := by exact prefixLift 575765
  have htrace : WordTrace (prefixWord ++ tailWord_575765) baseStart_575765 baseEnd_575765 := by
    simpa [prefixWord, tailWord_575765, baseEnd_575765] using wordTrace_append hprefix tailTrace_575765
  have hstable : (prefixWord ++ tailWord_575765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575765).length < 2 ^ (prefixWord ++ tailWord_575765).sum := by decide
  have hdescent : baseEnd_575765 < baseStart_575765 := by decide
  rcases family_descends (prefixWord ++ tailWord_575765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575771 : List Nat := [1, 1, 1, 1, 1, 1, 8, 9]
def baseStart_575771 : Nat := 118140960795 + 575771 * 2 ^ 59
def prefixEnd_575771 : Nat := 4983230072969 + 3 ^ 40 * 575771 * 2
def baseEnd_575771 : Nat := 10949898885924889889429

theorem tailTrace_575771 : CollatzResearch.WordTrace tailWord_575771 prefixEnd_575771 10949898885924889889429 := by
  unfold tailWord_575771
  simp only [CollatzResearch.WordTrace]
  refine ⟨21000093597087475703151167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14000062398058317135434111 21000093597087475703151167)
  ·
    refine ⟨31500140395631213554726751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21000093597087475703151167 31500140395631213554726751)
    ·
      refine ⟨47250210593446820332090127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31500140395631213554726751 47250210593446820332090127)
      ·
        refine ⟨70875315890170230498135191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47250210593446820332090127 70875315890170230498135191)
        ·
          refine ⟨106312973835255345747202787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70875315890170230498135191 106312973835255345747202787)
          ·
            refine ⟨159469460752883018620804181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106312973835255345747202787 159469460752883018620804181)
            ·
              refine ⟨1868782743197847874462549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 159469460752883018620804181 1868782743197847874462549)
              ·
                refine ⟨10949898885924889889429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1868782743197847874462549 10949898885924889889429)
                ·
                  rfl

theorem cell23_575771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 9].length) (baseStart_575771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575771 prefixEnd_575771 := by exact prefixLift 575771
  have htrace : WordTrace (prefixWord ++ tailWord_575771) baseStart_575771 baseEnd_575771 := by
    simpa [prefixWord, tailWord_575771, baseEnd_575771] using wordTrace_append hprefix tailTrace_575771
  have hstable : (prefixWord ++ tailWord_575771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575771).length < 2 ^ (prefixWord ++ tailWord_575771).sum := by decide
  have hdescent : baseEnd_575771 < baseStart_575771 := by decide
  rcases family_descends (prefixWord ++ tailWord_575771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575793 : List Nat := [1, 2, 2, 3, 5, 1, 2, 2, 1, 1, 3]
def baseStart_575793 : Nat := 118140960795 + 575793 * 2 ^ 59
def prefixEnd_575793 : Nat := 4983230072969 + 3 ^ 40 * 575793 * 2
def baseEnd_575793 : Nat := 295658566494370940939483

theorem tailTrace_575793 : CollatzResearch.WordTrace tailWord_575793 prefixEnd_575793 295658566494370940939483 := by
  unfold tailWord_575793
  simp only [CollatzResearch.WordTrace]
  refine ⟨21000896003007773460452033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14000597335338515640301355 21000896003007773460452033)
  ·
    refine ⟨15750672002255830095339025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21000896003007773460452033 15750672002255830095339025)
    ·
      refine ⟨11813004001691872571504269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15750672002255830095339025 11813004001691872571504269)
      ·
        refine ⟨4429876500634452214314101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11813004001691872571504269 4429876500634452214314101)
        ·
          refine ⟨415300921934479895091947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4429876500634452214314101 415300921934479895091947)
          ·
            refine ⟨622951382901719842637921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415300921934479895091947 622951382901719842637921)
            ·
              refine ⟨467213537176289881978441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622951382901719842637921 467213537176289881978441)
              ·
                refine ⟨350410152882217411483831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467213537176289881978441 350410152882217411483831)
                ·
                  refine ⟨525615229323326117225747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350410152882217411483831 525615229323326117225747)
                  ·
                    refine ⟨788422843984989175838621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 525615229323326117225747 788422843984989175838621)
                    ·
                      refine ⟨295658566494370940939483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 788422843984989175838621 295658566494370940939483)
                      ·
                        rfl

theorem cell23_575793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_575793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575793 prefixEnd_575793 := by exact prefixLift 575793
  have htrace : WordTrace (prefixWord ++ tailWord_575793) baseStart_575793 baseEnd_575793 := by
    simpa [prefixWord, tailWord_575793, baseEnd_575793] using wordTrace_append hprefix tailTrace_575793
  have hstable : (prefixWord ++ tailWord_575793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575793).length < 2 ^ (prefixWord ++ tailWord_575793).sum := by decide
  have hdescent : baseEnd_575793 < baseStart_575793 := by decide
  rcases family_descends (prefixWord ++ tailWord_575793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575815 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_575815 : Nat := 118140960795 + 575815 * 2 ^ 59
def prefixEnd_575815 : Nat := 4983230072969 + 3 ^ 40 * 575815 * 2
def baseEnd_575815 : Nat := 295669863068769854864381

theorem tailTrace_575815 : CollatzResearch.WordTrace tailWord_575815 prefixEnd_575815 295669863068769854864381 := by
  unfold tailWord_575815
  simp only [CollatzResearch.WordTrace]
  refine ⟨21001698408928071217752899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14001132272618714145168599 21001698408928071217752899)
  ·
    refine ⟨31502547613392106826629349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21001698408928071217752899 31502547613392106826629349)
    ·
      refine ⟨5906727677511020029993003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31502547613392106826629349 5906727677511020029993003)
      ·
        refine ⟨8860091516266530044989505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906727677511020029993003 8860091516266530044989505)
        ·
          refine ⟨6645068637199897533742129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8860091516266530044989505 6645068637199897533742129)
          ·
            refine ⟨4983801477899923150306597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645068637199897533742129 4983801477899923150306597)
            ·
              refine ⟨934462777106235590682487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4983801477899923150306597 934462777106235590682487)
              ·
                refine ⟨1401694165659353386023731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934462777106235590682487 1401694165659353386023731)
                ·
                  refine ⟨2102541248489030079035597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1401694165659353386023731 2102541248489030079035597)
                  ·
                    refine ⟨788452968183386279638349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2102541248489030079035597 788452968183386279638349)
                    ·
                      refine ⟨295669863068769854864381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 788452968183386279638349 295669863068769854864381)
                      ·
                        rfl

theorem cell23_575815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_575815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575815 prefixEnd_575815 := by exact prefixLift 575815
  have htrace : WordTrace (prefixWord ++ tailWord_575815) baseStart_575815 baseEnd_575815 := by
    simpa [prefixWord, tailWord_575815, baseEnd_575815] using wordTrace_append hprefix tailTrace_575815
  have hstable : (prefixWord ++ tailWord_575815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575815).length < 2 ^ (prefixWord ++ tailWord_575815).sum := by decide
  have hdescent : baseEnd_575815 < baseStart_575815 := by decide
  rcases family_descends (prefixWord ++ tailWord_575815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575868 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_575868 : Nat := 118140960795 + 575868 * 2 ^ 59
def prefixEnd_575868 : Nat := 4983230072969 + 3 ^ 40 * 575868 * 2
def baseEnd_575868 : Nat := 295697077543458147501637

theorem tailTrace_575868 : CollatzResearch.WordTrace tailWord_575868 prefixEnd_575868 295697077543458147501637 := by
  unfold tailWord_575868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10501815738868030634716129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14002420985157374179621505 10501815738868030634716129)
  ·
    refine ⟨7876361804151022976037097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10501815738868030634716129 7876361804151022976037097)
    ·
      refine ⟨5907271353113267232027823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7876361804151022976037097 5907271353113267232027823)
      ·
        refine ⟨8860907029669900848041735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5907271353113267232027823 8860907029669900848041735)
        ·
          refine ⟨13291360544504851272062603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8860907029669900848041735 13291360544504851272062603)
          ·
            refine ⟨19937040816757276908093905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13291360544504851272062603 19937040816757276908093905)
            ·
              refine ⟨14952780612567957681070429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19937040816757276908093905 14952780612567957681070429)
              ·
                refine ⟨5607292729712984130401411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14952780612567957681070429 5607292729712984130401411)
                ·
                  refine ⟨8410939094569476195602117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607292729712984130401411 8410939094569476195602117)
                  ·
                    refine ⟨1577051080231776786675397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8410939094569476195602117 1577051080231776786675397)
                    ·
                      refine ⟨295697077543458147501637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1577051080231776786675397 295697077543458147501637)
                      ·
                        rfl

theorem cell23_575868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_575868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575868 prefixEnd_575868 := by exact prefixLift 575868
  have htrace : WordTrace (prefixWord ++ tailWord_575868) baseStart_575868 baseEnd_575868 := by
    simpa [prefixWord, tailWord_575868, baseEnd_575868] using wordTrace_append hprefix tailTrace_575868
  have hstable : (prefixWord ++ tailWord_575868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575868).length < 2 ^ (prefixWord ++ tailWord_575868).sum := by decide
  have hdescent : baseEnd_575868 < baseStart_575868 := by decide
  rcases family_descends (prefixWord ++ tailWord_575868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575892 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_575892 : Nat := 118140960795 + 575892 * 2 ^ 59
def prefixEnd_575892 : Nat := 4983230072969 + 3 ^ 40 * 575892 * 2
def baseEnd_575892 : Nat := 295709401079166053601527

theorem tailTrace_575892 : CollatzResearch.WordTrace tailWord_575892 prefixEnd_575892 295709401079166053601527 := by
  unfold tailWord_575892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10502253414824556684152965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14003004553099408912203953 10502253414824556684152965)
  ·
    refine ⟨1969172515279604378278681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10502253414824556684152965 1969172515279604378278681)
    ·
      refine ⟨1476879386459703283709011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1969172515279604378278681 1476879386459703283709011)
      ·
        refine ⟨2215319079689554925563517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476879386459703283709011 2215319079689554925563517)
        ·
          refine ⟨830744654883583097086319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2215319079689554925563517 830744654883583097086319)
          ·
            refine ⟨1246116982325374645629479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830744654883583097086319 1246116982325374645629479)
            ·
              refine ⟨1869175473488061968444219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246116982325374645629479 1869175473488061968444219)
              ·
                refine ⟨2803763210232092952666329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1869175473488061968444219 2803763210232092952666329)
                ·
                  refine ⟨2102822407674069714499747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2803763210232092952666329 2102822407674069714499747)
                  ·
                    refine ⟨3154233611511104571749621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2102822407674069714499747 3154233611511104571749621)
                    ·
                      refine ⟨295709401079166053601527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3154233611511104571749621 295709401079166053601527)
                      ·
                        rfl

theorem cell23_575892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_575892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575892 prefixEnd_575892 := by exact prefixLift 575892
  have htrace : WordTrace (prefixWord ++ tailWord_575892) baseStart_575892 baseEnd_575892 := by
    simpa [prefixWord, tailWord_575892, baseEnd_575892] using wordTrace_append hprefix tailTrace_575892
  have hstable : (prefixWord ++ tailWord_575892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575892).length < 2 ^ (prefixWord ++ tailWord_575892).sum := by decide
  have hdescent : baseEnd_575892 < baseStart_575892 := by decide
  rcases family_descends (prefixWord ++ tailWord_575892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575912 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 7]
def baseStart_575912 : Nat := 118140960795 + 575912 * 2 ^ 59
def prefixEnd_575912 : Nat := 4983230072969 + 3 ^ 40 * 575912 * 2
def baseEnd_575912 : Nat := 32857741188028441705715

theorem tailTrace_575912 : CollatzResearch.WordTrace tailWord_575912 prefixEnd_575912 32857741188028441705715 := by
  unfold tailWord_575912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10502618144788328392016995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14003490859717771189355993 10502618144788328392016995)
  ·
    refine ⟨15753927217182492588025493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10502618144788328392016995 15753927217182492588025493)
    ·
      refine ⟨738465338305429340063695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15753927217182492588025493 738465338305429340063695)
      ·
        refine ⟨1107698007458144010095543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738465338305429340063695 1107698007458144010095543)
        ·
          refine ⟨1661547011187216015143315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107698007458144010095543 1661547011187216015143315)
          ·
            refine ⟨2492320516780824022714973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1661547011187216015143315 2492320516780824022714973)
            ·
              refine ⟨934620193792809008518115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2492320516780824022714973 934620193792809008518115)
              ·
                refine ⟨1401930290689213512777173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934620193792809008518115 1401930290689213512777173)
                ·
                  refine ⟨32857741188028441705715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1401930290689213512777173 32857741188028441705715)
                  ·
                    rfl

theorem cell23_575912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_575912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575912 prefixEnd_575912 := by exact prefixLift 575912
  have htrace : WordTrace (prefixWord ++ tailWord_575912) baseStart_575912 baseEnd_575912 := by
    simpa [prefixWord, tailWord_575912, baseEnd_575912] using wordTrace_append hprefix tailTrace_575912
  have hstable : (prefixWord ++ tailWord_575912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575912).length < 2 ^ (prefixWord ++ tailWord_575912).sum := by decide
  have hdescent : baseEnd_575912 < baseStart_575912 := by decide
  rcases family_descends (prefixWord ++ tailWord_575912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575945 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_575945 : Nat := 118140960795 + 575945 * 2 ^ 59
def prefixEnd_575945 : Nat := 4983230072969 + 3 ^ 40 * 575945 * 2
def baseEnd_575945 : Nat := 295736615553854346238783

theorem tailTrace_575945 : CollatzResearch.WordTrace tailWord_575945 prefixEnd_575945 295736615553854346238783 := by
  unfold tailWord_575945
  simp only [CollatzResearch.WordTrace]
  refine ⟨21006439898457103419985289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14004293265638068946656859 21006439898457103419985289)
  ·
    refine ⟨15754829923842827564988967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21006439898457103419985289 15754829923842827564988967)
    ·
      refine ⟨23632244885764241347483451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15754829923842827564988967 23632244885764241347483451)
      ·
        refine ⟨35448367328646362021225177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23632244885764241347483451 35448367328646362021225177)
        ·
          refine ⟨26586275496484771515918883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35448367328646362021225177 26586275496484771515918883)
          ·
            refine ⟨39879413244727157273878325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26586275496484771515918883 39879413244727157273878325)
            ·
              refine ⟨3738694991693170994426093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39879413244727157273878325 3738694991693170994426093)
              ·
                refine ⟨1402010621884939122909785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3738694991693170994426093 1402010621884939122909785)
                ·
                  refine ⟨1051507966413704342182339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402010621884939122909785 1051507966413704342182339)
                  ·
                    refine ⟨1577261949620556513273509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1051507966413704342182339 1577261949620556513273509)
                    ·
                      refine ⟨295736615553854346238783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1577261949620556513273509 295736615553854346238783)
                      ·
                        rfl

theorem cell23_575945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_575945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575945 prefixEnd_575945 := by exact prefixLift 575945
  have htrace : WordTrace (prefixWord ++ tailWord_575945) baseStart_575945 baseEnd_575945 := by
    simpa [prefixWord, tailWord_575945, baseEnd_575945] using wordTrace_append hprefix tailTrace_575945
  have hstable : (prefixWord ++ tailWord_575945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575945).length < 2 ^ (prefixWord ++ tailWord_575945).sum := by decide
  have hdescent : baseEnd_575945 < baseStart_575945 := by decide
  rcases family_descends (prefixWord ++ tailWord_575945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575962 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_575962 : Nat := 118140960795 + 575962 * 2 ^ 59
def prefixEnd_575962 : Nat := 4983230072969 + 3 ^ 40 * 575962 * 2
def baseEnd_575962 : Nat := 295745344724980779726205

theorem tailTrace_575962 : CollatzResearch.WordTrace tailWord_575962 prefixEnd_575962 295745344724980779726205 := by
  unfold tailWord_575962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5251764984848878830838535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14004706626263676882236093 5251764984848878830838535)
  ·
    refine ⟨7877647477273318246257803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5251764984848878830838535 7877647477273318246257803)
    ·
      refine ⟨11816471215909977369386705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7877647477273318246257803 11816471215909977369386705)
      ·
        refine ⟨8862353411932483027040029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11816471215909977369386705 8862353411932483027040029)
        ·
          refine ⟨3323382529474681135140011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8862353411932483027040029 3323382529474681135140011)
          ·
            refine ⟨4985073794212021702710017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323382529474681135140011 4985073794212021702710017)
            ·
              refine ⟨3738805345659016277032513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4985073794212021702710017 3738805345659016277032513)
              ·
                refine ⟨2804104009244262207774385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3738805345659016277032513 2804104009244262207774385)
                ·
                  refine ⟨2103078006933196655830789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2804104009244262207774385 2103078006933196655830789)
                  ·
                    refine ⟨394327126299974372968273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103078006933196655830789 394327126299974372968273)
                    ·
                      refine ⟨295745344724980779726205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394327126299974372968273 295745344724980779726205)
                      ·
                        rfl

theorem cell23_575962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_575962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575962 prefixEnd_575962 := by exact prefixLift 575962
  have htrace : WordTrace (prefixWord ++ tailWord_575962) baseStart_575962 baseEnd_575962 := by
    simpa [prefixWord, tailWord_575962, baseEnd_575962] using wordTrace_append hprefix tailTrace_575962
  have hstable : (prefixWord ++ tailWord_575962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575962).length < 2 ^ (prefixWord ++ tailWord_575962).sum := by decide
  have hdescent : baseEnd_575962 < baseStart_575962 := by decide
  rcases family_descends (prefixWord ++ tailWord_575962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575965 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_575965 : Nat := 118140960795 + 575965 * 2 ^ 59
def prefixEnd_575965 : Nat := 4983230072969 + 3 ^ 40 * 575965 * 2
def baseEnd_575965 : Nat := 295746885166944267988691

theorem tailTrace_575965 : CollatzResearch.WordTrace tailWord_575965 prefixEnd_575965 295746885166944267988691 := by
  unfold tailWord_575965
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007169358384646835713349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14004779572256431223808899 21007169358384646835713349)
  ·
    refine ⟨3938844254697121281696253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21007169358384646835713349 3938844254697121281696253)
    ·
      refine ⟨1477066595511420480636095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3938844254697121281696253 1477066595511420480636095)
      ·
        refine ⟨2215599893267130720954143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477066595511420480636095 2215599893267130720954143)
        ·
          refine ⟨3323399839900696081431215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215599893267130720954143 3323399839900696081431215)
          ·
            refine ⟨4985099759851044122146823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323399839900696081431215 4985099759851044122146823)
            ·
              refine ⟨7477649639776566183220235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985099759851044122146823 7477649639776566183220235)
              ·
                refine ⟨11216474459664849274830353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7477649639776566183220235 11216474459664849274830353)
                ·
                  refine ⟨8412355844748636956122765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11216474459664849274830353 8412355844748636956122765)
                  ·
                    refine ⟨3154633441780738858546037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8412355844748636956122765 3154633441780738858546037)
                    ·
                      refine ⟨295746885166944267988691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3154633441780738858546037 295746885166944267988691)
                      ·
                        rfl

theorem cell23_575965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_575965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575965 prefixEnd_575965 := by exact prefixLift 575965
  have htrace : WordTrace (prefixWord ++ tailWord_575965) baseStart_575965 baseEnd_575965 := by
    simpa [prefixWord, tailWord_575965, baseEnd_575965] using wordTrace_append hprefix tailTrace_575965
  have hstable : (prefixWord ++ tailWord_575965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575965).length < 2 ^ (prefixWord ++ tailWord_575965).sum := by decide
  have hdescent : baseEnd_575965 < baseStart_575965 := by decide
  rcases family_descends (prefixWord ++ tailWord_575965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575985 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 6]
def baseStart_575985 : Nat := 118140960795 + 575985 * 2 ^ 59
def prefixEnd_575985 : Nat := 4983230072969 + 3 ^ 40 * 575985 * 2
def baseEnd_575985 : Nat := 32861906086670465526511

theorem tailTrace_575985 : CollatzResearch.WordTrace tailWord_575985 prefixEnd_575985 32861906086670465526511 := by
  unfold tailWord_575985
  simp only [CollatzResearch.WordTrace]
  refine ⟨21007898818312190251441409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14005265878874793500960939 21007898818312190251441409)
  ·
    refine ⟨15755924113734142688581057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21007898818312190251441409 15755924113734142688581057)
    ·
      refine ⟨11816943085300607016435793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15755924113734142688581057 11816943085300607016435793)
      ·
        refine ⟨8862707313975455262326845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11816943085300607016435793 8862707313975455262326845)
        ·
          refine ⟨3323515242740795723372567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8862707313975455262326845 3323515242740795723372567)
          ·
            refine ⟨4985272864111193585058851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323515242740795723372567 4985272864111193585058851)
            ·
              refine ⟨7477909296166790377588277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985272864111193585058851 7477909296166790377588277)
              ·
                refine ⟨701053996515636597898901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7477909296166790377588277 701053996515636597898901)
                ·
                  refine ⟨32861906086670465526511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 701053996515636597898901 32861906086670465526511)
                  ·
                    rfl

theorem cell23_575985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 6].length) (baseStart_575985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_575985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_575985 prefixEnd_575985 := by exact prefixLift 575985
  have htrace : WordTrace (prefixWord ++ tailWord_575985) baseStart_575985 baseEnd_575985 := by
    simpa [prefixWord, tailWord_575985, baseEnd_575985] using wordTrace_append hprefix tailTrace_575985
  have hstable : (prefixWord ++ tailWord_575985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575985).length < 2 ^ (prefixWord ++ tailWord_575985).sum := by decide
  have hdescent : baseEnd_575985 < baseStart_575985 := by decide
  rcases family_descends (prefixWord ++ tailWord_575985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576029 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_576029 : Nat := 118140960795 + 576029 * 2 ^ 59
def prefixEnd_576029 : Nat := 4983230072969 + 3 ^ 40 * 576029 * 2
def baseEnd_576029 : Nat := 295779747928832017588397

theorem tailTrace_576029 : CollatzResearch.WordTrace tailWord_576029 prefixEnd_576029 295779747928832017588397 := by
  unfold tailWord_576029
  simp only [CollatzResearch.WordTrace]
  refine ⟨21009503630152785766043141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14006335753435190510695427 21009503630152785766043141)
  ·
    refine ⟨3939281930653647331133089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21009503630152785766043141 3939281930653647331133089)
    ·
      refine ⟨2954461447990235498349817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3939281930653647331133089 2954461447990235498349817)
      ·
        refine ⟨2215846085992676623762363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2954461447990235498349817 2215846085992676623762363)
        ·
          refine ⟨3323769128989014935643545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215846085992676623762363 3323769128989014935643545)
          ·
            refine ⟨2492826846741761201732659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3323769128989014935643545 2492826846741761201732659)
            ·
              refine ⟨3739240270112641802598989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2492826846741761201732659 3739240270112641802598989)
              ·
                refine ⟨1402215101292240675974621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3739240270112641802598989 1402215101292240675974621)
                ·
                  refine ⟨525830662984590253490483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1402215101292240675974621 525830662984590253490483)
                  ·
                    refine ⟨788745994476885380235725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 525830662984590253490483 788745994476885380235725)
                    ·
                      refine ⟨295779747928832017588397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 788745994476885380235725 295779747928832017588397)
                      ·
                        rfl

theorem cell23_576029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_576029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576029 prefixEnd_576029 := by exact prefixLift 576029
  have htrace : WordTrace (prefixWord ++ tailWord_576029) baseStart_576029 baseEnd_576029 := by
    simpa [prefixWord, tailWord_576029, baseEnd_576029] using wordTrace_append hprefix tailTrace_576029
  have hstable : (prefixWord ++ tailWord_576029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576029).length < 2 ^ (prefixWord ++ tailWord_576029).sum := by decide
  have hdescent : baseEnd_576029 < baseStart_576029 := by decide
  rcases family_descends (prefixWord ++ tailWord_576029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576036 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 6]
def baseStart_576036 : Nat := 118140960795 + 576036 * 2 ^ 59
def prefixEnd_576036 : Nat := 4983230072969 + 3 ^ 40 * 576036 * 2
def baseEnd_576036 : Nat := 32864815810379276688985

theorem tailTrace_576036 : CollatzResearch.WordTrace tailWord_576036 prefixEnd_576036 32864815810379276688985 := by
  unfold tailWord_576036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504879470563712980773981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14006505960751617307698641 10504879470563712980773981)
  ·
    refine ⟨3939329801461392367790243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10504879470563712980773981 3939329801461392367790243)
    ·
      refine ⟨5908994702192088551685365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939329801461392367790243 5908994702192088551685365)
      ·
        refine ⟨553968253330508301720503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5908994702192088551685365 553968253330508301720503)
        ·
          refine ⟨830952379995762452580755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553968253330508301720503 830952379995762452580755)
          ·
            refine ⟨1246428569993643678871133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830952379995762452580755 1246428569993643678871133)
            ·
              refine ⟨467410713747616379576675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1246428569993643678871133 467410713747616379576675)
              ·
                refine ⟨701116070621424569365013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467410713747616379576675 701116070621424569365013)
                ·
                  refine ⟨32864815810379276688985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 701116070621424569365013 32864815810379276688985)
                  ·
                    rfl

theorem cell23_576036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_576036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576036 prefixEnd_576036 := by exact prefixLift 576036
  have htrace : WordTrace (prefixWord ++ tailWord_576036) baseStart_576036 baseEnd_576036 := by
    simpa [prefixWord, tailWord_576036, baseEnd_576036] using wordTrace_append hprefix tailTrace_576036
  have hstable : (prefixWord ++ tailWord_576036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576036).length < 2 ^ (prefixWord ++ tailWord_576036).sum := by decide
  have hdescent : baseEnd_576036 < baseStart_576036 := by decide
  rcases family_descends (prefixWord ++ tailWord_576036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576055 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_576055 : Nat := 118140960795 + 576055 * 2 ^ 59
def prefixEnd_576055 : Nat := 4983230072969 + 3 ^ 40 * 576055 * 2
def baseEnd_576055 : Nat := 295793098425848915863277

theorem tailTrace_576055 : CollatzResearch.WordTrace tailWord_576055 prefixEnd_576055 295793098425848915863277 := by
  unfold tailWord_576055
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010451928058592206489619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14006967952039061470993079 21010451928058592206489619)
  ·
    refine ⟨31515677892087888309734429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21010451928058592206489619 31515677892087888309734429)
    ·
      refine ⟨11818379209532958116150411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31515677892087888309734429 11818379209532958116150411)
      ·
        refine ⟨17727568814299437174225617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11818379209532958116150411 17727568814299437174225617)
        ·
          refine ⟨13295676610724577880669213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17727568814299437174225617 13295676610724577880669213)
          ·
            refine ⟨4985878729021716705250955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13295676610724577880669213 4985878729021716705250955)
            ·
              refine ⟨7478818093532575057876433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985878729021716705250955 7478818093532575057876433)
              ·
                refine ⟨5609113570149431293407325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7478818093532575057876433 5609113570149431293407325)
                ·
                  refine ⟨2103417588806036735027747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5609113570149431293407325 2103417588806036735027747)
                  ·
                    refine ⟨3155126383209055102541621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2103417588806036735027747 3155126383209055102541621)
                    ·
                      refine ⟨295793098425848915863277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3155126383209055102541621 295793098425848915863277)
                      ·
                        rfl

theorem cell23_576055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_576055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576055 prefixEnd_576055 := by exact prefixLift 576055
  have htrace : WordTrace (prefixWord ++ tailWord_576055) baseStart_576055 baseEnd_576055 := by
    simpa [prefixWord, tailWord_576055, baseEnd_576055] using wordTrace_append hprefix tailTrace_576055
  have hstable : (prefixWord ++ tailWord_576055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576055).length < 2 ^ (prefixWord ++ tailWord_576055).sum := by decide
  have hdescent : baseEnd_576055 < baseStart_576055 := by decide
  rcases family_descends (prefixWord ++ tailWord_576055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576115 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5]
def baseStart_576115 : Nat := 118140960795 + 576115 * 2 ^ 59
def prefixEnd_576115 : Nat := 4983230072969 + 3 ^ 40 * 576115 * 2
def baseEnd_576115 : Nat := 295823907265118681113001

theorem tailTrace_576115 : CollatzResearch.WordTrace tailWord_576115 prefixEnd_576115 295823907265118681113001 := by
  unfold tailWord_576115
  simp only [CollatzResearch.WordTrace]
  refine ⟨21012640307841222453673799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14008426871894148302449199 21012640307841222453673799)
  ·
    refine ⟨31518960461761833680510699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21012640307841222453673799 31518960461761833680510699)
    ·
      refine ⟨47278440692642750520766049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31518960461761833680510699 47278440692642750520766049)
      ·
        refine ⟨35458830519482062890574537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47278440692642750520766049 35458830519482062890574537)
        ·
          refine ⟨26594122889611547167930903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35458830519482062890574537 26594122889611547167930903)
          ·
            refine ⟨39891184334417320751896355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26594122889611547167930903 39891184334417320751896355)
            ·
              refine ⟨59836776501625981127844533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39891184334417320751896355 59836776501625981127844533)
              ·
                refine ⟨5609697797027435730735425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59836776501625981127844533 5609697797027435730735425)
                ·
                  refine ⟨4207273347770576798051569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5609697797027435730735425 4207273347770576798051569)
                  ·
                    refine ⟨3155455010827932598538677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4207273347770576798051569 3155455010827932598538677)
                    ·
                      refine ⟨295823907265118681113001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3155455010827932598538677 295823907265118681113001)
                      ·
                        rfl

theorem cell23_576115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_576115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576115 prefixEnd_576115 := by exact prefixLift 576115
  have htrace : WordTrace (prefixWord ++ tailWord_576115) baseStart_576115 baseEnd_576115 := by
    simpa [prefixWord, tailWord_576115, baseEnd_576115] using wordTrace_append hprefix tailTrace_576115
  have hstable : (prefixWord ++ tailWord_576115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576115).length < 2 ^ (prefixWord ++ tailWord_576115).sum := by decide
  have hdescent : baseEnd_576115 < baseStart_576115 := by decide
  rcases family_descends (prefixWord ++ tailWord_576115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576142 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_576142 : Nat := 118140960795 + 576142 * 2 ^ 59
def prefixEnd_576142 : Nat := 4983230072969 + 3 ^ 40 * 576142 * 2
def baseEnd_576142 : Nat := 295837771242790075475377

theorem tailTrace_576142 : CollatzResearch.WordTrace tailWord_576142 prefixEnd_576142 295837771242790075475377 := by
  unfold tailWord_576142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2626703134842925758113335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14009083385828937376604453 2626703134842925758113335)
  ·
    refine ⟨3940054702264388637170003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2626703134842925758113335 3940054702264388637170003)
    ·
      refine ⟨5910082053396582955755005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940054702264388637170003 5910082053396582955755005)
      ·
        refine ⟨2216280770023718608408127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5910082053396582955755005 2216280770023718608408127)
        ·
          refine ⟨3324421155035577912612191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216280770023718608408127 3324421155035577912612191)
          ·
            refine ⟨4986631732553366868918287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324421155035577912612191 4986631732553366868918287)
            ·
              refine ⟨7479947598830050303377431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4986631732553366868918287 7479947598830050303377431)
              ·
                refine ⟨11219921398245075455066147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7479947598830050303377431 11219921398245075455066147)
                ·
                  refine ⟨16829882097367613182599221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11219921398245075455066147 16829882097367613182599221)
                  ·
                    refine ⟨1577801446628213735868677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16829882097367613182599221 1577801446628213735868677)
                    ·
                      refine ⟨295837771242790075475377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1577801446628213735868677 295837771242790075475377)
                      ·
                        rfl

theorem cell23_576142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_576142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576142 prefixEnd_576142 := by exact prefixLift 576142
  have htrace : WordTrace (prefixWord ++ tailWord_576142) baseStart_576142 baseEnd_576142 := by
    simpa [prefixWord, tailWord_576142, baseEnd_576142] using wordTrace_append hprefix tailTrace_576142
  have hstable : (prefixWord ++ tailWord_576142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576142).length < 2 ^ (prefixWord ++ tailWord_576142).sum := by decide
  have hdescent : baseEnd_576142 < baseStart_576142 := by decide
  rcases family_descends (prefixWord ++ tailWord_576142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576146 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_576146 : Nat := 118140960795 + 576146 * 2 ^ 59
def prefixEnd_576146 : Nat := 4983230072969 + 3 ^ 40 * 576146 * 2
def baseEnd_576146 : Nat := 295839825165408059825359

theorem tailTrace_576146 : CollatzResearch.WordTrace tailWord_576146 prefixEnd_576146 295839825165408059825359 := by
  unfold tailWord_576146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253442742682228687013073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14009180647152609832034861 5253442742682228687013073)
  ·
    refine ⟨3940082057011671515259805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5253442742682228687013073 3940082057011671515259805)
    ·
      refine ⟨1477530771379376818222427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3940082057011671515259805 1477530771379376818222427)
      ·
        refine ⟨2216296157069065227333641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1477530771379376818222427 2216296157069065227333641)
        ·
          refine ⟨1662222117801798920500231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2216296157069065227333641 1662222117801798920500231)
          ·
            refine ⟨2493333176702698380750347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662222117801798920500231 2493333176702698380750347)
            ·
              refine ⟨3739999765054047571125521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2493333176702698380750347 3739999765054047571125521)
              ·
                refine ⟨2804999823790535678344141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3739999765054047571125521 2804999823790535678344141)
                ·
                  refine ⟨1051874933921450879379053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2804999823790535678344141 1051874933921450879379053)
                  ·
                    refine ⟨394453100220544079767145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1051874933921450879379053 394453100220544079767145)
                    ·
                      refine ⟨295839825165408059825359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394453100220544079767145 295839825165408059825359)
                      ·
                        rfl

theorem cell23_576146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_576146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576146 prefixEnd_576146 := by exact prefixLift 576146
  have htrace : WordTrace (prefixWord ++ tailWord_576146) baseStart_576146 baseEnd_576146 := by
    simpa [prefixWord, tailWord_576146, baseEnd_576146] using wordTrace_append hprefix tailTrace_576146
  have hstable : (prefixWord ++ tailWord_576146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576146).length < 2 ^ (prefixWord ++ tailWord_576146).sum := by decide
  have hdescent : baseEnd_576146 < baseStart_576146 := by decide
  rcases family_descends (prefixWord ++ tailWord_576146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576152 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_576152 : Nat := 118140960795 + 576152 * 2 ^ 59
def prefixEnd_576152 : Nat := 4983230072969 + 3 ^ 40 * 576152 * 2
def baseEnd_576152 : Nat := 98614302016445012116777

theorem tailTrace_576152 : CollatzResearch.WordTrace tailWord_576152 prefixEnd_576152 98614302016445012116777 := by
  unfold tailWord_576152
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506994904353588886385355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14009326539138118515180473 10506994904353588886385355)
  ·
    refine ⟨15760492356530383329578033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10506994904353588886385355 15760492356530383329578033)
    ·
      refine ⟨11820369267397787497183525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15760492356530383329578033 11820369267397787497183525)
      ·
        refine ⟨2216319237637085155721911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11820369267397787497183525 2216319237637085155721911)
        ·
          refine ⟨3324478856455627733582867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2216319237637085155721911 3324478856455627733582867)
          ·
            refine ⟨4986718284683441600374301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3324478856455627733582867 4986718284683441600374301)
            ·
              refine ⟨1870019356756290600140363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4986718284683441600374301 1870019356756290600140363)
              ·
                refine ⟨2805029035134435900210545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1870019356756290600140363 2805029035134435900210545)
                ·
                  refine ⟨2103771776350826925157909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2805029035134435900210545 2103771776350826925157909)
                  ·
                    refine ⟨98614302016445012116777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2103771776350826925157909 98614302016445012116777)
                    ·
                      rfl

theorem cell23_576152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_576152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576152 prefixEnd_576152 := by exact prefixLift 576152
  have htrace : WordTrace (prefixWord ++ tailWord_576152) baseStart_576152 baseEnd_576152 := by
    simpa [prefixWord, tailWord_576152, baseEnd_576152] using wordTrace_append hprefix tailTrace_576152
  have hstable : (prefixWord ++ tailWord_576152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576152).length < 2 ^ (prefixWord ++ tailWord_576152).sum := by decide
  have hdescent : baseEnd_576152 < baseStart_576152 := by decide
  rcases family_descends (prefixWord ++ tailWord_576152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576210 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_576210 : Nat := 118140960795 + 576210 * 2 ^ 59
def prefixEnd_576210 : Nat := 4983230072969 + 3 ^ 40 * 576210 * 2
def baseEnd_576210 : Nat := 295872687927295809425065

theorem tailTrace_576210 : CollatzResearch.WordTrace tailWord_576210 prefixEnd_576210 295872687927295809425065 := by
  unfold tailWord_576210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5254026310624263419595521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14010736828331369118921389 5254026310624263419595521)
  ·
    refine ⟨3940519732968197564696641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5254026310624263419595521 3940519732968197564696641)
    ·
      refine ⟨2955389799726148173522481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3940519732968197564696641 2955389799726148173522481)
      ·
        refine ⟨2216542349794611130141861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955389799726148173522481 2216542349794611130141861)
        ·
          refine ⟨415601690586489586901599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2216542349794611130141861 415601690586489586901599)
          ·
            refine ⟨623402535879734380352399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415601690586489586901599 623402535879734380352399)
            ·
              refine ⟨935103803819601570528599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623402535879734380352399 935103803819601570528599)
              ·
                refine ⟨1402655705729402355792899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935103803819601570528599 1402655705729402355792899)
                ·
                  refine ⟨2103983558594103533689349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1402655705729402355792899 2103983558594103533689349)
                  ·
                    refine ⟨394496917236394412566753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2103983558594103533689349 394496917236394412566753)
                    ·
                      refine ⟨295872687927295809425065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394496917236394412566753 295872687927295809425065)
                      ·
                        rfl

theorem cell23_576210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_576210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576210 prefixEnd_576210 := by exact prefixLift 576210
  have htrace : WordTrace (prefixWord ++ tailWord_576210) baseStart_576210 baseEnd_576210 := by
    simpa [prefixWord, tailWord_576210, baseEnd_576210] using wordTrace_append hprefix tailTrace_576210
  have hstable : (prefixWord ++ tailWord_576210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576210).length < 2 ^ (prefixWord ++ tailWord_576210).sum := by decide
  have hdescent : baseEnd_576210 < baseStart_576210 := by decide
  rcases family_descends (prefixWord ++ tailWord_576210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576249 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 4, 4, 2]
def baseStart_576249 : Nat := 118140960795 + 576249 * 2 ^ 59
def prefixEnd_576249 : Nat := 4983230072969 + 3 ^ 40 * 576249 * 2
def baseEnd_576249 : Nat := 295892713672821156837385

theorem tailTrace_576249 : CollatzResearch.WordTrace tailWord_576249 prefixEnd_576249 295892713672821156837385 := by
  unfold tailWord_576249
  simp only [CollatzResearch.WordTrace]
  refine ⟨21017527689355763339051801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14011685126237175559367867 21017527689355763339051801)
  ·
    refine ⟨15763145767016822504288851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21017527689355763339051801 15763145767016822504288851)
    ·
      refine ⟨23644718650525233756433277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15763145767016822504288851 23644718650525233756433277)
      ·
        refine ⟨8866769493946962658662479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23644718650525233756433277 8866769493946962658662479)
        ·
          refine ⟨13300154240920443987993719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866769493946962658662479 13300154240920443987993719)
          ·
            refine ⟨19950231361380665981990579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300154240920443987993719 19950231361380665981990579)
            ·
              refine ⟨29925347042070998972985869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19950231361380665981990579 29925347042070998972985869)
              ·
                refine ⟨11222005140776624614869701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29925347042070998972985869 11222005140776624614869701)
                ·
                  refine ⟨2104125963895617115288069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11222005140776624614869701 2104125963895617115288069)
                  ·
                    refine ⟨394523618230428209116513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104125963895617115288069 394523618230428209116513)
                    ·
                      refine ⟨295892713672821156837385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394523618230428209116513 295892713672821156837385)
                      ·
                        rfl

theorem cell23_576249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_576249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576249 prefixEnd_576249 := by exact prefixLift 576249
  have htrace : WordTrace (prefixWord ++ tailWord_576249) baseStart_576249 baseEnd_576249 := by
    simpa [prefixWord, tailWord_576249, baseEnd_576249] using wordTrace_append hprefix tailTrace_576249
  have hstable : (prefixWord ++ tailWord_576249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576249).length < 2 ^ (prefixWord ++ tailWord_576249).sum := by decide
  have hdescent : baseEnd_576249 < baseStart_576249 := by decide
  rcases family_descends (prefixWord ++ tailWord_576249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576316 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_576316 : Nat := 118140960795 + 576316 * 2 ^ 59
def prefixEnd_576316 : Nat := 4983230072969 + 3 ^ 40 * 576316 * 2
def baseEnd_576316 : Nat := 295927116876672394699577

theorem tailTrace_576316 : CollatzResearch.WordTrace tailWord_576316 prefixEnd_576316 295927116876672394699577 := by
  unfold tailWord_576316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509985690056516890870401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14013314253408689187827201 10509985690056516890870401)
  ·
    refine ⟨7882489267542387668152801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10509985690056516890870401 7882489267542387668152801)
    ·
      refine ⟨5911866950656790751114601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7882489267542387668152801 5911866950656790751114601)
      ·
        refine ⟨4433900212992593063335951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5911866950656790751114601 4433900212992593063335951)
        ·
          refine ⟨6650850319488889595003927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433900212992593063335951 6650850319488889595003927)
          ·
            refine ⟨9976275479233334392505891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6650850319488889595003927 9976275479233334392505891)
            ·
              refine ⟨14964413218850001588758837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9976275479233334392505891 14964413218850001588758837)
              ·
                refine ⟨1402913739267187648946141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14964413218850001588758837 1402913739267187648946141)
                ·
                  refine ⟨526092652225195368354803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1402913739267187648946141 526092652225195368354803)
                  ·
                    refine ⟨789138978337793052532205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526092652225195368354803 789138978337793052532205)
                    ·
                      refine ⟨295927116876672394699577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789138978337793052532205 295927116876672394699577)
                      ·
                        rfl

theorem cell23_576316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_576316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576316 prefixEnd_576316 := by exact prefixLift 576316
  have htrace : WordTrace (prefixWord ++ tailWord_576316) baseStart_576316 baseEnd_576316 := by
    simpa [prefixWord, tailWord_576316, baseEnd_576316] using wordTrace_append hprefix tailTrace_576316
  have hstable : (prefixWord ++ tailWord_576316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576316).length < 2 ^ (prefixWord ++ tailWord_576316).sum := by decide
  have hdescent : baseEnd_576316 < baseStart_576316 := by decide
  rcases family_descends (prefixWord ++ tailWord_576316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576319 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 3, 5]
def baseStart_576319 : Nat := 118140960795 + 576319 * 2 ^ 59
def prefixEnd_576319 : Nat := 4983230072969 + 3 ^ 40 * 576319 * 2
def baseEnd_576319 : Nat := 98642885772878627654021

theorem tailTrace_576319 : CollatzResearch.WordTrace tailWord_576319 prefixEnd_576319 98642885772878627654021 := by
  unfold tailWord_576319
  simp only [CollatzResearch.WordTrace]
  refine ⟨21020080799102165294100011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14013387199401443529400007 21020080799102165294100011)
  ·
    refine ⟨31530121198653247941150017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21020080799102165294100011 31530121198653247941150017)
    ·
      refine ⟨23647590898989935955862513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31530121198653247941150017 23647590898989935955862513)
      ·
        refine ⟨17735693174242451966896885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23647590898989935955862513 17735693174242451966896885)
        ·
          refine ⟨1662721235085229871896583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17735693174242451966896885 1662721235085229871896583)
          ·
            refine ⟨2494081852627844807844875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662721235085229871896583 2494081852627844807844875)
            ·
              refine ⟨3741122778941767211767313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494081852627844807844875 3741122778941767211767313)
              ·
                refine ⟨2805842084206325408825485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741122778941767211767313 2805842084206325408825485)
                ·
                  refine ⟨1052190781577372028309557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2805842084206325408825485 1052190781577372028309557)
                  ·
                    refine ⟨98642885772878627654021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1052190781577372028309557 98642885772878627654021)
                    ·
                      rfl

theorem cell23_576319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_576319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576319 prefixEnd_576319 := by exact prefixLift 576319
  have htrace : WordTrace (prefixWord ++ tailWord_576319) baseStart_576319 baseEnd_576319 := by
    simpa [prefixWord, tailWord_576319, baseEnd_576319] using wordTrace_append hprefix tailTrace_576319
  have hstable : (prefixWord ++ tailWord_576319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576319).length < 2 ^ (prefixWord ++ tailWord_576319).sum := by decide
  have hdescent : baseEnd_576319 < baseStart_576319 := by decide
  rcases family_descends (prefixWord ++ tailWord_576319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576343 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_576343 : Nat := 118140960795 + 576343 * 2 ^ 59
def prefixEnd_576343 : Nat := 4983230072969 + 3 ^ 40 * 576343 * 2
def baseEnd_576343 : Nat := 295940980854343789061953

theorem tailTrace_576343 : CollatzResearch.WordTrace tailWord_576343 prefixEnd_576343 295940980854343789061953 := by
  unfold tailWord_576343
  simp only [CollatzResearch.WordTrace]
  refine ⟨21020956151015217392973683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14013970767343478261982455 21020956151015217392973683)
  ·
    refine ⟨31531434226522826089460525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21020956151015217392973683 31531434226522826089460525)
    ·
      refine ⟨11824287834946059783547697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31531434226522826089460525 11824287834946059783547697)
      ·
        refine ⟨8868215876209544837660773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11824287834946059783547697 8868215876209544837660773)
        ·
          refine ⟨1662790476789289657061395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8868215876209544837660773 1662790476789289657061395)
          ·
            refine ⟨2494185715183934485592093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662790476789289657061395 2494185715183934485592093)
            ·
              refine ⟨935319643193975432097035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2494185715183934485592093 935319643193975432097035)
              ·
                refine ⟨1402979464790963148145553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935319643193975432097035 1402979464790963148145553)
                ·
                  refine ⟨1052234598593222361109165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1402979464790963148145553 1052234598593222361109165)
                  ·
                    refine ⟨394587974472458385415937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052234598593222361109165 394587974472458385415937)
                    ·
                      refine ⟨295940980854343789061953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394587974472458385415937 295940980854343789061953)
                      ·
                        rfl

theorem cell23_576343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_576343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576343 prefixEnd_576343 := by exact prefixLift 576343
  have htrace : WordTrace (prefixWord ++ tailWord_576343) baseStart_576343 baseEnd_576343 := by
    simpa [prefixWord, tailWord_576343, baseEnd_576343] using wordTrace_append hprefix tailTrace_576343
  have hstable : (prefixWord ++ tailWord_576343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576343).length < 2 ^ (prefixWord ++ tailWord_576343).sum := by decide
  have hdescent : baseEnd_576343 < baseStart_576343 := by decide
  rcases family_descends (prefixWord ++ tailWord_576343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576393 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_576393 : Nat := 118140960795 + 576393 * 2 ^ 59
def prefixEnd_576393 : Nat := 4983230072969 + 3 ^ 40 * 576393 * 2
def baseEnd_576393 : Nat := 295966654887068593436723

theorem tailTrace_576393 : CollatzResearch.WordTrace tailWord_576393 prefixEnd_576393 295966654887068593436723 := by
  unfold tailWord_576393
  simp only [CollatzResearch.WordTrace]
  refine ⟨21022779800834075932293833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015186533889383954862555 21022779800834075932293833)
  ·
    refine ⟨15767084850625556949220375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21022779800834075932293833 15767084850625556949220375)
    ·
      refine ⟨23650627275938335423830563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15767084850625556949220375 23650627275938335423830563)
      ·
        refine ⟨35475940913907503135745845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23650627275938335423830563 35475940913907503135745845)
        ·
          refine ⟨3325869460678828418976173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35475940913907503135745845 3325869460678828418976173)
          ·
            refine ⟨1247201047754560657116065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3325869460678828418976173 1247201047754560657116065)
            ·
              refine ⟨935400785815920492837049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247201047754560657116065 935400785815920492837049)
              ·
                refine ⟨701550589361940369627787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935400785815920492837049 701550589361940369627787)
                ·
                  refine ⟨1052325884042910554441681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701550589361940369627787 1052325884042910554441681)
                  ·
                    refine ⟨789244413032182915831261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052325884042910554441681 789244413032182915831261)
                    ·
                      refine ⟨295966654887068593436723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789244413032182915831261 295966654887068593436723)
                      ·
                        rfl

theorem cell23_576393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_576393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576393 prefixEnd_576393 := by exact prefixLift 576393
  have htrace : WordTrace (prefixWord ++ tailWord_576393) baseStart_576393 baseEnd_576393 := by
    simpa [prefixWord, tailWord_576393, baseEnd_576393] using wordTrace_append hprefix tailTrace_576393
  have hstable : (prefixWord ++ tailWord_576393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576393).length < 2 ^ (prefixWord ++ tailWord_576393).sum := by decide
  have hdescent : baseEnd_576393 < baseStart_576393 := by decide
  rcases family_descends (prefixWord ++ tailWord_576393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576439 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 2, 6]
def baseStart_576439 : Nat := 118140960795 + 576439 * 2 ^ 59
def prefixEnd_576439 : Nat := 4983230072969 + 3 ^ 40 * 576439 * 2
def baseEnd_576439 : Nat := 98663424999058471153837

theorem tailTrace_576439 : CollatzResearch.WordTrace tailWord_576439 prefixEnd_576439 98663424999058471153837 := by
  unfold tailWord_576439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21024457558667425788468371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14016305039111617192312247 21024457558667425788468371)
  ·
    refine ⟨31536686338001138682702557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21024457558667425788468371 31536686338001138682702557)
    ·
      refine ⟨11826257376750427006013459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31536686338001138682702557 11826257376750427006013459)
      ·
        refine ⟨17739386065125640509020189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11826257376750427006013459 17739386065125640509020189)
        ·
          refine ⟨6652269774422115190882571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17739386065125640509020189 6652269774422115190882571)
          ·
            refine ⟨9978404661633172786323857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6652269774422115190882571 9978404661633172786323857)
            ·
              refine ⟨7483803496224879589742893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9978404661633172786323857 7483803496224879589742893)
              ·
                refine ⟨2806426311084329846153585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7483803496224879589742893 2806426311084329846153585)
                ·
                  refine ⟨2104819733313247384615189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2806426311084329846153585 2104819733313247384615189)
                  ·
                    refine ⟨98663424999058471153837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2104819733313247384615189 98663424999058471153837)
                    ·
                      rfl

theorem cell23_576439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_576439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576439 prefixEnd_576439 := by exact prefixLift 576439
  have htrace : WordTrace (prefixWord ++ tailWord_576439) baseStart_576439 baseEnd_576439 := by
    simpa [prefixWord, tailWord_576439, baseEnd_576439] using wordTrace_append hprefix tailTrace_576439
  have hstable : (prefixWord ++ tailWord_576439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576439).length < 2 ^ (prefixWord ++ tailWord_576439).sum := by decide
  have hdescent : baseEnd_576439 < baseStart_576439 := by decide
  rcases family_descends (prefixWord ++ tailWord_576439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576440 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_576440 : Nat := 118140960795 + 576440 * 2 ^ 59
def prefixEnd_576440 : Nat := 4983230072969 + 3 ^ 40 * 576440 * 2
def baseEnd_576440 : Nat := 295990788477829909549007

theorem tailTrace_576440 : CollatzResearch.WordTrace tailWord_576440 prefixEnd_576440 295990788477829909549007 := by
  unfold tailWord_576440
  simp only [CollatzResearch.WordTrace]
  refine ⟨10512247015831901479627387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14016329354442535306169849 10512247015831901479627387)
  ·
    refine ⟨15768370523747852219441081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10512247015831901479627387 15768370523747852219441081)
    ·
      refine ⟨11826277892810889164580811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15768370523747852219441081 11826277892810889164580811)
      ·
        refine ⟨17739416839216333746871217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11826277892810889164580811 17739416839216333746871217)
        ·
          refine ⟨13304562629412250310153413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17739416839216333746871217 13304562629412250310153413)
          ·
            refine ⟨2494605493014796933153765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13304562629412250310153413 2494605493014796933153765)
            ·
              refine ⟨467738529940274424966331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2494605493014796933153765 467738529940274424966331)
              ·
                refine ⟨701607794910411637449497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467738529940274424966331 701607794910411637449497)
                ·
                  refine ⟨526205846182808728087123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 701607794910411637449497 526205846182808728087123)
                  ·
                    refine ⟨789308769274213092130685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526205846182808728087123 789308769274213092130685)
                    ·
                      refine ⟨295990788477829909549007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789308769274213092130685 295990788477829909549007)
                      ·
                        rfl

theorem cell23_576440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_576440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576440 prefixEnd_576440 := by exact prefixLift 576440
  have htrace : WordTrace (prefixWord ++ tailWord_576440) baseStart_576440 baseEnd_576440 := by
    simpa [prefixWord, tailWord_576440, baseEnd_576440] using wordTrace_append hprefix tailTrace_576440
  have hstable : (prefixWord ++ tailWord_576440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576440).length < 2 ^ (prefixWord ++ tailWord_576440).sum := by decide
  have hdescent : baseEnd_576440 < baseStart_576440 := by decide
  rcases family_descends (prefixWord ++ tailWord_576440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576454 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_576454 : Nat := 118140960795 + 576454 * 2 ^ 59
def prefixEnd_576454 : Nat := 4983230072969 + 3 ^ 40 * 576454 * 2
def baseEnd_576454 : Nat := 295997977206992854773943

theorem tailTrace_576454 : CollatzResearch.WordTrace tailWord_576454 prefixEnd_576454 295997977206992854773943 := by
  unfold tailWord_576454
  simp only [CollatzResearch.WordTrace]
  refine ⟨657031395425408854695763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14016669769075388900176277 657031395425408854695763)
  ·
    refine ⟨985547093138113282043645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657031395425408854695763 985547093138113282043645)
    ·
      refine ⟨369580159926792480766367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 985547093138113282043645 369580159926792480766367)
      ·
        refine ⟨554370239890188721149551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369580159926792480766367 554370239890188721149551)
        ·
          refine ⟨831555359835283081724327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554370239890188721149551 831555359835283081724327)
          ·
            refine ⟨1247333039752924622586491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831555359835283081724327 1247333039752924622586491)
            ·
              refine ⟨1870999559629386933879737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247333039752924622586491 1870999559629386933879737)
              ·
                refine ⟨1403249669722040200409803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1870999559629386933879737 1403249669722040200409803)
                ·
                  refine ⟨2104874504583060300614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403249669722040200409803 2104874504583060300614705)
                  ·
                    refine ⟨1578655878437295225461029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2104874504583060300614705 1578655878437295225461029)
                    ·
                      refine ⟨295997977206992854773943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1578655878437295225461029 295997977206992854773943)
                      ·
                        rfl

theorem cell23_576454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_576454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576454 prefixEnd_576454 := by exact prefixLift 576454
  have htrace : WordTrace (prefixWord ++ tailWord_576454) baseStart_576454 baseEnd_576454 := by
    simpa [prefixWord, tailWord_576454, baseEnd_576454] using wordTrace_append hprefix tailTrace_576454
  have hstable : (prefixWord ++ tailWord_576454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576454).length < 2 ^ (prefixWord ++ tailWord_576454).sum := by decide
  have hdescent : baseEnd_576454 < baseStart_576454 := by decide
  rcases family_descends (prefixWord ++ tailWord_576454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576461 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_576461 : Nat := 118140960795 + 576461 * 2 ^ 59
def prefixEnd_576461 : Nat := 4983230072969 + 3 ^ 40 * 576461 * 2
def baseEnd_576461 : Nat := 296001571571574327386411

theorem tailTrace_576461 : CollatzResearch.WordTrace tailWord_576461 prefixEnd_576461 296001571571574327386411 := by
  unfold tailWord_576461
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025259964587723545769237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14016839976391815697179491 21025259964587723545769237)
  ·
    refine ⟨985559060840049541207933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21025259964587723545769237 985559060840049541207933)
    ·
      refine ⟨369584647815018577952975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 985559060840049541207933 369584647815018577952975)
      ·
        refine ⟨554376971722527866929463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369584647815018577952975 554376971722527866929463)
        ·
          refine ⟨831565457583791800394195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554376971722527866929463 831565457583791800394195)
          ·
            refine ⟨1247348186375687700591293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831565457583791800394195 1247348186375687700591293)
            ·
              refine ⟨467755569890882887721735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1247348186375687700591293 467755569890882887721735)
              ·
                refine ⟨701633354836324331582603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467755569890882887721735 701633354836324331582603)
                ·
                  refine ⟨1052450032254486497373905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701633354836324331582603 1052450032254486497373905)
                  ·
                    refine ⟨789337524190864873030429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052450032254486497373905 789337524190864873030429)
                    ·
                      refine ⟨296001571571574327386411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789337524190864873030429 296001571571574327386411)
                      ·
                        rfl

theorem cell23_576461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_576461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576461 prefixEnd_576461 := by exact prefixLift 576461
  have htrace : WordTrace (prefixWord ++ tailWord_576461) baseStart_576461 baseEnd_576461 := by
    simpa [prefixWord, tailWord_576461, baseEnd_576461] using wordTrace_append hprefix tailTrace_576461
  have hstable : (prefixWord ++ tailWord_576461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576461).length < 2 ^ (prefixWord ++ tailWord_576461).sum := by decide
  have hdescent : baseEnd_576461 < baseStart_576461 := by decide
  rcases family_descends (prefixWord ++ tailWord_576461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576463 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 1, 4, 2]
def baseStart_576463 : Nat := 118140960795 + 576463 * 2 ^ 59
def prefixEnd_576463 : Nat := 4983230072969 + 3 ^ 40 * 576463 * 2
def baseEnd_576463 : Nat := 296002598532883319561401

theorem tailTrace_576463 : CollatzResearch.WordTrace tailWord_576463 prefixEnd_576463 296002598532883319561401 := by
  unfold tailWord_576463
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025332910580477887342043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14016888607053651924894695 21025332910580477887342043)
  ·
    refine ⟨31537999365870716831013065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21025332910580477887342043 31537999365870716831013065)
    ·
      refine ⟨23653499524403037623259799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31537999365870716831013065 23653499524403037623259799)
      ·
        refine ⟨35480249286604556434889699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23653499524403037623259799 35480249286604556434889699)
        ·
          refine ⟨53220373929906834652334549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35480249286604556434889699 53220373929906834652334549)
          ·
            refine ⟨1247352513982191437164091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53220373929906834652334549 1247352513982191437164091)
            ·
              refine ⟨1871028770973287155746137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247352513982191437164091 1871028770973287155746137)
              ·
                refine ⟨1403271578229965366809603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871028770973287155746137 1403271578229965366809603)
                ·
                  refine ⟨2104907367344948050214405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403271578229965366809603 2104907367344948050214405)
                  ·
                    refine ⟨394670131377177759415201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2104907367344948050214405 394670131377177759415201)
                    ·
                      refine ⟨296002598532883319561401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394670131377177759415201 296002598532883319561401)
                      ·
                        rfl

theorem cell23_576463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4, 2].length) (baseStart_576463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576463 prefixEnd_576463 := by exact prefixLift 576463
  have htrace : WordTrace (prefixWord ++ tailWord_576463) baseStart_576463 baseEnd_576463 := by
    simpa [prefixWord, tailWord_576463, baseEnd_576463] using wordTrace_append hprefix tailTrace_576463
  have hstable : (prefixWord ++ tailWord_576463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576463).length < 2 ^ (prefixWord ++ tailWord_576463).sum := by decide
  have hdescent : baseEnd_576463 < baseStart_576463 := by decide
  rcases family_descends (prefixWord ++ tailWord_576463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576529 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_576529 : Nat := 118140960795 + 576529 * 2 ^ 59
def prefixEnd_576529 : Nat := 4983230072969 + 3 ^ 40 * 576529 * 2
def baseEnd_576529 : Nat := 98678829418693353778699

theorem tailTrace_576529 : CollatzResearch.WordTrace tailWord_576529 prefixEnd_576529 98678829418693353778699 := by
  unfold tailWord_576529
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027740128341371159244641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14018493418894247439496427 21027740128341371159244641)
  ·
    refine ⟨15770805096256028369433481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21027740128341371159244641 15770805096256028369433481)
    ·
      refine ⟨11828103822192021277075111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15770805096256028369433481 11828103822192021277075111)
      ·
        refine ⟨17742155733288031915612667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11828103822192021277075111 17742155733288031915612667)
        ·
          refine ⟨26613233599932047873419001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17742155733288031915612667 26613233599932047873419001)
          ·
            refine ⟨19959925199949035905064251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26613233599932047873419001 19959925199949035905064251)
            ·
              refine ⟨29939887799923553857596377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19959925199949035905064251 29939887799923553857596377)
              ·
                refine ⟨22454915849942665393197283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29939887799923553857596377 22454915849942665393197283)
                ·
                  refine ⟨33682373774913998089795925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22454915849942665393197283 33682373774913998089795925)
                  ·
                    refine ⟨98678829418693353778699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 33682373774913998089795925 98678829418693353778699)
                    ·
                      rfl

theorem cell23_576529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_576529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576529 prefixEnd_576529 := by exact prefixLift 576529
  have htrace : WordTrace (prefixWord ++ tailWord_576529) baseStart_576529 baseEnd_576529 := by
    simpa [prefixWord, tailWord_576529, baseEnd_576529] using wordTrace_append hprefix tailTrace_576529
  have hstable : (prefixWord ++ tailWord_576529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576529).length < 2 ^ (prefixWord ++ tailWord_576529).sum := by decide
  have hdescent : baseEnd_576529 < baseStart_576529 := by decide
  rcases family_descends (prefixWord ++ tailWord_576529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576556 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_576556 : Nat := 118140960795 + 576556 * 2 ^ 59
def prefixEnd_576556 : Nat := 4983230072969 + 3 ^ 40 * 576556 * 2
def baseEnd_576556 : Nat := 296050352233751455698473

theorem tailTrace_576556 : CollatzResearch.WordTrace tailWord_576556 prefixEnd_576556 296050352233751455698473 := by
  unfold tailWord_576556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10514362449621777385238761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14019149932829036513651681 10514362449621777385238761)
  ·
    refine ⟨7885771837216333038929071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10514362449621777385238761 7885771837216333038929071)
    ·
      refine ⟨11828657755824499558393607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7885771837216333038929071 11828657755824499558393607)
      ·
        refine ⟨17742986633736749337590411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11828657755824499558393607 17742986633736749337590411)
        ·
          refine ⟨26614479950605124006385617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17742986633736749337590411 26614479950605124006385617)
          ·
            refine ⟨19960859962953843004789213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26614479950605124006385617 19960859962953843004789213)
            ·
              refine ⟨7485322486107691126795955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19960859962953843004789213 7485322486107691126795955)
              ·
                refine ⟨11227983729161536690193933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7485322486107691126795955 11227983729161536690193933)
                ·
                  refine ⟨4210493898435576258822725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11227983729161536690193933 4210493898435576258822725)
                  ·
                    refine ⟨789467605956670548529261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4210493898435576258822725 789467605956670548529261)
                    ·
                      refine ⟨296050352233751455698473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789467605956670548529261 296050352233751455698473)
                      ·
                        rfl

theorem cell23_576556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_576556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576556 prefixEnd_576556 := by exact prefixLift 576556
  have htrace : WordTrace (prefixWord ++ tailWord_576556) baseStart_576556 baseEnd_576556 := by
    simpa [prefixWord, tailWord_576556, baseEnd_576556] using wordTrace_append hprefix tailTrace_576556
  have hstable : (prefixWord ++ tailWord_576556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576556).length < 2 ^ (prefixWord ++ tailWord_576556).sum := by decide
  have hdescent : baseEnd_576556 < baseStart_576556 := by decide
  rcases family_descends (prefixWord ++ tailWord_576556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576573 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_576573 : Nat := 118140960795 + 576573 * 2 ^ 59
def prefixEnd_576573 : Nat := 4983230072969 + 3 ^ 40 * 576573 * 2
def baseEnd_576573 : Nat := 296059081404877889185895

theorem tailTrace_576573 : CollatzResearch.WordTrace tailWord_576573 prefixEnd_576573 296059081404877889185895 := by
  unfold tailWord_576573
  simp only [CollatzResearch.WordTrace]
  refine ⟨21029344940181966673846373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14019563293454644449230915 21029344940181966673846373)
  ·
    refine ⟨3943002176284118751346195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21029344940181966673846373 3943002176284118751346195)
    ·
      refine ⟨5914503264426178127019293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943002176284118751346195 5914503264426178127019293)
      ·
        refine ⟨2217938724159816797632235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5914503264426178127019293 2217938724159816797632235)
        ·
          refine ⟨3326908086239725196448353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217938724159816797632235 3326908086239725196448353)
          ·
            refine ⟨2495181064679793897336265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326908086239725196448353 2495181064679793897336265)
            ·
              refine ⟨1871385798509845423002199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2495181064679793897336265 1871385798509845423002199)
              ·
                refine ⟨2807078697764768134503299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1871385798509845423002199 2807078697764768134503299)
                ·
                  refine ⟨4210618046647152201754949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807078697764768134503299 4210618046647152201754949)
                  ·
                    refine ⟨789490883746341037829053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4210618046647152201754949 789490883746341037829053)
                    ·
                      refine ⟨296059081404877889185895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789490883746341037829053 296059081404877889185895)
                      ·
                        rfl

theorem cell23_576573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_576573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576573 prefixEnd_576573 := by exact prefixLift 576573
  have htrace : WordTrace (prefixWord ++ tailWord_576573) baseStart_576573 baseEnd_576573 := by
    simpa [prefixWord, tailWord_576573, baseEnd_576573] using wordTrace_append hprefix tailTrace_576573
  have hstable : (prefixWord ++ tailWord_576573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576573).length < 2 ^ (prefixWord ++ tailWord_576573).sum := by decide
  have hdescent : baseEnd_576573 < baseStart_576573 := by decide
  rcases family_descends (prefixWord ++ tailWord_576573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576596 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_576596 : Nat := 118140960795 + 576596 * 2 ^ 59
def prefixEnd_576596 : Nat := 4983230072969 + 3 ^ 40 * 576596 * 2
def baseEnd_576596 : Nat := 296070891459931299198289

theorem tailTrace_576596 : CollatzResearch.WordTrace tailWord_576596 prefixEnd_576596 296070891459931299198289 := by
  unfold tailWord_576596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10515091909549320800966821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14020122546065761067955761 10515091909549320800966821)
  ·
    refine ⟨1971579733040497650181279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10515091909549320800966821 1971579733040497650181279)
    ·
      refine ⟨2957369599560746475271919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971579733040497650181279 2957369599560746475271919)
      ·
        refine ⟨4436054399341119712907879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957369599560746475271919 4436054399341119712907879)
        ·
          refine ⟨6654081599011679569361819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436054399341119712907879 6654081599011679569361819)
          ·
            refine ⟨9981122398517519354042729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6654081599011679569361819 9981122398517519354042729)
            ·
              refine ⟨7485841798888139515532047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9981122398517519354042729 7485841798888139515532047)
              ·
                refine ⟨11228762698332209273298071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7485841798888139515532047 11228762698332209273298071)
                ·
                  refine ⟨16843144047498313909947107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11228762698332209273298071 16843144047498313909947107)
                  ·
                    refine ⟨25264716071247470864920661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16843144047498313909947107 25264716071247470864920661)
                    ·
                      refine ⟨296070891459931299198289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 25264716071247470864920661 296070891459931299198289)
                      ·
                        rfl

theorem cell23_576596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_576596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576596 prefixEnd_576596 := by exact prefixLift 576596
  have htrace : WordTrace (prefixWord ++ tailWord_576596) baseStart_576596 baseEnd_576596 := by
    simpa [prefixWord, tailWord_576596, baseEnd_576596] using wordTrace_append hprefix tailTrace_576596
  have hstable : (prefixWord ++ tailWord_576596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576596).length < 2 ^ (prefixWord ++ tailWord_576596).sum := by decide
  have hdescent : baseEnd_576596 < baseStart_576596 := by decide
  rcases family_descends (prefixWord ++ tailWord_576596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576597 : List Nat := [1, 3, 2, 2, 1, 2, 5, 2, 1, 4]
def baseStart_576597 : Nat := 118140960795 + 576597 * 2 ^ 59
def prefixEnd_576597 : Nat := 4983230072969 + 3 ^ 40 * 576597 * 2
def baseEnd_576597 : Nat := 98690468313528598428595

theorem tailTrace_576597 : CollatzResearch.WordTrace tailWord_576597 prefixEnd_576597 98690468313528598428595 := by
  unfold tailWord_576597
  simp only [CollatzResearch.WordTrace]
  refine ⟨21030220292095018772720045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14020146861396679181813363 21030220292095018772720045)
  ·
    refine ⟨7886332609535632039770017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21030220292095018772720045 7886332609535632039770017)
    ·
      refine ⟨5914749457151724029827513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7886332609535632039770017 5914749457151724029827513)
      ·
        refine ⟨4436062092863793022370635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5914749457151724029827513 4436062092863793022370635)
        ·
          refine ⟨6654093139295689533555953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436062092863793022370635 6654093139295689533555953)
          ·
            refine ⟨4990569854471767150166965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6654093139295689533555953 4990569854471767150166965)
            ·
              refine ⟨467865923856728170328153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4990569854471767150166965 467865923856728170328153)
              ·
                refine ⟨350899442892546127746115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467865923856728170328153 350899442892546127746115)
                ·
                  refine ⟨526349164338819191619173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350899442892546127746115 526349164338819191619173)
                  ·
                    refine ⟨98690468313528598428595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526349164338819191619173 98690468313528598428595)
                    ·
                      rfl

theorem cell23_576597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_576597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576597 prefixEnd_576597 := by exact prefixLift 576597
  have htrace : WordTrace (prefixWord ++ tailWord_576597) baseStart_576597 baseEnd_576597 := by
    simpa [prefixWord, tailWord_576597, baseEnd_576597] using wordTrace_append hprefix tailTrace_576597
  have hstable : (prefixWord ++ tailWord_576597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576597).length < 2 ^ (prefixWord ++ tailWord_576597).sum := by decide
  have hdescent : baseEnd_576597 < baseStart_576597 := by decide
  rcases family_descends (prefixWord ++ tailWord_576597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576610 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 6]
def baseStart_576610 : Nat := 118140960795 + 576610 * 2 ^ 59
def prefixEnd_576610 : Nat := 4983230072969 + 3 ^ 40 * 576610 * 2
def baseEnd_576610 : Nat := 32897564465454916047025

theorem tailTrace_576610 : CollatzResearch.WordTrace tailWord_576610 prefixEnd_576610 32897564465454916047025 := by
  unfold tailWord_576610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257673610261980498235821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14020462960698614661962189 5257673610261980498235821)
  ·
    refine ⟨1971627603848242686838433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5257673610261980498235821 1971627603848242686838433)
    ·
      refine ⟨1478720702886182015128825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1971627603848242686838433 1478720702886182015128825)
      ·
        refine ⟨1109040527164636511346619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1478720702886182015128825 1109040527164636511346619)
        ·
          refine ⟨1663560790746954767019929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109040527164636511346619 1663560790746954767019929)
          ·
            refine ⟨1247670593060216075264947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663560790746954767019929 1247670593060216075264947)
            ·
              refine ⟨1871505889590324112897421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247670593060216075264947 1871505889590324112897421)
              ·
                refine ⟨701814708596371542336533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1871505889590324112897421 701814708596371542336533)
                ·
                  refine ⟨32897564465454916047025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 701814708596371542336533 32897564465454916047025)
                  ·
                    rfl

theorem cell23_576610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_576610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576610 prefixEnd_576610 := by exact prefixLift 576610
  have htrace : WordTrace (prefixWord ++ tailWord_576610) baseStart_576610 baseEnd_576610 := by
    simpa [prefixWord, tailWord_576610, baseEnd_576610] using wordTrace_append hprefix tailTrace_576610
  have hstable : (prefixWord ++ tailWord_576610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576610).length < 2 ^ (prefixWord ++ tailWord_576610).sum := by decide
  have hdescent : baseEnd_576610 < baseStart_576610 := by decide
  rcases family_descends (prefixWord ++ tailWord_576610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576637 : List Nat := [1, 4, 1, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_576637 : Nat := 118140960795 + 576637 * 2 ^ 59
def prefixEnd_576637 : Nat := 4983230072969 + 3 ^ 40 * 576637 * 2
def baseEnd_576637 : Nat := 296091944166765638785601

theorem tailTrace_576637 : CollatzResearch.WordTrace tailWord_576637 prefixEnd_576637 296091944166765638785601 := by
  unfold tailWord_576637
  simp only [CollatzResearch.WordTrace]
  refine ⟨21031679211950105604176165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14021119474633403736117443 21031679211950105604176165)
  ·
    refine ⟨3943439852240644800783031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21031679211950105604176165 3943439852240644800783031)
    ·
      refine ⟨5915159778360967201174547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943439852240644800783031 5915159778360967201174547)
      ·
        refine ⟨8872739667541450801761821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5915159778360967201174547 8872739667541450801761821)
        ·
          refine ⟨3327277375328044050660683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8872739667541450801761821 3327277375328044050660683)
          ·
            refine ⟨4990916062992066075991025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327277375328044050660683 4990916062992066075991025)
            ·
              refine ⟨3743187047244049556993269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4990916062992066075991025 3743187047244049556993269)
              ·
                refine ⟨350923785679129645968119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3743187047244049556993269 350923785679129645968119)
                ·
                  refine ⟨526385678518694468952179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350923785679129645968119 526385678518694468952179)
                  ·
                    refine ⟨789578517778041703428269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526385678518694468952179 789578517778041703428269)
                    ·
                      refine ⟨296091944166765638785601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789578517778041703428269 296091944166765638785601)
                      ·
                        rfl

theorem cell23_576637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_576637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576637 prefixEnd_576637 := by exact prefixLift 576637
  have htrace : WordTrace (prefixWord ++ tailWord_576637) baseStart_576637 baseEnd_576637 := by
    simpa [prefixWord, tailWord_576637, baseEnd_576637] using wordTrace_append hprefix tailTrace_576637
  have hstable : (prefixWord ++ tailWord_576637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576637).length < 2 ^ (prefixWord ++ tailWord_576637).sum := by decide
  have hdescent : baseEnd_576637 < baseStart_576637 := by decide
  rcases family_descends (prefixWord ++ tailWord_576637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576654 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_576654 : Nat := 118140960795 + 576654 * 2 ^ 59
def prefixEnd_576654 : Nat := 4983230072969 + 3 ^ 40 * 576654 * 2
def baseEnd_576654 : Nat := 296100673337892072273023

theorem tailTrace_576654 : CollatzResearch.WordTrace tailWord_576654 prefixEnd_576654 296100673337892072273023 := by
  unfold tailWord_576654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629037406611064688443127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14021532835259011671696677 2629037406611064688443127)
  ·
    refine ⟨3943556109916597032664691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629037406611064688443127 3943556109916597032664691)
    ·
      refine ⟨5915334164874895548997037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3943556109916597032664691 5915334164874895548997037)
      ·
        refine ⟨2218250311828085830873889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5915334164874895548997037 2218250311828085830873889)
        ·
          refine ⟨1663687733871064373155417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218250311828085830873889 1663687733871064373155417)
          ·
            refine ⟨1247765800403298279866563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663687733871064373155417 1247765800403298279866563)
            ·
              refine ⟨1871648700604947419799845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247765800403298279866563 1871648700604947419799845)
              ·
                refine ⟨350934131363427641212471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1871648700604947419799845 350934131363427641212471)
                ·
                  refine ⟨526401197045141461818707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 350934131363427641212471 526401197045141461818707)
                  ·
                    refine ⟨789601795567712192728061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526401197045141461818707 789601795567712192728061)
                    ·
                      refine ⟨296100673337892072273023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789601795567712192728061 296100673337892072273023)
                      ·
                        rfl

theorem cell23_576654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_576654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576654 prefixEnd_576654 := by exact prefixLift 576654
  have htrace : WordTrace (prefixWord ++ tailWord_576654) baseStart_576654 baseEnd_576654 := by
    simpa [prefixWord, tailWord_576654, baseEnd_576654] using wordTrace_append hprefix tailTrace_576654
  have hstable : (prefixWord ++ tailWord_576654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576654).length < 2 ^ (prefixWord ++ tailWord_576654).sum := by decide
  have hdescent : baseEnd_576654 < baseStart_576654 := by decide
  rcases family_descends (prefixWord ++ tailWord_576654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576656 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_576656 : Nat := 118140960795 + 576656 * 2 ^ 59
def prefixEnd_576656 : Nat := 4983230072969 + 3 ^ 40 * 576656 * 2
def baseEnd_576656 : Nat := 296101700299201064448013

theorem tailTrace_576656 : CollatzResearch.WordTrace tailWord_576656 prefixEnd_576656 296101700299201064448013 := by
  unfold tailWord_576656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516186099440635924558911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14021581465920847899411881 10516186099440635924558911)
  ·
    refine ⟨15774279149160953886838367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10516186099440635924558911 15774279149160953886838367)
    ·
      refine ⟨23661418723741430830257551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15774279149160953886838367 23661418723741430830257551)
      ·
        refine ⟨35492128085612146245386327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23661418723741430830257551 35492128085612146245386327)
        ·
          refine ⟨53238192128418219368079491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35492128085612146245386327 53238192128418219368079491)
          ·
            refine ⟨79857288192627329052119237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53238192128418219368079491 79857288192627329052119237)
            ·
              refine ⟨14973241536117624197272357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79857288192627329052119237 14973241536117624197272357)
              ·
                refine ⟨2807482788022054536988567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14973241536117624197272357 2807482788022054536988567)
                ·
                  refine ⟨4211224182033081805482851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2807482788022054536988567 4211224182033081805482851)
                  ·
                    refine ⟨6316836273049622708224277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4211224182033081805482851 6316836273049622708224277)
                    ·
                      refine ⟨296101700299201064448013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6316836273049622708224277 296101700299201064448013)
                      ·
                        rfl

theorem cell23_576656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_576656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576656 prefixEnd_576656 := by exact prefixLift 576656
  have htrace : WordTrace (prefixWord ++ tailWord_576656) baseStart_576656 baseEnd_576656 := by
    simpa [prefixWord, tailWord_576656, baseEnd_576656] using wordTrace_append hprefix tailTrace_576656
  have hstable : (prefixWord ++ tailWord_576656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576656).length < 2 ^ (prefixWord ++ tailWord_576656).sum := by decide
  have hdescent : baseEnd_576656 < baseStart_576656 := by decide
  rcases family_descends (prefixWord ++ tailWord_576656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576670 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_576670 : Nat := 118140960795 + 576670 * 2 ^ 59
def prefixEnd_576670 : Nat := 4983230072969 + 3 ^ 40 * 576670 * 2
def baseEnd_576670 : Nat := 98702963009454669890983

theorem tailTrace_576670 : CollatzResearch.WordTrace tailWord_576670 prefixEnd_576670 98702963009454669890983 := by
  unfold tailWord_576670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629110352603819030015933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14021921880553701493418309 2629110352603819030015933)
  ·
    refine ⟨985916382226432136255975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2629110352603819030015933 985916382226432136255975)
    ·
      refine ⟨1478874573339648204383963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 985916382226432136255975 1478874573339648204383963)
      ·
        refine ⟨2218311860009472306575945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478874573339648204383963 2218311860009472306575945)
        ·
          refine ⟨1663733895007104229931959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218311860009472306575945 1663733895007104229931959)
          ·
            refine ⟨2495600842510656344897939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663733895007104229931959 2495600842510656344897939)
            ·
              refine ⟨3743401263765984517346909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495600842510656344897939 3743401263765984517346909)
              ·
                refine ⟨1403775473912244194005091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3743401263765984517346909 1403775473912244194005091)
                ·
                  refine ⟨2105663210868366291007637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403775473912244194005091 2105663210868366291007637)
                  ·
                    refine ⟨98702963009454669890983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2105663210868366291007637 98702963009454669890983)
                    ·
                      rfl

theorem cell23_576670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_576670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576670 prefixEnd_576670 := by exact prefixLift 576670
  have htrace : WordTrace (prefixWord ++ tailWord_576670) baseStart_576670 baseEnd_576670 := by
    simpa [prefixWord, tailWord_576670, baseEnd_576670] using wordTrace_append hprefix tailTrace_576670
  have hstable : (prefixWord ++ tailWord_576670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576670).length < 2 ^ (prefixWord ++ tailWord_576670).sum := by decide
  have hdescent : baseEnd_576670 < baseStart_576670 := by decide
  rcases family_descends (prefixWord ++ tailWord_576670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576677 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 3, 2, 2]
def baseStart_576677 : Nat := 118140960795 + 576677 * 2 ^ 59
def prefixEnd_576677 : Nat := 4983230072969 + 3 ^ 40 * 576677 * 2
def baseEnd_576677 : Nat := 296112483392945482285417

theorem tailTrace_576677 : CollatzResearch.WordTrace tailWord_576677 prefixEnd_576677 296112483392945482285417 := by
  unfold tailWord_576677
  simp only [CollatzResearch.WordTrace]
  refine ⟨21033138131805192435632285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14022092087870128290421523 21033138131805192435632285)
  ·
    refine ⟨7887426799426947163362107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21033138131805192435632285 7887426799426947163362107)
    ·
      refine ⟨11831140199140420745043161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7887426799426947163362107 11831140199140420745043161)
      ·
        refine ⟨8873355149355315558782371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11831140199140420745043161 8873355149355315558782371)
        ·
          refine ⟨13310032724032973338173557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8873355149355315558782371 13310032724032973338173557)
          ·
            refine ⟨1247815567878091250453771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13310032724032973338173557 1247815567878091250453771)
            ·
              refine ⟨1871723351817136875680657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247815567878091250453771 1871723351817136875680657)
              ·
                refine ⟨1403792513862852656760493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871723351817136875680657 1403792513862852656760493)
                ·
                  refine ⟨526422192698569746285185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1403792513862852656760493 526422192698569746285185)
                  ·
                    refine ⟨394816644523927309713889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 526422192698569746285185 394816644523927309713889)
                    ·
                      refine ⟨296112483392945482285417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394816644523927309713889 296112483392945482285417)
                      ·
                        rfl

theorem cell23_576677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_576677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576677 prefixEnd_576677 := by exact prefixLift 576677
  have htrace : WordTrace (prefixWord ++ tailWord_576677) baseStart_576677 baseEnd_576677 := by
    simpa [prefixWord, tailWord_576677, baseEnd_576677] using wordTrace_append hprefix tailTrace_576677
  have hstable : (prefixWord ++ tailWord_576677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576677).length < 2 ^ (prefixWord ++ tailWord_576677).sum := by decide
  have hdescent : baseEnd_576677 < baseStart_576677 := by decide
  rcases family_descends (prefixWord ++ tailWord_576677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576696 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_576696 : Nat := 118140960795 + 576696 * 2 ^ 59
def prefixEnd_576696 : Nat := 4983230072969 + 3 ^ 40 * 576696 * 2
def baseEnd_576696 : Nat := 98707413175126969315943

theorem tailTrace_576696 : CollatzResearch.WordTrace tailWord_576696 prefixEnd_576696 98707413175126969315943 := by
  unfold tailWord_576696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516915559368179340286971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14022554079157572453715961 10516915559368179340286971)
  ·
    refine ⟨15775373339052269010430457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10516915559368179340286971 15775373339052269010430457)
    ·
      refine ⟨11831530004289201757822843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15775373339052269010430457 11831530004289201757822843)
      ·
        refine ⟨17747295006433802636734265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11831530004289201757822843 17747295006433802636734265)
        ·
          refine ⟨13310471254825351977550699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17747295006433802636734265 13310471254825351977550699)
          ·
            refine ⟨19965706882238027966326049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13310471254825351977550699 19965706882238027966326049)
            ·
              refine ⟨14974280161678520974744537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19965706882238027966326049 14974280161678520974744537)
              ·
                refine ⟨11230710121258890731058403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14974280161678520974744537 11230710121258890731058403)
                ·
                  refine ⟨16846065181888336096587605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11230710121258890731058403 16846065181888336096587605)
                  ·
                    refine ⟨98707413175126969315943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16846065181888336096587605 98707413175126969315943)
                    ·
                      rfl

theorem cell23_576696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_576696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576696 prefixEnd_576696 := by exact prefixLift 576696
  have htrace : WordTrace (prefixWord ++ tailWord_576696) baseStart_576696 baseEnd_576696 := by
    simpa [prefixWord, tailWord_576696, baseEnd_576696] using wordTrace_append hprefix tailTrace_576696
  have hstable : (prefixWord ++ tailWord_576696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576696).length < 2 ^ (prefixWord ++ tailWord_576696).sum := by decide
  have hdescent : baseEnd_576696 < baseStart_576696 := by decide
  rcases family_descends (prefixWord ++ tailWord_576696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576697 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 1, 2, 3]
def baseStart_576697 : Nat := 118140960795 + 576697 * 2 ^ 59
def prefixEnd_576697 : Nat := 4983230072969 + 3 ^ 40 * 576697 * 2
def baseEnd_576697 : Nat := 296122753006035404035325

theorem tailTrace_576697 : CollatzResearch.WordTrace tailWord_576697 prefixEnd_576697 296122753006035404035325 := by
  unfold tailWord_576697
  simp only [CollatzResearch.WordTrace]
  refine ⟨21033867591732735851360345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14022578394488490567573563 21033867591732735851360345)
  ·
    refine ⟨15775400693799551888520259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21033867591732735851360345 15775400693799551888520259)
    ·
      refine ⟨23663101040699327832780389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15775400693799551888520259 23663101040699327832780389)
      ·
        refine ⟨4436831445131123968646323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23663101040699327832780389 4436831445131123968646323)
        ·
          refine ⟨6655247167696685952969485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436831445131123968646323 6655247167696685952969485)
          ·
            refine ⟨2495717687886257232363557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6655247167696685952969485 2495717687886257232363557)
            ·
              refine ⟨467947066478673231068167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2495717687886257232363557 467947066478673231068167)
              ·
                refine ⟨701920599718009846602251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467947066478673231068167 701920599718009846602251)
                ·
                  refine ⟨1052880899577014769903377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701920599718009846602251 1052880899577014769903377)
                  ·
                    refine ⟨789660674682761077427533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1052880899577014769903377 789660674682761077427533)
                    ·
                      refine ⟨296122753006035404035325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789660674682761077427533 296122753006035404035325)
                      ·
                        rfl

theorem cell23_576697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_576697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576697 prefixEnd_576697 := by exact prefixLift 576697
  have htrace : WordTrace (prefixWord ++ tailWord_576697) baseStart_576697 baseEnd_576697 := by
    simpa [prefixWord, tailWord_576697, baseEnd_576697] using wordTrace_append hprefix tailTrace_576697
  have hstable : (prefixWord ++ tailWord_576697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576697).length < 2 ^ (prefixWord ++ tailWord_576697).sum := by decide
  have hdescent : baseEnd_576697 < baseStart_576697 := by decide
  rcases family_descends (prefixWord ++ tailWord_576697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576704 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 2, 4]
def baseStart_576704 : Nat := 118140960795 + 576704 * 2 ^ 59
def prefixEnd_576704 : Nat := 4983230072969 + 3 ^ 40 * 576704 * 2
def baseEnd_576704 : Nat := 98708782456872292215931

theorem tailTrace_576704 : CollatzResearch.WordTrace tailWord_576704 prefixEnd_576704 98708782456872292215931 := by
  unfold tailWord_576704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517061451353688023432583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14022748601804917364576777 10517061451353688023432583)
  ·
    refine ⟨15775592177030532035148875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10517061451353688023432583 15775592177030532035148875)
    ·
      refine ⟨23663388265545798052723313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15775592177030532035148875 23663388265545798052723313)
      ·
        refine ⟨17747541199159348539542485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23663388265545798052723313 17747541199159348539542485)
        ·
          refine ⟨415957996855297231395527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17747541199159348539542485 415957996855297231395527)
          ·
            refine ⟨623936995282945847093291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415957996855297231395527 623936995282945847093291)
            ·
              refine ⟨935905492924418770639937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623936995282945847093291 935905492924418770639937)
              ·
                refine ⟨701929119693314077979953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935905492924418770639937 701929119693314077979953)
                ·
                  refine ⟨526446839769985558484965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 701929119693314077979953 526446839769985558484965)
                  ·
                    refine ⟨98708782456872292215931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526446839769985558484965 98708782456872292215931)
                    ·
                      rfl

theorem cell23_576704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_576704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576704 prefixEnd_576704 := by exact prefixLift 576704
  have htrace : WordTrace (prefixWord ++ tailWord_576704) baseStart_576704 baseEnd_576704 := by
    simpa [prefixWord, tailWord_576704, baseEnd_576704] using wordTrace_append hprefix tailTrace_576704
  have hstable : (prefixWord ++ tailWord_576704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576704).length < 2 ^ (prefixWord ++ tailWord_576704).sum := by decide
  have hdescent : baseEnd_576704 < baseStart_576704 := by decide
  rcases family_descends (prefixWord ++ tailWord_576704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576724 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_576724 : Nat := 118140960795 + 576724 * 2 ^ 59
def prefixEnd_576724 : Nat := 4983230072969 + 3 ^ 40 * 576724 * 2
def baseEnd_576724 : Nat := 296136616983706798397701

theorem tailTrace_576724 : CollatzResearch.WordTrace tailWord_576724 prefixEnd_576724 296136616983706798397701 := by
  unfold tailWord_576724
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517426181317459731296613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14023234908423279641728817 10517426181317459731296613)
  ·
    refine ⟨1972017408997023699618115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10517426181317459731296613 1972017408997023699618115)
    ·
      refine ⟨2958026113495535549427173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972017408997023699618115 2958026113495535549427173)
      ·
        refine ⟨554629896280412915517595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2958026113495535549427173 554629896280412915517595)
        ·
          refine ⟨831944844420619373276393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554629896280412915517595 831944844420619373276393)
          ·
            refine ⟨623958633315464529957295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831944844420619373276393 623958633315464529957295)
            ·
              refine ⟨935937949973196794935943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623958633315464529957295 935937949973196794935943)
              ·
                refine ⟨1403906924959795192403915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935937949973196794935943 1403906924959795192403915)
                ·
                  refine ⟨2105860387439692788605873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1403906924959795192403915 2105860387439692788605873)
                  ·
                    refine ⟨1579395290579769591454405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2105860387439692788605873 1579395290579769591454405)
                    ·
                      refine ⟨296136616983706798397701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1579395290579769591454405 296136616983706798397701)
                      ·
                        rfl

theorem cell23_576724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_576724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576724 prefixEnd_576724 := by exact prefixLift 576724
  have htrace : WordTrace (prefixWord ++ tailWord_576724) baseStart_576724 baseEnd_576724 := by
    simpa [prefixWord, tailWord_576724, baseEnd_576724] using wordTrace_append hprefix tailTrace_576724
  have hstable : (prefixWord ++ tailWord_576724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576724).length < 2 ^ (prefixWord ++ tailWord_576724).sum := by decide
  have hdescent : baseEnd_576724 < baseStart_576724 := by decide
  rcases family_descends (prefixWord ++ tailWord_576724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576737 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 1, 3, 2]
def baseStart_576737 : Nat := 118140960795 + 576737 * 2 ^ 59
def prefixEnd_576737 : Nat := 4983230072969 + 3 ^ 40 * 576737 * 2
def baseEnd_576737 : Nat := 296143292232215247535141

theorem tailTrace_576737 : CollatzResearch.WordTrace tailWord_576737 prefixEnd_576737 296143292232215247535141 := by
  unfold tailWord_576737
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035326511587822682816465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14023551007725215121877643 21035326511587822682816465)
  ·
    refine ⟨15776494883690867012112349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21035326511587822682816465 15776494883690867012112349)
    ·
      refine ⟨5916185581384075129542131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15776494883690867012112349 5916185581384075129542131)
      ·
        refine ⟨8874278372076112694313197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5916185581384075129542131 8874278372076112694313197)
        ·
          refine ⟨3327854389528542260367449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8874278372076112694313197 3327854389528542260367449)
          ·
            refine ⟨2495890792146406695275587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3327854389528542260367449 2495890792146406695275587)
            ·
              refine ⟨3743836188219610042913381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495890792146406695275587 3743836188219610042913381)
              ·
                refine ⟨701969285291176883046259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3743836188219610042913381 701969285291176883046259)
                ·
                  refine ⟨1052953927936765324569389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 701969285291176883046259 1052953927936765324569389)
                  ·
                    refine ⟨394857722976286996713521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1052953927936765324569389 394857722976286996713521)
                    ·
                      refine ⟨296143292232215247535141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394857722976286996713521 296143292232215247535141)
                      ·
                        rfl

theorem cell23_576737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_576737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576737 prefixEnd_576737 := by exact prefixLift 576737
  have htrace : WordTrace (prefixWord ++ tailWord_576737) baseStart_576737 baseEnd_576737 := by
    simpa [prefixWord, tailWord_576737, baseEnd_576737] using wordTrace_append hprefix tailTrace_576737
  have hstable : (prefixWord ++ tailWord_576737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576737).length < 2 ^ (prefixWord ++ tailWord_576737).sum := by decide
  have hdescent : baseEnd_576737 < baseStart_576737 := by decide
  rcases family_descends (prefixWord ++ tailWord_576737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576753 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_576753 : Nat := 118140960795 + 576753 * 2 ^ 59
def prefixEnd_576753 : Nat := 4983230072969 + 3 ^ 40 * 576753 * 2
def baseEnd_576753 : Nat := 296151507922687184935067

theorem tailTrace_576753 : CollatzResearch.WordTrace tailWord_576753 prefixEnd_576753 296151507922687184935067 := by
  unfold tailWord_576753
  simp only [CollatzResearch.WordTrace]
  refine ⟨21035910079529857415398913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14023940053019904943599275 21035910079529857415398913)
  ·
    refine ⟨15776932559647393061549185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21035910079529857415398913 15776932559647393061549185)
    ·
      refine ⟨11832699419735544796161889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15776932559647393061549185 11832699419735544796161889)
      ·
        refine ⟨8874524564801658597121417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11832699419735544796161889 8874524564801658597121417)
        ·
          refine ⟨6655893423601243947841063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8874524564801658597121417 6655893423601243947841063)
          ·
            refine ⟨9983840135401865921761595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655893423601243947841063 9983840135401865921761595)
            ·
              refine ⟨14975760203102798882642393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9983840135401865921761595 14975760203102798882642393)
              ·
                refine ⟨11231820152327099161981795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14975760203102798882642393 11231820152327099161981795)
                ·
                  refine ⟨16847730228490648742972693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11231820152327099161981795 16847730228490648742972693)
                  ·
                    refine ⟨789737354460499159826845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16847730228490648742972693 789737354460499159826845)
                    ·
                      refine ⟨296151507922687184935067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789737354460499159826845 296151507922687184935067)
                      ·
                        rfl

theorem cell23_576753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_576753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576753 prefixEnd_576753 := by exact prefixLift 576753
  have htrace : WordTrace (prefixWord ++ tailWord_576753) baseStart_576753 baseEnd_576753 := by
    simpa [prefixWord, tailWord_576753, baseEnd_576753] using wordTrace_append hprefix tailTrace_576753
  have hstable : (prefixWord ++ tailWord_576753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576753).length < 2 ^ (prefixWord ++ tailWord_576753).sum := by decide
  have hdescent : baseEnd_576753 < baseStart_576753 := by decide
  rcases family_descends (prefixWord ++ tailWord_576753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576767 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 4, 2, 2]
def baseStart_576767 : Nat := 118140960795 + 576767 * 2 ^ 59
def prefixEnd_576767 : Nat := 4983230072969 + 3 ^ 40 * 576767 * 2
def baseEnd_576767 : Nat := 296158696651850130160003

theorem tailTrace_576767 : CollatzResearch.WordTrace tailWord_576767 prefixEnd_576767 296158696651850130160003 := by
  unfold tailWord_576767
  simp only [CollatzResearch.WordTrace]
  refine ⟨21036420701479137806408555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14024280467652758537605703 21036420701479137806408555)
  ·
    refine ⟨31554631052218706709612833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21036420701479137806408555 31554631052218706709612833)
    ·
      refine ⟨23665973289164030032209625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31554631052218706709612833 23665973289164030032209625)
      ·
        refine ⟨17749479966873022524157219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23665973289164030032209625 17749479966873022524157219)
        ·
          refine ⟨26624219950309533786235829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17749479966873022524157219 26624219950309533786235829)
          ·
            refine ⟨2496020620341518792459609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26624219950309533786235829 2496020620341518792459609)
            ·
              refine ⟨1872015465256139094344707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496020620341518792459609 1872015465256139094344707)
              ·
                refine ⟨2808023197884208641517061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872015465256139094344707 2808023197884208641517061)
                ·
                  refine ⟨526504349603289120284449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2808023197884208641517061 526504349603289120284449)
                  ·
                    refine ⟨394878262202466840213337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 526504349603289120284449 394878262202466840213337)
                    ·
                      refine ⟨296158696651850130160003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394878262202466840213337 296158696651850130160003)
                      ·
                        rfl

theorem cell23_576767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_576767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576767 prefixEnd_576767 := by exact prefixLift 576767
  have htrace : WordTrace (prefixWord ++ tailWord_576767) baseStart_576767 baseEnd_576767 := by
    simpa [prefixWord, tailWord_576767, baseEnd_576767] using wordTrace_append hprefix tailTrace_576767
  have hstable : (prefixWord ++ tailWord_576767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576767).length < 2 ^ (prefixWord ++ tailWord_576767).sum := by decide
  have hdescent : baseEnd_576767 < baseStart_576767 := by decide
  rcases family_descends (prefixWord ++ tailWord_576767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576823 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_576823 : Nat := 118140960795 + 576823 * 2 ^ 59
def prefixEnd_576823 : Nat := 4983230072969 + 3 ^ 40 * 576823 * 2
def baseEnd_576823 : Nat := 296187451568501911059745

theorem tailTrace_576823 : CollatzResearch.WordTrace tailWord_576823 prefixEnd_576823 296187451568501911059745 := by
  unfold tailWord_576823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038463189276259370447123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14025642126184172913631415 21038463189276259370447123)
  ·
    refine ⟨31557694783914389055670685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21038463189276259370447123 31557694783914389055670685)
    ·
      refine ⟨11834135543967895895876507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31557694783914389055670685 11834135543967895895876507)
      ·
        refine ⟨17751203315951843843814761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11834135543967895895876507 17751203315951843843814761)
        ·
          refine ⟨13313402486963882882861071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17751203315951843843814761 13313402486963882882861071)
          ·
            refine ⟨19970103730445824324291607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13313402486963882882861071 19970103730445824324291607)
            ·
              refine ⟨29955155595668736486437411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19970103730445824324291607 29955155595668736486437411)
              ·
                refine ⟨44932733393503104729656117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29955155595668736486437411 44932733393503104729656117)
                ·
                  refine ⟨4212443755640916068405261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44932733393503104729656117 4212443755640916068405261)
                  ·
                    refine ⟨1579666408365343525651973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4212443755640916068405261 1579666408365343525651973)
                    ·
                      refine ⟨296187451568501911059745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1579666408365343525651973 296187451568501911059745)
                      ·
                        rfl

theorem cell23_576823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_576823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576823 prefixEnd_576823 := by exact prefixLift 576823
  have htrace : WordTrace (prefixWord ++ tailWord_576823) baseStart_576823 baseEnd_576823 := by
    simpa [prefixWord, tailWord_576823, baseEnd_576823] using wordTrace_append hprefix tailTrace_576823
  have hstable : (prefixWord ++ tailWord_576823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576823).length < 2 ^ (prefixWord ++ tailWord_576823).sum := by decide
  have hdescent : baseEnd_576823 < baseStart_576823 := by decide
  rcases family_descends (prefixWord ++ tailWord_576823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576830 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_576830 : Nat := 118140960795 + 576830 * 2 ^ 59
def prefixEnd_576830 : Nat := 4983230072969 + 3 ^ 40 * 576830 * 2
def baseEnd_576830 : Nat := 296191045933083383672213

theorem tailTrace_576830 : CollatzResearch.WordTrace tailWord_576830 prefixEnd_576830 296191045933083383672213 := by
  unfold tailWord_576830
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629839812531362445743993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14025812333500599710634629 2629839812531362445743993)
  ·
    refine ⟨1972379859398521834307995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2629839812531362445743993 1972379859398521834307995)
    ·
      refine ⟨2958569789097782751461993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972379859398521834307995 2958569789097782751461993)
      ·
        refine ⟨2218927341823337063596495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2958569789097782751461993 2218927341823337063596495)
        ·
          refine ⟨3328391012735005595394743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218927341823337063596495 3328391012735005595394743)
          ·
            refine ⟨4992586519102508393092115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3328391012735005595394743 4992586519102508393092115)
            ·
              refine ⟨7488879778653762589638173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4992586519102508393092115 7488879778653762589638173)
              ·
                refine ⟨2808329916995160971114315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7488879778653762589638173 2808329916995160971114315)
                ·
                  refine ⟨4212494875492741456671473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808329916995160971114315 4212494875492741456671473)
                  ·
                    refine ⟨3159371156619556092503605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4212494875492741456671473 3159371156619556092503605)
                    ·
                      refine ⟨296191045933083383672213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3159371156619556092503605 296191045933083383672213)
                      ·
                        rfl

theorem cell23_576830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_576830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576830 prefixEnd_576830 := by exact prefixLift 576830
  have htrace : WordTrace (prefixWord ++ tailWord_576830) baseStart_576830 baseEnd_576830 := by
    simpa [prefixWord, tailWord_576830, baseEnd_576830] using wordTrace_append hprefix tailTrace_576830
  have hstable : (prefixWord ++ tailWord_576830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576830).length < 2 ^ (prefixWord ++ tailWord_576830).sum := by decide
  have hdescent : baseEnd_576830 < baseStart_576830 := by decide
  rcases family_descends (prefixWord ++ tailWord_576830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576863 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 8]
def baseStart_576863 : Nat := 118140960795 + 576863 * 2 ^ 59
def prefixEnd_576863 : Nat := 4983230072969 + 3 ^ 40 * 576863 * 2
def baseEnd_576863 : Nat := 32911998977186861617729

theorem tailTrace_576863 : CollatzResearch.WordTrace tailWord_576863 prefixEnd_576863 32911998977186861617729 := by
  unfold tailWord_576863
  simp only [CollatzResearch.WordTrace]
  refine ⟨21039922109131346201903243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14026614739420897467935495 21039922109131346201903243)
  ·
    refine ⟨31559883163697019302854865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21039922109131346201903243 31559883163697019302854865)
    ·
      refine ⟨23669912372772764477141149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31559883163697019302854865 23669912372772764477141149)
      ·
        refine ⟨8876217139789786678927931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23669912372772764477141149 8876217139789786678927931)
        ·
          refine ⟨13314325709684680018391897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8876217139789786678927931 13314325709684680018391897)
          ·
            refine ⟨9985744282263510013793923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13314325709684680018391897 9985744282263510013793923)
            ·
              refine ⟨14978616423395265020690885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9985744282263510013793923 14978616423395265020690885)
              ·
                refine ⟨2808490579386612191379541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14978616423395265020690885 2808490579386612191379541)
                ·
                  refine ⟨32911998977186861617729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2808490579386612191379541 32911998977186861617729)
                  ·
                    rfl

theorem cell23_576863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 8].length) (baseStart_576863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576863 prefixEnd_576863 := by exact prefixLift 576863
  have htrace : WordTrace (prefixWord ++ tailWord_576863) baseStart_576863 baseEnd_576863 := by
    simpa [prefixWord, tailWord_576863, baseEnd_576863] using wordTrace_append hprefix tailTrace_576863
  have hstable : (prefixWord ++ tailWord_576863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576863).length < 2 ^ (prefixWord ++ tailWord_576863).sum := by decide
  have hdescent : baseEnd_576863 < baseStart_576863 := by decide
  rcases family_descends (prefixWord ++ tailWord_576863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576907 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 3]
def baseStart_576907 : Nat := 118140960795 + 576907 * 2 ^ 59
def prefixEnd_576907 : Nat := 4983230072969 + 3 ^ 40 * 576907 * 2
def baseEnd_576907 : Nat := 296230583943479582409359

theorem tailTrace_576907 : CollatzResearch.WordTrace tailWord_576907 prefixEnd_576907 296230583943479582409359 := by
  unfold tailWord_576907
  simp only [CollatzResearch.WordTrace]
  refine ⟨21041526920971941716504975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14027684613981294477669983 21041526920971941716504975)
  ·
    refine ⟨31562290381457912574757463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21041526920971941716504975 31562290381457912574757463)
    ·
      refine ⟨47343435572186868862136195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31562290381457912574757463 47343435572186868862136195)
      ·
        refine ⟨71015153358280303293204293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47343435572186868862136195 71015153358280303293204293)
        ·
          refine ⟨13315341254677556867475805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71015153358280303293204293 13315341254677556867475805)
          ·
            refine ⟨4993252970504083825303427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13315341254677556867475805 4993252970504083825303427)
            ·
              refine ⟨7489879455756125737955141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4993252970504083825303427 7489879455756125737955141)
              ·
                refine ⟨1404352397954273575866589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7489879455756125737955141 1404352397954273575866589)
                ·
                  refine ⟨526632149232852590949971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1404352397954273575866589 526632149232852590949971)
                  ·
                    refine ⟨789948223849278886424957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526632149232852590949971 789948223849278886424957)
                    ·
                      refine ⟨296230583943479582409359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789948223849278886424957 296230583943479582409359)
                      ·
                        rfl

theorem cell23_576907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 1, 3].length) (baseStart_576907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576907 prefixEnd_576907 := by exact prefixLift 576907
  have htrace : WordTrace (prefixWord ++ tailWord_576907) baseStart_576907 baseEnd_576907 := by
    simpa [prefixWord, tailWord_576907, baseEnd_576907] using wordTrace_append hprefix tailTrace_576907
  have hstable : (prefixWord ++ tailWord_576907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576907).length < 2 ^ (prefixWord ++ tailWord_576907).sum := by decide
  have hdescent : baseEnd_576907 < baseStart_576907 := by decide
  rcases family_descends (prefixWord ++ tailWord_576907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576917 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 5, 2]
def baseStart_576917 : Nat := 118140960795 + 576917 * 2 ^ 59
def prefixEnd_576917 : Nat := 4983230072969 + 3 ^ 40 * 576917 * 2
def baseEnd_576917 : Nat := 296235718750024543284313

theorem tailTrace_576917 : CollatzResearch.WordTrace tailWord_576917 prefixEnd_576917 296235718750024543284313 := by
  unfold tailWord_576917
  simp only [CollatzResearch.WordTrace]
  refine ⟨21041891650935713424369005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14027927767290475616246003 21041891650935713424369005)
  ·
    refine ⟨7890709369100892534138377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21041891650935713424369005 7890709369100892534138377)
    ·
      refine ⟨5918032026825669400603783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7890709369100892534138377 5918032026825669400603783)
      ·
        refine ⟨8877048040238504100905675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918032026825669400603783 8877048040238504100905675)
        ·
          refine ⟨13315572060357756151358513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877048040238504100905675 13315572060357756151358513)
          ·
            refine ⟨9986679045268317113518885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13315572060357756151358513 9986679045268317113518885)
            ·
              refine ⟨1872502320987809458784791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9986679045268317113518885 1872502320987809458784791)
              ·
                refine ⟨2808753481481714188177187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872502320987809458784791 2808753481481714188177187)
                ·
                  refine ⟨4213130222222571282265781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808753481481714188177187 4213130222222571282265781)
                  ·
                    refine ⟨394980958333366057712417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4213130222222571282265781 394980958333366057712417)
                    ·
                      refine ⟨296235718750024543284313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 394980958333366057712417 296235718750024543284313)
                      ·
                        rfl

theorem cell23_576917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_576917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576917 prefixEnd_576917 := by exact prefixLift 576917
  have htrace : WordTrace (prefixWord ++ tailWord_576917) baseStart_576917 baseEnd_576917 := by
    simpa [prefixWord, tailWord_576917, baseEnd_576917] using wordTrace_append hprefix tailTrace_576917
  have hstable : (prefixWord ++ tailWord_576917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576917).length < 2 ^ (prefixWord ++ tailWord_576917).sum := by decide
  have hdescent : baseEnd_576917 < baseStart_576917 := by decide
  rcases family_descends (prefixWord ++ tailWord_576917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576923 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 10]
def baseStart_576923 : Nat := 118140960795 + 576923 * 2 ^ 59
def prefixEnd_576923 : Nat := 4983230072969 + 3 ^ 40 * 576923 * 2
def baseEnd_576923 : Nat := 98746266544650506603095

theorem tailTrace_576923 : CollatzResearch.WordTrace tailWord_576923 prefixEnd_576923 98746266544650506603095 := by
  unfold tailWord_576923
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042110488913976449087423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028073659275984299391615 21042110488913976449087423)
  ·
    refine ⟨31563165733370964673631135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21042110488913976449087423 31563165733370964673631135)
    ·
      refine ⟨47344748600056447010446703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31563165733370964673631135 47344748600056447010446703)
      ·
        refine ⟨71017122900084670515670055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47344748600056447010446703 71017122900084670515670055)
        ·
          refine ⟨106525684350127005773505083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71017122900084670515670055 106525684350127005773505083)
          ·
            refine ⟨159788526525190508660257625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106525684350127005773505083 159788526525190508660257625)
            ·
              refine ⟨119841394893892881495193219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159788526525190508660257625 119841394893892881495193219)
              ·
                refine ⟨179762092340839322242789829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119841394893892881495193219 179762092340839322242789829)
                ·
                  refine ⟨33705392313907372920523093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179762092340839322242789829 33705392313907372920523093)
                  ·
                    refine ⟨98746266544650506603095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 33705392313907372920523093 98746266544650506603095)
                    ·
                      rfl

theorem cell23_576923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 10].length) (baseStart_576923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576923 prefixEnd_576923 := by exact prefixLift 576923
  have htrace : WordTrace (prefixWord ++ tailWord_576923) baseStart_576923 baseEnd_576923 := by
    simpa [prefixWord, tailWord_576923, baseEnd_576923] using wordTrace_append hprefix tailTrace_576923
  have hstable : (prefixWord ++ tailWord_576923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576923).length < 2 ^ (prefixWord ++ tailWord_576923).sum := by decide
  have hdescent : baseEnd_576923 < baseStart_576923 := by decide
  rcases family_descends (prefixWord ++ tailWord_576923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576927 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 1, 5]
def baseStart_576927 : Nat := 118140960795 + 576927 * 2 ^ 59
def prefixEnd_576927 : Nat := 4983230072969 + 3 ^ 40 * 576927 * 2
def baseEnd_576927 : Nat := 98746951185523168053089

theorem tailTrace_576927 : CollatzResearch.WordTrace tailWord_576927 prefixEnd_576927 98746951185523168053089 := by
  unfold tailWord_576927
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042256380899485132233035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028170920599656754822023 21042256380899485132233035)
  ·
    refine ⟨31563384571349227698349553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21042256380899485132233035 31563384571349227698349553)
    ·
      refine ⟨23672538428511920773762165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31563384571349227698349553 23672538428511920773762165)
      ·
        refine ⟨2219300477672992572540203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23672538428511920773762165 2219300477672992572540203)
        ·
          refine ⟨3328950716509488858810305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219300477672992572540203 3328950716509488858810305)
          ·
            refine ⟨2496713037382116644107729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3328950716509488858810305 2496713037382116644107729)
            ·
              refine ⟨1872534778036587483080797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496713037382116644107729 1872534778036587483080797)
              ·
                refine ⟨702200541763720306155299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1872534778036587483080797 702200541763720306155299)
                ·
                  refine ⟨1053300812645580459232949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702200541763720306155299 1053300812645580459232949)
                  ·
                    refine ⟨98746951185523168053089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1053300812645580459232949 98746951185523168053089)
                    ·
                      rfl

theorem cell23_576927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_576927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576927 prefixEnd_576927 := by exact prefixLift 576927
  have htrace : WordTrace (prefixWord ++ tailWord_576927) baseStart_576927 baseEnd_576927 := by
    simpa [prefixWord, tailWord_576927, baseEnd_576927] using wordTrace_append hprefix tailTrace_576927
  have hstable : (prefixWord ++ tailWord_576927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576927).length < 2 ^ (prefixWord ++ tailWord_576927).sum := by decide
  have hdescent : baseEnd_576927 < baseStart_576927 := by decide
  rcases family_descends (prefixWord ++ tailWord_576927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576941 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_576941 : Nat := 118140960795 + 576941 * 2 ^ 59
def prefixEnd_576941 : Nat := 4983230072969 + 3 ^ 40 * 576941 * 2
def baseEnd_576941 : Nat := 296248042285732449384203

theorem tailTrace_576941 : CollatzResearch.WordTrace tailWord_576941 prefixEnd_576941 296248042285732449384203 := by
  unfold tailWord_576941
  simp only [CollatzResearch.WordTrace]
  refine ⟨21042767002848765523242677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028511335232510348828451 21042767002848765523242677)
  ·
    refine ⟨1972759406517071767804001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21042767002848765523242677 1972759406517071767804001)
    ·
      refine ⟨1479569554887803825853001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1972759406517071767804001 1479569554887803825853001)
      ·
        refine ⟨1109677166165852869389751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479569554887803825853001 1109677166165852869389751)
        ·
          refine ⟨1664515749248779304084627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109677166165852869389751 1664515749248779304084627)
          ·
            refine ⟨2496773623873168956126941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1664515749248779304084627 2496773623873168956126941)
            ·
              refine ⟨936290108952438358547603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2496773623873168956126941 936290108952438358547603)
              ·
                refine ⟨1404435163428657537821405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936290108952438358547603 1404435163428657537821405)
                ·
                  refine ⟨526663186285746576683027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1404435163428657537821405 526663186285746576683027)
                  ·
                    refine ⟨789994779428619865024541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526663186285746576683027 789994779428619865024541)
                    ·
                      refine ⟨296248042285732449384203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 789994779428619865024541 296248042285732449384203)
                      ·
                        rfl

theorem cell23_576941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_576941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576941 prefixEnd_576941 := by exact prefixLift 576941
  have htrace : WordTrace (prefixWord ++ tailWord_576941) baseStart_576941 baseEnd_576941 := by
    simpa [prefixWord, tailWord_576941, baseEnd_576941] using wordTrace_append hprefix tailTrace_576941
  have hstable : (prefixWord ++ tailWord_576941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576941).length < 2 ^ (prefixWord ++ tailWord_576941).sum := by decide
  have hdescent : baseEnd_576941 < baseStart_576941 := by decide
  rcases family_descends (prefixWord ++ tailWord_576941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576960 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_576960 : Nat := 118140960795 + 576960 * 2 ^ 59
def prefixEnd_576960 : Nat := 4983230072969 + 3 ^ 40 * 576960 * 2
def baseEnd_576960 : Nat := 296257798418167875046615

theorem tailTrace_576960 : CollatzResearch.WordTrace tailWord_576960 prefixEnd_576960 296257798418167875046615 := by
  unfold tailWord_576960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521729994889965884092167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14028973326519954512122889 10521729994889965884092167)
  ·
    refine ⟨15782594992334948826138251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10521729994889965884092167 15782594992334948826138251)
    ·
      refine ⟨23673892488502423239207377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15782594992334948826138251 23673892488502423239207377)
      ·
        refine ⟨17755419366376817429405533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23673892488502423239207377 17755419366376817429405533)
        ·
          refine ⟨6658282262391306536027075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17755419366376817429405533 6658282262391306536027075)
          ·
            refine ⟨9987423393586959804040613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6658282262391306536027075 9987423393586959804040613)
            ·
              refine ⟨1872641886297554963257615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9987423393586959804040613 1872641886297554963257615)
              ·
                refine ⟨2808962829446332444886423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872641886297554963257615 2808962829446332444886423)
                ·
                  refine ⟨4213444244169498667329635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2808962829446332444886423 4213444244169498667329635)
                  ·
                    refine ⟨6320166366254248000994453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4213444244169498667329635 6320166366254248000994453)
                    ·
                      refine ⟨296257798418167875046615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6320166366254248000994453 296257798418167875046615)
                      ·
                        rfl

theorem cell23_576960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_576960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576960 prefixEnd_576960 := by exact prefixLift 576960
  have htrace : WordTrace (prefixWord ++ tailWord_576960) baseStart_576960 baseEnd_576960 := by
    simpa [prefixWord, tailWord_576960, baseEnd_576960] using wordTrace_append hprefix tailTrace_576960
  have hstable : (prefixWord ++ tailWord_576960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576960).length < 2 ^ (prefixWord ++ tailWord_576960).sum := by decide
  have hdescent : baseEnd_576960 < baseStart_576960 := by decide
  rcases family_descends (prefixWord ++ tailWord_576960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576964 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_576964 : Nat := 118140960795 + 576964 * 2 ^ 59
def prefixEnd_576964 : Nat := 4983230072969 + 3 ^ 40 * 576964 * 2
def baseEnd_576964 : Nat := 296259852340785859396597

theorem tailTrace_576964 : CollatzResearch.WordTrace tailWord_576964 prefixEnd_576964 296259852340785859396597 := by
  unfold tailWord_576964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521802940882720225664973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14029070587843626967553297 10521802940882720225664973)
  ·
    refine ⟨3945676102831020084624365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10521802940882720225664973 3945676102831020084624365)
    ·
      refine ⟨1479628538561632531734137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3945676102831020084624365 1479628538561632531734137)
      ·
        refine ⟨1109721403921224398800603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479628538561632531734137 1109721403921224398800603)
        ·
          refine ⟨1664582105881836598200905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109721403921224398800603 1664582105881836598200905)
          ·
            refine ⟨1248436579411377448650679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664582105881836598200905 1248436579411377448650679)
            ·
              refine ⟨1872654869117066172976019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248436579411377448650679 1872654869117066172976019)
              ·
                refine ⟨2808982303675599259464029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872654869117066172976019 2808982303675599259464029)
                ·
                  refine ⟨1053368363878349722299011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2808982303675599259464029 1053368363878349722299011)
                  ·
                    refine ⟨1580052545817524583448517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1053368363878349722299011 1580052545817524583448517)
                    ·
                      refine ⟨296259852340785859396597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1580052545817524583448517 296259852340785859396597)
                      ·
                        rfl

theorem cell23_576964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_576964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576964 prefixEnd_576964 := by exact prefixLift 576964
  have htrace : WordTrace (prefixWord ++ tailWord_576964) baseStart_576964 baseEnd_576964 := by
    simpa [prefixWord, tailWord_576964, baseEnd_576964] using wordTrace_append hprefix tailTrace_576964
  have hstable : (prefixWord ++ tailWord_576964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576964).length < 2 ^ (prefixWord ++ tailWord_576964).sum := by decide
  have hdescent : baseEnd_576964 < baseStart_576964 := by decide
  rcases family_descends (prefixWord ++ tailWord_576964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576967 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_576967 : Nat := 118140960795 + 576967 * 2 ^ 59
def prefixEnd_576967 : Nat := 4983230072969 + 3 ^ 40 * 576967 * 2
def baseEnd_576967 : Nat := 296261392782749347659083

theorem tailTrace_576967 : CollatzResearch.WordTrace tailWord_576967 prefixEnd_576967 296261392782749347659083 := by
  unfold tailWord_576967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21043715300754571963689155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14029143533836381309126103 21043715300754571963689155)
  ·
    refine ⟨31565572951131857945533733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21043715300754571963689155 31565572951131857945533733)
    ·
      refine ⟨5918544928337223364787575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31565572951131857945533733 5918544928337223364787575)
      ·
        refine ⟨8877817392505835047181363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918544928337223364787575 8877817392505835047181363)
        ·
          refine ⟨13316726088758752570772045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8877817392505835047181363 13316726088758752570772045)
          ·
            refine ⟨4993772283284532214039517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13316726088758752570772045 4993772283284532214039517)
            ·
              refine ⟨1872664606231699580264819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4993772283284532214039517 1872664606231699580264819)
              ·
                refine ⟨2808996909347549370397229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1872664606231699580264819 2808996909347549370397229)
                ·
                  refine ⟨1053373841005331013898961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2808996909347549370397229 1053373841005331013898961)
                  ·
                    refine ⟨790030380753998260424221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1053373841005331013898961 790030380753998260424221)
                    ·
                      refine ⟨296261392782749347659083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790030380753998260424221 296261392782749347659083)
                      ·
                        rfl

theorem cell23_576967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_576967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576967 prefixEnd_576967 := by exact prefixLift 576967
  have htrace : WordTrace (prefixWord ++ tailWord_576967) baseStart_576967 baseEnd_576967 := by
    simpa [prefixWord, tailWord_576967, baseEnd_576967] using wordTrace_append hprefix tailTrace_576967
  have hstable : (prefixWord ++ tailWord_576967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576967).length < 2 ^ (prefixWord ++ tailWord_576967).sum := by decide
  have hdescent : baseEnd_576967 < baseStart_576967 := by decide
  rcases family_descends (prefixWord ++ tailWord_576967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576970 : List Nat := [3, 1, 2, 1, 2, 3, 2, 9]
def baseStart_576970 : Nat := 118140960795 + 576970 * 2 ^ 59
def prefixEnd_576970 : Nat := 4983230072969 + 3 ^ 40 * 576970 * 2
def baseEnd_576970 : Nat := 10972701230544919848947

theorem tailTrace_576970 : CollatzResearch.WordTrace tailWord_576970 prefixEnd_576970 10972701230544919848947 := by
  unfold tailWord_576970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260956179935925869012091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14029216479829135650698909 5260956179935925869012091)
  ·
    refine ⟨7891434269903888803518137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5260956179935925869012091 7891434269903888803518137)
    ·
      refine ⟨5918575702427916602638603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7891434269903888803518137 5918575702427916602638603)
      ·
        refine ⟨8877863553641874903957905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918575702427916602638603 8877863553641874903957905)
        ·
          refine ⟨6658397665231406177968429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8877863553641874903957905 6658397665231406177968429)
          ·
            refine ⟨2496899124461777316738161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6658397665231406177968429 2496899124461777316738161)
            ·
              refine ⟨1872674343346332987553621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2496899124461777316738161 1872674343346332987553621)
              ·
                refine ⟨10972701230544919848947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1872674343346332987553621 10972701230544919848947)
                ·
                  rfl

theorem cell23_576970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_576970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_576970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_576970 prefixEnd_576970 := by exact prefixLift 576970
  have htrace : WordTrace (prefixWord ++ tailWord_576970) baseStart_576970 baseEnd_576970 := by
    simpa [prefixWord, tailWord_576970, baseEnd_576970] using wordTrace_append hprefix tailTrace_576970
  have hstable : (prefixWord ++ tailWord_576970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576970).length < 2 ^ (prefixWord ++ tailWord_576970).sum := by decide
  have hdescent : baseEnd_576970 < baseStart_576970 := by decide
  rcases family_descends (prefixWord ++ tailWord_576970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577000 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_577000 : Nat := 118140960795 + 577000 * 2 ^ 59
def prefixEnd_577000 : Nat := 4983230072969 + 3 ^ 40 * 577000 * 2
def baseEnd_577000 : Nat := 98759445881449239515477

theorem tailTrace_577000 : CollatzResearch.WordTrace tailWord_577000 prefixEnd_577000 98759445881449239515477 := by
  unfold tailWord_577000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522459454817509299820227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14029945939756679066426969 10522459454817509299820227)
  ·
    refine ⟨15783689182226263949730341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10522459454817509299820227 15783689182226263949730341)
    ·
      refine ⟨2959441721667424490574439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15783689182226263949730341 2959441721667424490574439)
      ·
        refine ⟨4439162582501136735861659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959441721667424490574439 4439162582501136735861659)
        ·
          refine ⟨6658743873751705103792489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439162582501136735861659 6658743873751705103792489)
          ·
            refine ⟨4994057905313778827844367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6658743873751705103792489 4994057905313778827844367)
            ·
              refine ⟨7491086857970668241766551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4994057905313778827844367 7491086857970668241766551)
              ·
                refine ⟨11236630286956002362649827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7491086857970668241766551 11236630286956002362649827)
                ·
                  refine ⟨16854945430434003543974741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11236630286956002362649827 16854945430434003543974741)
                  ·
                    refine ⟨98759445881449239515477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 16854945430434003543974741 98759445881449239515477)
                    ·
                      rfl

theorem cell23_577000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_577000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577000 prefixEnd_577000 := by exact prefixLift 577000
  have htrace : WordTrace (prefixWord ++ tailWord_577000) baseStart_577000 baseEnd_577000 := by
    simpa [prefixWord, tailWord_577000, baseEnd_577000] using wordTrace_append hprefix tailTrace_577000
  have hstable : (prefixWord ++ tailWord_577000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577000).length < 2 ^ (prefixWord ++ tailWord_577000).sum := by decide
  have hdescent : baseEnd_577000 < baseStart_577000 := by decide
  rcases family_descends (prefixWord ++ tailWord_577000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577014 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_577014 : Nat := 118140960795 + 577014 * 2 ^ 59
def prefixEnd_577014 : Nat := 4983230072969 + 3 ^ 40 * 577014 * 2
def baseEnd_577014 : Nat := 296285526373510663771367

theorem tailTrace_577014 : CollatzResearch.WordTrace tailWord_577014 prefixEnd_577014 296285526373510663771367 := by
  unfold tailWord_577014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315339345724018686915631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14030286354389532660433397 1315339345724018686915631)
  ·
    refine ⟨1973009018586028030373447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315339345724018686915631 1973009018586028030373447)
    ·
      refine ⟨2959513527879042045560171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973009018586028030373447 2959513527879042045560171)
      ·
        refine ⟨4439270291818563068340257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959513527879042045560171 4439270291818563068340257)
        ·
          refine ⟨3329452718863922301255193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4439270291818563068340257 3329452718863922301255193)
          ·
            refine ⟨2497089539147941725941395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3329452718863922301255193 2497089539147941725941395)
            ·
              refine ⟨3745634308721912588912093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2497089539147941725941395 3745634308721912588912093)
              ·
                refine ⟨1404612865770717220842035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745634308721912588912093 1404612865770717220842035)
                ·
                  refine ⟨2106919298656075831263053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1404612865770717220842035 2106919298656075831263053)
                  ·
                    refine ⟨790094736996028436723645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2106919298656075831263053 790094736996028436723645)
                    ·
                      refine ⟨296285526373510663771367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790094736996028436723645 296285526373510663771367)
                      ·
                        rfl

theorem cell23_577014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_577014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577014 prefixEnd_577014 := by exact prefixLift 577014
  have htrace : WordTrace (prefixWord ++ tailWord_577014) baseStart_577014 baseEnd_577014 := by
    simpa [prefixWord, tailWord_577014, baseEnd_577014] using wordTrace_append hprefix tailTrace_577014
  have hstable : (prefixWord ++ tailWord_577014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577014).length < 2 ^ (prefixWord ++ tailWord_577014).sum := by decide
  have hdescent : baseEnd_577014 < baseStart_577014 := by decide
  rcases family_descends (prefixWord ++ tailWord_577014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577048 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_577048 : Nat := 118140960795 + 577048 * 2 ^ 59
def prefixEnd_577048 : Nat := 4983230072969 + 3 ^ 40 * 577048 * 2
def baseEnd_577048 : Nat := 296302984715763530746211

theorem tailTrace_577048 : CollatzResearch.WordTrace tailWord_577048 prefixEnd_577048 296302984715763530746211 := by
  unfold tailWord_577048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10523334806730561398693899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14031113075640748531591865 10523334806730561398693899)
  ·
    refine ⟨15785002210095842098040849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10523334806730561398693899 15785002210095842098040849)
    ·
      refine ⟨11838751657571881573530637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15785002210095842098040849 11838751657571881573530637)
      ·
        refine ⟨4439531871589455590073989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11838751657571881573530637 4439531871589455590073989)
        ·
          refine ⟨832412225923022923138873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4439531871589455590073989 832412225923022923138873)
          ·
            refine ⟨624309169442267192354155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832412225923022923138873 624309169442267192354155)
            ·
              refine ⟨936463754163400788531233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624309169442267192354155 936463754163400788531233)
              ·
                refine ⟨702347815622550591398425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936463754163400788531233 702347815622550591398425)
                ·
                  refine ⟨526760861716912943548819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 702347815622550591398425 526760861716912943548819)
                  ·
                    refine ⟨790141292575369415323229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 526760861716912943548819 790141292575369415323229)
                    ·
                      refine ⟨296302984715763530746211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790141292575369415323229 296302984715763530746211)
                      ·
                        rfl

theorem cell23_577048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_577048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577048 prefixEnd_577048 := by exact prefixLift 577048
  have htrace : WordTrace (prefixWord ++ tailWord_577048) baseStart_577048 baseEnd_577048 := by
    simpa [prefixWord, tailWord_577048, baseEnd_577048] using wordTrace_append hprefix tailTrace_577048
  have hstable : (prefixWord ++ tailWord_577048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577048).length < 2 ^ (prefixWord ++ tailWord_577048).sum := by decide
  have hdescent : baseEnd_577048 < baseStart_577048 := by decide
  rcases family_descends (prefixWord ++ tailWord_577048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577077 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 7]
def baseStart_577077 : Nat := 118140960795 + 577077 * 2 ^ 59
def prefixEnd_577077 : Nat := 4983230072969 + 3 ^ 40 * 577077 * 2
def baseEnd_577077 : Nat := 32924208406082657475953

theorem tailTrace_577077 : CollatzResearch.WordTrace tailWord_577077 prefixEnd_577077 32924208406082657475953 := by
  unfold tailWord_577077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21047727330356060750193485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14031818220237373833462323 21047727330356060750193485)
  ·
    refine ⟨7892897748883522781322557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21047727330356060750193485 7892897748883522781322557)
    ·
      refine ⟨2959836655831321042995959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7892897748883522781322557 2959836655831321042995959)
      ·
        refine ⟨4439754983746981564493939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959836655831321042995959 4439754983746981564493939)
        ·
          refine ⟨6659632475620472346740909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439754983746981564493939 6659632475620472346740909)
          ·
            refine ⟨2497362178357677130027841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6659632475620472346740909 2497362178357677130027841)
            ·
              refine ⟨1873021633768257847520881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497362178357677130027841 1873021633768257847520881)
              ·
                refine ⟨1404766225326193385640661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1873021633768257847520881 1404766225326193385640661)
                ·
                  refine ⟨32924208406082657475953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1404766225326193385640661 32924208406082657475953)
                  ·
                    rfl

theorem cell23_577077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 7].length) (baseStart_577077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577077 prefixEnd_577077 := by exact prefixLift 577077
  have htrace : WordTrace (prefixWord ++ tailWord_577077) baseStart_577077 baseEnd_577077 := by
    simpa [prefixWord, tailWord_577077, baseEnd_577077] using wordTrace_append hprefix tailTrace_577077
  have hstable : (prefixWord ++ tailWord_577077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577077).length < 2 ^ (prefixWord ++ tailWord_577077).sum := by decide
  have hdescent : baseEnd_577077 < baseStart_577077 := by decide
  rcases family_descends (prefixWord ++ tailWord_577077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577111 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 5]
def baseStart_577111 : Nat := 118140960795 + 577111 * 2 ^ 59
def prefixEnd_577111 : Nat := 4983230072969 + 3 ^ 40 * 577111 * 2
def baseEnd_577111 : Nat := 32926148221888531584269

theorem tailTrace_577111 : CollatzResearch.WordTrace tailWord_577111 prefixEnd_577111 32926148221888531584269 := by
  unfold tailWord_577111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21048967412232884556931187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14032644941488589704620791 21048967412232884556931187)
  ·
    refine ⟨31573451118349326835396781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21048967412232884556931187 31573451118349326835396781)
    ·
      refine ⟨11840044169380997563273793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31573451118349326835396781 11840044169380997563273793)
      ·
        refine ⟨8880033127035748172455345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11840044169380997563273793 8880033127035748172455345)
        ·
          refine ⟨6660024845276811129341509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8880033127035748172455345 6660024845276811129341509)
          ·
            refine ⟨1248754658489402086751533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6660024845276811129341509 1248754658489402086751533)
            ·
              refine ⟨468282996933525782531825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1248754658489402086751533 468282996933525782531825)
              ·
                refine ⟨351212247700144336898869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468282996933525782531825 351212247700144336898869)
                ·
                  refine ⟨32926148221888531584269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351212247700144336898869 32926148221888531584269)
                  ·
                    rfl

theorem cell23_577111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 5].length) (baseStart_577111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577111 prefixEnd_577111 := by exact prefixLift 577111
  have htrace : WordTrace (prefixWord ++ tailWord_577111) baseStart_577111 baseEnd_577111 := by
    simpa [prefixWord, tailWord_577111, baseEnd_577111] using wordTrace_append hprefix tailTrace_577111
  have hstable : (prefixWord ++ tailWord_577111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577111).length < 2 ^ (prefixWord ++ tailWord_577111).sum := by decide
  have hdescent : baseEnd_577111 < baseStart_577111 := by decide
  rcases family_descends (prefixWord ++ tailWord_577111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577127 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_577127 : Nat := 118140960795 + 577127 * 2 ^ 59
def prefixEnd_577127 : Nat := 4983230072969 + 3 ^ 40 * 577127 * 2
def baseEnd_577127 : Nat := 296343549687468721658347

theorem tailTrace_577127 : CollatzResearch.WordTrace tailWord_577127 prefixEnd_577127 296343549687468721658347 := by
  unfold tailWord_577127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21049550980174919289513635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14033033986783279526342423 21049550980174919289513635)
  ·
    refine ⟨31574326470262378934270453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21049550980174919289513635 31574326470262378934270453)
    ·
      refine ⟨2960093106587098025087855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31574326470262378934270453 2960093106587098025087855)
      ·
        refine ⟨4440139659880647037631783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2960093106587098025087855 4440139659880647037631783)
        ·
          refine ⟨6660209489820970556447675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4440139659880647037631783 6660209489820970556447675)
          ·
            refine ⟨9990314234731455834671513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6660209489820970556447675 9990314234731455834671513)
            ·
              refine ⟨7492735676048591876003635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9990314234731455834671513 7492735676048591876003635)
              ·
                refine ⟨11239103514072887814005453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7492735676048591876003635 11239103514072887814005453)
                ·
                  refine ⟨4214663817777332930252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11239103514072887814005453 4214663817777332930252045)
                  ·
                    refine ⟨1580498931666499848844517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4214663817777332930252045 1580498931666499848844517)
                    ·
                      refine ⟨296343549687468721658347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1580498931666499848844517 296343549687468721658347)
                      ·
                        rfl

theorem cell23_577127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_577127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577127 prefixEnd_577127 := by exact prefixLift 577127
  have htrace : WordTrace (prefixWord ++ tailWord_577127) baseStart_577127 baseEnd_577127 := by
    simpa [prefixWord, tailWord_577127, baseEnd_577127] using wordTrace_append hprefix tailTrace_577127
  have hstable : (prefixWord ++ tailWord_577127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577127).length < 2 ^ (prefixWord ++ tailWord_577127).sum := by decide
  have hdescent : baseEnd_577127 < baseStart_577127 := by decide
  rcases family_descends (prefixWord ++ tailWord_577127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577141 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_577141 : Nat := 118140960795 + 577141 * 2 ^ 59
def prefixEnd_577141 : Nat := 4983230072969 + 3 ^ 40 * 577141 * 2
def baseEnd_577141 : Nat := 98783579472210555627761

theorem tailTrace_577141 : CollatzResearch.WordTrace tailWord_577141 prefixEnd_577141 98783579472210555627761 := by
  unfold tailWord_577141
  simp only [CollatzResearch.WordTrace]
  refine ⟨21050061602124199680523277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14033374401416133120348851 21050061602124199680523277)
  ·
    refine ⟨7893773100796574880196229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21050061602124199680523277 7893773100796574880196229)
    ·
      refine ⟨1480082456399357790036793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7893773100796574880196229 1480082456399357790036793)
      ·
        refine ⟨1110061842299518342527595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1480082456399357790036793 1110061842299518342527595)
        ·
          refine ⟨1665092763449277513791393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110061842299518342527595 1665092763449277513791393)
          ·
            refine ⟨1248819572586958135343545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1665092763449277513791393 1248819572586958135343545)
            ·
              refine ⟨936614679440218601507659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248819572586958135343545 936614679440218601507659)
              ·
                refine ⟨1404922019160327902261489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936614679440218601507659 1404922019160327902261489)
                ·
                  refine ⟨1053691514370245926696117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1404922019160327902261489 1053691514370245926696117)
                  ·
                    refine ⟨98783579472210555627761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1053691514370245926696117 98783579472210555627761)
                    ·
                      rfl

theorem cell23_577141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_577141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577141 prefixEnd_577141 := by exact prefixLift 577141
  have htrace : WordTrace (prefixWord ++ tailWord_577141) baseStart_577141 baseEnd_577141 := by
    simpa [prefixWord, tailWord_577141, baseEnd_577141] using wordTrace_append hprefix tailTrace_577141
  have hstable : (prefixWord ++ tailWord_577141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577141).length < 2 ^ (prefixWord ++ tailWord_577141).sum := by decide
  have hdescent : baseEnd_577141 < baseStart_577141 := by decide
  rcases family_descends (prefixWord ++ tailWord_577141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577157 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_577157 : Nat := 118140960795 + 577157 * 2 ^ 59
def prefixEnd_577157 : Nat := 4983230072969 + 3 ^ 40 * 577157 * 2
def baseEnd_577157 : Nat := 296358954107103604283209

theorem tailTrace_577157 : CollatzResearch.WordTrace tailWord_577157 prefixEnd_577157 296358954107103604283209 := by
  unfold tailWord_577157
  simp only [CollatzResearch.WordTrace]
  refine ⟨21050645170066234413105725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14033763446710822942070483 21050645170066234413105725)
  ·
    refine ⟨7893991938774837904914647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21050645170066234413105725 7893991938774837904914647)
    ·
      refine ⟨11840987908162256857371971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7893991938774837904914647 11840987908162256857371971)
      ·
        refine ⟨17761481862243385286057957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11840987908162256857371971 17761481862243385286057957)
        ·
          refine ⟨3330277849170634741135867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17761481862243385286057957 3330277849170634741135867)
          ·
            refine ⟨4995416773755952111703801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3330277849170634741135867 4995416773755952111703801)
            ·
              refine ⟨3746562580316964083777851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4995416773755952111703801 3746562580316964083777851)
              ·
                refine ⟨5619843870475446125666777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3746562580316964083777851 5619843870475446125666777)
                ·
                  refine ⟨4214882902856584594250083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5619843870475446125666777 4214882902856584594250083)
                  ·
                    refine ⟨6322324354284876891375125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4214882902856584594250083 6322324354284876891375125)
                    ·
                      refine ⟨296358954107103604283209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6322324354284876891375125 296358954107103604283209)
                      ·
                        rfl

theorem cell23_577157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_577157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577157 prefixEnd_577157 := by exact prefixLift 577157
  have htrace : WordTrace (prefixWord ++ tailWord_577157) baseStart_577157 baseEnd_577157 := by
    simpa [prefixWord, tailWord_577157, baseEnd_577157] using wordTrace_append hprefix tailTrace_577157
  have hstable : (prefixWord ++ tailWord_577157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577157).length < 2 ^ (prefixWord ++ tailWord_577157).sum := by decide
  have hdescent : baseEnd_577157 < baseStart_577157 := by decide
  rcases family_descends (prefixWord ++ tailWord_577157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577164 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_577164 : Nat := 118140960795 + 577164 * 2 ^ 59
def prefixEnd_577164 : Nat := 4983230072969 + 3 ^ 40 * 577164 * 2
def baseEnd_577164 : Nat := 296362548471685076895677

theorem tailTrace_577164 : CollatzResearch.WordTrace tailWord_577164 prefixEnd_577164 296362548471685076895677 := by
  unfold tailWord_577164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525450240520437304305273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14033933654027249739073697 10525450240520437304305273)
  ·
    refine ⟨7894087680390327978228955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10525450240520437304305273 7894087680390327978228955)
    ·
      refine ⟨11841131520585491967343433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7894087680390327978228955 11841131520585491967343433)
      ·
        refine ⟨8880848640439118975507575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11841131520585491967343433 8880848640439118975507575)
        ·
          refine ⟨13321272960658678463261363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8880848640439118975507575 13321272960658678463261363)
          ·
            refine ⟨19981909440988017694892045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13321272960658678463261363 19981909440988017694892045)
            ·
              refine ⟨7493216040370506635584517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19981909440988017694892045 7493216040370506635584517)
              ·
                refine ⟨1404978007569469994172097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7493216040370506635584517 1404978007569469994172097)
                ·
                  refine ⟨1053733505677102495629073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1404978007569469994172097 1053733505677102495629073)
                  ·
                    refine ⟨790300129257826871721805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1053733505677102495629073 790300129257826871721805)
                    ·
                      refine ⟨296362548471685076895677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790300129257826871721805 296362548471685076895677)
                      ·
                        rfl

theorem cell23_577164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_577164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577164 prefixEnd_577164 := by exact prefixLift 577164
  have htrace : WordTrace (prefixWord ++ tailWord_577164) baseStart_577164 baseEnd_577164 := by
    simpa [prefixWord, tailWord_577164, baseEnd_577164] using wordTrace_append hprefix tailTrace_577164
  have hstable : (prefixWord ++ tailWord_577164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577164).length < 2 ^ (prefixWord ++ tailWord_577164).sum := by decide
  have hdescent : baseEnd_577164 < baseStart_577164 := by decide
  rcases family_descends (prefixWord ++ tailWord_577164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577184 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 6]
def baseStart_577184 : Nat := 118140960795 + 577184 * 2 ^ 59
def prefixEnd_577184 : Nat := 4983230072969 + 3 ^ 40 * 577184 * 2
def baseEnd_577184 : Nat := 32930313120530555405065

theorem tailTrace_577184 : CollatzResearch.WordTrace tailWord_577184 prefixEnd_577184 32930313120530555405065 := by
  unfold tailWord_577184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525814970484209012169303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14034419960645612016225737 10525814970484209012169303)
  ·
    refine ⟨15788722455726313518253955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525814970484209012169303 15788722455726313518253955)
    ·
      refine ⟨23683083683589470277380933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15788722455726313518253955 23683083683589470277380933)
      ·
        refine ⟨4440578190673025677008925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23683083683589470277380933 4440578190673025677008925)
        ·
          refine ⟨1665216821502384628878347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4440578190673025677008925 1665216821502384628878347)
          ·
            refine ⟨2497825232253576943317521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665216821502384628878347 2497825232253576943317521)
            ·
              refine ⟨1873368924190182707488141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497825232253576943317521 1873368924190182707488141)
              ·
                refine ⟨702513346571318515308053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873368924190182707488141 702513346571318515308053)
                ·
                  refine ⟨32930313120530555405065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 702513346571318515308053 32930313120530555405065)
                  ·
                    rfl

theorem cell23_577184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_577184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577184 prefixEnd_577184 := by exact prefixLift 577184
  have htrace : WordTrace (prefixWord ++ tailWord_577184) baseStart_577184 baseEnd_577184 := by
    simpa [prefixWord, tailWord_577184, baseEnd_577184] using wordTrace_append hprefix tailTrace_577184
  have hstable : (prefixWord ++ tailWord_577184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577184).length < 2 ^ (prefixWord ++ tailWord_577184).sum := by decide
  have hdescent : baseEnd_577184 < baseStart_577184 := by decide
  rcases family_descends (prefixWord ++ tailWord_577184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577192 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 2, 5]
def baseStart_577192 : Nat := 118140960795 + 577192 * 2 ^ 59
def prefixEnd_577192 : Nat := 4983230072969 + 3 ^ 40 * 577192 * 2
def baseEnd_577192 : Nat := 98792308643336989115183

theorem tailTrace_577192 : CollatzResearch.WordTrace tailWord_577192 prefixEnd_577192 98792308643336989115183 := by
  unfold tailWord_577192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10525960862469717695314915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14034614483292956927086553 10525960862469717695314915)
  ·
    refine ⟨15788941293704576542972373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10525960862469717695314915 15788941293704576542972373)
    ·
      refine ⟨370053311571201012725915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15788941293704576542972373 370053311571201012725915)
      ·
        refine ⟨555079967356801519088873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370053311571201012725915 555079967356801519088873)
        ·
          refine ⟨416309975517601139316655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555079967356801519088873 416309975517601139316655)
          ·
            refine ⟨624464963276401708974983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416309975517601139316655 624464963276401708974983)
            ·
              refine ⟨936697444914602563462475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624464963276401708974983 936697444914602563462475)
              ·
                refine ⟨1405046167371903845193713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936697444914602563462475 1405046167371903845193713)
                ·
                  refine ⟨1053784625528927883895285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1405046167371903845193713 1053784625528927883895285)
                  ·
                    refine ⟨98792308643336989115183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1053784625528927883895285 98792308643336989115183)
                    ·
                      rfl

theorem cell23_577192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_577192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577192 prefixEnd_577192 := by exact prefixLift 577192
  have htrace : WordTrace (prefixWord ++ tailWord_577192) baseStart_577192 baseEnd_577192 := by
    simpa [prefixWord, tailWord_577192, baseEnd_577192] using wordTrace_append hprefix tailTrace_577192
  have hstable : (prefixWord ++ tailWord_577192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577192).length < 2 ^ (prefixWord ++ tailWord_577192).sum := by decide
  have hdescent : baseEnd_577192 < baseStart_577192 := by decide
  rcases family_descends (prefixWord ++ tailWord_577192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577198 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_577198 : Nat := 118140960795 + 577198 * 2 ^ 59
def prefixEnd_577198 : Nat := 4983230072969 + 3 ^ 40 * 577198 * 2
def baseEnd_577198 : Nat := 296380006813937943870521

theorem tailTrace_577198 : CollatzResearch.WordTrace tailWord_577198 prefixEnd_577198 296380006813937943870521 := by
  unfold tailWord_577198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631517570364712301918531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14034760375278465610232165 2631517570364712301918531)
  ·
    refine ⟨3947276355547068452877797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2631517570364712301918531 3947276355547068452877797)
    ·
      refine ⟨740114316665075334914587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3947276355547068452877797 740114316665075334914587)
      ·
        refine ⟨1110171474997613002371881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740114316665075334914587 1110171474997613002371881)
        ·
          refine ⟨832628606248209751778911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110171474997613002371881 832628606248209751778911)
          ·
            refine ⟨1248942909372314627668367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832628606248209751778911 1248942909372314627668367)
            ·
              refine ⟨1873414364058471941502551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248942909372314627668367 1873414364058471941502551)
              ·
                refine ⟨2810121546087707912253827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1873414364058471941502551 2810121546087707912253827)
                ·
                  refine ⟨4215182319131561868380741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2810121546087707912253827 4215182319131561868380741)
                  ·
                    refine ⟨790346684837167850321389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4215182319131561868380741 790346684837167850321389)
                    ·
                      refine ⟨296380006813937943870521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790346684837167850321389 296380006813937943870521)
                      ·
                        rfl

theorem cell23_577198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_577198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577198 prefixEnd_577198 := by exact prefixLift 577198
  have htrace : WordTrace (prefixWord ++ tailWord_577198) baseStart_577198 baseEnd_577198 := by
    simpa [prefixWord, tailWord_577198, baseEnd_577198] using wordTrace_append hprefix tailTrace_577198
  have hstable : (prefixWord ++ tailWord_577198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577198).length < 2 ^ (prefixWord ++ tailWord_577198).sum := by decide
  have hdescent : baseEnd_577198 < baseStart_577198 := by decide
  rcases family_descends (prefixWord ++ tailWord_577198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577205 : List Nat := [1, 3, 3, 3, 2, 1, 2, 3, 1, 4]
def baseStart_577205 : Nat := 118140960795 + 577205 * 2 ^ 59
def prefixEnd_577205 : Nat := 4983230072969 + 3 ^ 40 * 577205 * 2
def baseEnd_577205 : Nat := 98794533726173138827663

theorem tailTrace_577205 : CollatzResearch.WordTrace tailWord_577205 prefixEnd_577205 98794533726173138827663 := by
  unfold tailWord_577205
  simp only [CollatzResearch.WordTrace]
  refine ⟨21052395873892338610853069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14034930582594892407235379 21052395873892338610853069)
  ·
    refine ⟨7894648452709626979069901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21052395873892338610853069 7894648452709626979069901)
    ·
      refine ⟨2960493169766110117151213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7894648452709626979069901 2960493169766110117151213)
      ·
        refine ⟨1110184938662291293931705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2960493169766110117151213 1110184938662291293931705)
        ·
          refine ⟨832638703996718470448779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1110184938662291293931705 832638703996718470448779)
          ·
            refine ⟨1248958055995077705673169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832638703996718470448779 1248958055995077705673169)
            ·
              refine ⟨936718541996308279254877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248958055995077705673169 936718541996308279254877)
              ·
                refine ⟨351269453248615604720579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 936718541996308279254877 351269453248615604720579)
                ·
                  refine ⟨526904179872923407080869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351269453248615604720579 526904179872923407080869)
                  ·
                    refine ⟨98794533726173138827663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526904179872923407080869 98794533726173138827663)
                    ·
                      rfl

theorem cell23_577205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_577205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577205 prefixEnd_577205 := by exact prefixLift 577205
  have htrace : WordTrace (prefixWord ++ tailWord_577205) baseStart_577205 baseEnd_577205 := by
    simpa [prefixWord, tailWord_577205, baseEnd_577205] using wordTrace_append hprefix tailTrace_577205
  have hstable : (prefixWord ++ tailWord_577205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577205).length < 2 ^ (prefixWord ++ tailWord_577205).sum := by decide
  have hdescent : baseEnd_577205 < baseStart_577205 := by decide
  rcases family_descends (prefixWord ++ tailWord_577205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577222 : List Nat := [6, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_577222 : Nat := 118140960795 + 577222 * 2 ^ 59
def prefixEnd_577222 : Nat := 4983230072969 + 3 ^ 40 * 577222 * 2
def baseEnd_577222 : Nat := 98797443449881949990137

theorem tailTrace_577222 : CollatzResearch.WordTrace tailWord_577222 prefixEnd_577222 98797443449881949990137 := by
  unfold tailWord_577222
  simp only [CollatzResearch.WordTrace]
  refine ⟨657906747338460953569435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14035343943220500342814613 657906747338460953569435)
  ·
    refine ⟨986860121007691430354153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 657906747338460953569435 986860121007691430354153)
    ·
      refine ⟨740145090755768572765615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 986860121007691430354153 740145090755768572765615)
      ·
        refine ⟨1110217636133652859148423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740145090755768572765615 1110217636133652859148423)
        ·
          refine ⟨1665326454200479288722635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110217636133652859148423 1665326454200479288722635)
          ·
            refine ⟨2497989681300718933083953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665326454200479288722635 2497989681300718933083953)
            ·
              refine ⟨1873492260975539199812965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497989681300718933083953 1873492260975539199812965)
              ·
                refine ⟨351279798932913599964931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1873492260975539199812965 351279798932913599964931)
                ·
                  refine ⟨526919698399370399947397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351279798932913599964931 526919698399370399947397)
                  ·
                    refine ⟨98797443449881949990137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526919698399370399947397 98797443449881949990137)
                    ·
                      rfl

theorem cell23_577222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_577222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577222 prefixEnd_577222 := by exact prefixLift 577222
  have htrace : WordTrace (prefixWord ++ tailWord_577222) baseStart_577222 baseEnd_577222 := by
    simpa [prefixWord, tailWord_577222, baseEnd_577222] using wordTrace_append hprefix tailTrace_577222
  have hstable : (prefixWord ++ tailWord_577222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577222).length < 2 ^ (prefixWord ++ tailWord_577222).sum := by decide
  have hdescent : baseEnd_577222 < baseStart_577222 := by decide
  rcases family_descends (prefixWord ++ tailWord_577222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577227 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 3, 6]
def baseStart_577227 : Nat := 118140960795 + 577227 * 2 ^ 59
def prefixEnd_577227 : Nat := 4983230072969 + 3 ^ 40 * 577227 * 2
def baseEnd_577227 : Nat := 98798299250972776802629

theorem tailTrace_577227 : CollatzResearch.WordTrace tailWord_577227 prefixEnd_577227 98798299250972776802629 := by
  unfold tailWord_577227
  simp only [CollatzResearch.WordTrace]
  refine ⟨21053198279812636368153935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14035465519875090912102623 21053198279812636368153935)
  ·
    refine ⟨31579797419718954552230903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21053198279812636368153935 31579797419718954552230903)
    ·
      refine ⟨47369696129578431828346355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31579797419718954552230903 47369696129578431828346355)
      ·
        refine ⟨71054544194367647742519533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47369696129578431828346355 71054544194367647742519533)
        ·
          refine ⟨26645454072887867903444825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71054544194367647742519533 26645454072887867903444825)
          ·
            refine ⟨19984090554665900927583619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26645454072887867903444825 19984090554665900927583619)
            ·
              refine ⟨29976135831998851391375429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19984090554665900927583619 29976135831998851391375429)
              ·
                refine ⟨5620525468499784635882893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29976135831998851391375429 5620525468499784635882893)
                ·
                  refine ⟨2107697050687419238456085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5620525468499784635882893 2107697050687419238456085)
                  ·
                    refine ⟨98798299250972776802629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2107697050687419238456085 98798299250972776802629)
                    ·
                      rfl

theorem cell23_577227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 6].length) (baseStart_577227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577227 prefixEnd_577227 := by exact prefixLift 577227
  have htrace : WordTrace (prefixWord ++ tailWord_577227) baseStart_577227 baseEnd_577227 := by
    simpa [prefixWord, tailWord_577227, baseEnd_577227] using wordTrace_append hprefix tailTrace_577227
  have hstable : (prefixWord ++ tailWord_577227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577227).length < 2 ^ (prefixWord ++ tailWord_577227).sum := by decide
  have hdescent : baseEnd_577227 < baseStart_577227 := by decide
  rcases family_descends (prefixWord ++ tailWord_577227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577261 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_577261 : Nat := 118140960795 + 577261 * 2 ^ 59
def prefixEnd_577261 : Nat := 4983230072969 + 3 ^ 40 * 577261 * 2
def baseEnd_577261 : Nat := 98804118698390399127577

theorem tailTrace_577261 : CollatzResearch.WordTrace tailWord_577261 prefixEnd_577261 98804118698390399127577 := by
  unfold tailWord_577261
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054438361689460174891637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14036292241126306783261091 21054438361689460174891637)
  ·
    refine ⟨1973853596408386891396091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21054438361689460174891637 1973853596408386891396091)
    ·
      refine ⟨2960780394612580337094137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973853596408386891396091 2960780394612580337094137)
      ·
        refine ⟨2220585295959435252820603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2960780394612580337094137 2220585295959435252820603)
        ·
          refine ⟨3330877943939152879230905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220585295959435252820603 3330877943939152879230905)
          ·
            refine ⟨2498158457954364659423179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3330877943939152879230905 2498158457954364659423179)
            ·
              refine ⟨3747237686931546989134769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498158457954364659423179 3747237686931546989134769)
              ·
                refine ⟨2810428265198660241851077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3747237686931546989134769 2810428265198660241851077)
                ·
                  refine ⟨526955299724748795347077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2810428265198660241851077 526955299724748795347077)
                  ·
                    refine ⟨98804118698390399127577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 526955299724748795347077 98804118698390399127577)
                    ·
                      rfl

theorem cell23_577261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_577261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577261 prefixEnd_577261 := by exact prefixLift 577261
  have htrace : WordTrace (prefixWord ++ tailWord_577261) baseStart_577261 baseEnd_577261 := by
    simpa [prefixWord, tailWord_577261, baseEnd_577261] using wordTrace_append hprefix tailTrace_577261
  have hstable : (prefixWord ++ tailWord_577261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577261).length < 2 ^ (prefixWord ++ tailWord_577261).sum := by decide
  have hdescent : baseEnd_577261 < baseStart_577261 := by decide
  rcases family_descends (prefixWord ++ tailWord_577261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577271 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_577271 : Nat := 118140960795 + 577271 * 2 ^ 59
def prefixEnd_577271 : Nat := 4983230072969 + 3 ^ 40 * 577271 * 2
def baseEnd_577271 : Nat := 296417490901716158257685

theorem tailTrace_577271 : CollatzResearch.WordTrace tailWord_577271 prefixEnd_577271 296417490901716158257685 := by
  unfold tailWord_577271
  simp only [CollatzResearch.WordTrace]
  refine ⟨21054803091653231882755667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14036535394435487921837111 21054803091653231882755667)
  ·
    refine ⟨31582204637479847824133501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21054803091653231882755667 31582204637479847824133501)
    ·
      refine ⟨11843326739054942934050063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31582204637479847824133501 11843326739054942934050063)
      ·
        refine ⟨17764990108582414401075095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11843326739054942934050063 17764990108582414401075095)
        ·
          refine ⟨26647485162873621601612643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17764990108582414401075095 26647485162873621601612643)
          ·
            refine ⟨39971227744310432402418965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26647485162873621601612643 39971227744310432402418965)
            ·
              refine ⟨1873651300514551518863389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39971227744310432402418965 1873651300514551518863389)
              ·
                refine ⟨702619237692956819573771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873651300514551518863389 702619237692956819573771)
                ·
                  refine ⟨1053928856539435229360657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702619237692956819573771 1053928856539435229360657)
                  ·
                    refine ⟨790446642404576422020493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1053928856539435229360657 790446642404576422020493)
                    ·
                      refine ⟨296417490901716158257685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790446642404576422020493 296417490901716158257685)
                      ·
                        rfl

theorem cell23_577271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_577271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577271 prefixEnd_577271 := by exact prefixLift 577271
  have htrace : WordTrace (prefixWord ++ tailWord_577271) baseStart_577271 baseEnd_577271 := by
    simpa [prefixWord, tailWord_577271, baseEnd_577271] using wordTrace_append hprefix tailTrace_577271
  have hstable : (prefixWord ++ tailWord_577271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577271).length < 2 ^ (prefixWord ++ tailWord_577271).sum := by decide
  have hdescent : baseEnd_577271 < baseStart_577271 := by decide
  rcases family_descends (prefixWord ++ tailWord_577271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577286 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_577286 : Nat := 118140960795 + 577286 * 2 ^ 59
def prefixEnd_577286 : Nat := 4983230072969 + 3 ^ 40 * 577286 * 2
def baseEnd_577286 : Nat := 32936132567948177730013

theorem tailTrace_577286 : CollatzResearch.WordTrace tailWord_577286 prefixEnd_577286 32936132567948177730013 := by
  unfold tailWord_577286
  simp only [CollatzResearch.WordTrace]
  refine ⟨657979693331215295142241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14036900124399259629701141 657979693331215295142241)
  ·
    refine ⟨493484769998411471356681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 657979693331215295142241 493484769998411471356681)
    ·
      refine ⟨370113577498808603517511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 493484769998411471356681 370113577498808603517511)
      ·
        refine ⟨555170366248212905276267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370113577498808603517511 555170366248212905276267)
        ·
          refine ⟨832755549372319357914401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555170366248212905276267 832755549372319357914401)
          ·
            refine ⟨624566662029239518435801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832755549372319357914401 624566662029239518435801)
            ·
              refine ⟨468424996521929638826851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624566662029239518435801 468424996521929638826851)
              ·
                refine ⟨702637494782894458240277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468424996521929638826851 702637494782894458240277)
                ·
                  refine ⟨32936132567948177730013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 702637494782894458240277 32936132567948177730013)
                  ·
                    rfl

theorem cell23_577286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_577286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577286 prefixEnd_577286 := by exact prefixLift 577286
  have htrace : WordTrace (prefixWord ++ tailWord_577286) baseStart_577286 baseEnd_577286 := by
    simpa [prefixWord, tailWord_577286, baseEnd_577286] using wordTrace_append hprefix tailTrace_577286
  have hstable : (prefixWord ++ tailWord_577286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577286).length < 2 ^ (prefixWord ++ tailWord_577286).sum := by decide
  have hdescent : baseEnd_577286 < baseStart_577286 := by decide
  rcases family_descends (prefixWord ++ tailWord_577286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577341 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_577341 : Nat := 118140960795 + 577341 * 2 ^ 59
def prefixEnd_577341 : Nat := 4983230072969 + 3 ^ 40 * 577341 * 2
def baseEnd_577341 : Nat := 296453434547530884382363

theorem tailTrace_577341 : CollatzResearch.WordTrace tailWord_577341 prefixEnd_577341 296453434547530884382363 := by
  unfold tailWord_577341
  simp only [CollatzResearch.WordTrace]
  refine ⟨21057356201399633837803877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14038237467599755891869251 21057356201399633837803877)
  ·
    refine ⟨3948254287762431344588227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21057356201399633837803877 3948254287762431344588227)
    ·
      refine ⟨5922381431643647016882341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948254287762431344588227 5922381431643647016882341)
      ·
        refine ⟨1110446518433183815665439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5922381431643647016882341 1110446518433183815665439)
        ·
          refine ⟨1665669777649775723498159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110446518433183815665439 1665669777649775723498159)
          ·
            refine ⟨2498504666474663585247239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1665669777649775723498159 2498504666474663585247239)
            ·
              refine ⟨3747756999711995377870859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2498504666474663585247239 3747756999711995377870859)
              ·
                refine ⟨5621635499567993066806289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3747756999711995377870859 5621635499567993066806289)
                ·
                  refine ⟨4216226624675994800104717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5621635499567993066806289 4216226624675994800104717)
                  ·
                    refine ⟨1581084984253498050039269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4216226624675994800104717 1581084984253498050039269)
                    ·
                      refine ⟨296453434547530884382363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1581084984253498050039269 296453434547530884382363)
                      ·
                        rfl

theorem cell23_577341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_577341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577341 prefixEnd_577341 := by exact prefixLift 577341
  have htrace : WordTrace (prefixWord ++ tailWord_577341) baseStart_577341 baseEnd_577341 := by
    simpa [prefixWord, tailWord_577341, baseEnd_577341] using wordTrace_append hprefix tailTrace_577341
  have hstable : (prefixWord ++ tailWord_577341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577341).length < 2 ^ (prefixWord ++ tailWord_577341).sum := by decide
  have hdescent : baseEnd_577341 < baseStart_577341 := by decide
  rcases family_descends (prefixWord ++ tailWord_577341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577358 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_577358 : Nat := 118140960795 + 577358 * 2 ^ 59
def prefixEnd_577358 : Nat := 4983230072969 + 3 ^ 40 * 577358 * 2
def baseEnd_577358 : Nat := 296462163718657317869785

theorem tailTrace_577358 : CollatzResearch.WordTrace tailWord_577358 prefixEnd_577358 296462163718657317869785 := by
  unfold tailWord_577358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632247030292255717646591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14038650828225363827448485 2632247030292255717646591)
  ·
    refine ⟨3948370545438383576469887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2632247030292255717646591 3948370545438383576469887)
    ·
      refine ⟨5922555818157575364704831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3948370545438383576469887 5922555818157575364704831)
      ·
        refine ⟨8883833727236363047057247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5922555818157575364704831 8883833727236363047057247)
        ·
          refine ⟨13325750590854544570585871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8883833727236363047057247 13325750590854544570585871)
          ·
            refine ⟨19988625886281816855878807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13325750590854544570585871 19988625886281816855878807)
            ·
              refine ⟨29982938829422725283818211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19988625886281816855878807 29982938829422725283818211)
              ·
                refine ⟨44974408244134087925727317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29982938829422725283818211 44974408244134087925727317)
                ·
                  refine ⟨527043846610946342879617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 44974408244134087925727317 527043846610946342879617)
                  ·
                    refine ⟨395282884958209757159713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527043846610946342879617 395282884958209757159713)
                    ·
                      refine ⟨296462163718657317869785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395282884958209757159713 296462163718657317869785)
                      ·
                        rfl

theorem cell23_577358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_577358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577358 prefixEnd_577358 := by exact prefixLift 577358
  have htrace : WordTrace (prefixWord ++ tailWord_577358) baseStart_577358 baseEnd_577358 := by
    simpa [prefixWord, tailWord_577358, baseEnd_577358] using wordTrace_append hprefix tailTrace_577358
  have hstable : (prefixWord ++ tailWord_577358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577358).length < 2 ^ (prefixWord ++ tailWord_577358).sum := by decide
  have hdescent : baseEnd_577358 < baseStart_577358 := by decide
  rcases family_descends (prefixWord ++ tailWord_577358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577379 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 1, 3, 2]
def baseStart_577379 : Nat := 118140960795 + 577379 * 2 ^ 59
def prefixEnd_577379 : Nat := 4983230072969 + 3 ^ 40 * 577379 * 2
def baseEnd_577379 : Nat := 296472946812401735707189

theorem tailTrace_577379 : CollatzResearch.WordTrace tailWord_577379 prefixEnd_577379 296472946812401735707189 := by
  unfold tailWord_577379
  simp only [CollatzResearch.WordTrace]
  refine ⟨21058742175261966327687191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14039161450174644218458127 21058742175261966327687191)
  ·
    refine ⟨31588113262892949491530787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21058742175261966327687191 31588113262892949491530787)
    ·
      refine ⟨47382169894339424237296181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31588113262892949491530787 47382169894339424237296181)
      ·
        refine ⟨4442078427594321022246517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47382169894339424237296181 4442078427594321022246517)
        ·
          refine ⟨416444852586967595835611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4442078427594321022246517 416444852586967595835611)
          ·
            refine ⟨624667278880451393753417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416444852586967595835611 624667278880451393753417)
            ·
              refine ⟨468500459160338545315063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624667278880451393753417 468500459160338545315063)
              ·
                refine ⟨702750688740507817972595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468500459160338545315063 702750688740507817972595)
                ·
                  refine ⟨1054126033110761726958893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702750688740507817972595 1054126033110761726958893)
                  ·
                    refine ⟨395297262416535647609585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1054126033110761726958893 395297262416535647609585)
                    ·
                      refine ⟨296472946812401735707189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395297262416535647609585 296472946812401735707189)
                      ·
                        rfl

theorem cell23_577379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_577379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577379 prefixEnd_577379 := by exact prefixLift 577379
  have htrace : WordTrace (prefixWord ++ tailWord_577379) baseStart_577379 baseEnd_577379 := by
    simpa [prefixWord, tailWord_577379, baseEnd_577379] using wordTrace_append hprefix tailTrace_577379
  have hstable : (prefixWord ++ tailWord_577379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577379).length < 2 ^ (prefixWord ++ tailWord_577379).sum := by decide
  have hdescent : baseEnd_577379 < baseStart_577379 := by decide
  rcases family_descends (prefixWord ++ tailWord_577379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577409 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_577409 : Nat := 118140960795 + 577409 * 2 ^ 59
def prefixEnd_577409 : Nat := 4983230072969 + 3 ^ 40 * 577409 * 2
def baseEnd_577409 : Nat := 296488351232036618332051

theorem tailTrace_577409 : CollatzResearch.WordTrace tailWord_577409 prefixEnd_577409 296488351232036618332051 := by
  unfold tailWord_577409
  simp only [CollatzResearch.WordTrace]
  refine ⟨21059836365153281451279281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14039890910102187634186187 21059836365153281451279281)
  ·
    refine ⟨15794877273864961088459461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21059836365153281451279281 15794877273864961088459461)
    ·
      refine ⟨2961539488849680204086149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15794877273864961088459461 2961539488849680204086149)
      ·
        refine ⟨555288654159315038266153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2961539488849680204086149 555288654159315038266153)
        ·
          refine ⟨416466490619486278699615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555288654159315038266153 416466490619486278699615)
          ·
            refine ⟨624699735929229418049423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416466490619486278699615 624699735929229418049423)
            ·
              refine ⟨937049603893844127074135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624699735929229418049423 937049603893844127074135)
              ·
                refine ⟨1405574405840766190611203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937049603893844127074135 1405574405840766190611203)
                ·
                  refine ⟨2108361608761149285916805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405574405840766190611203 2108361608761149285916805)
                  ·
                    refine ⟨395317801642715491109401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2108361608761149285916805 395317801642715491109401)
                    ·
                      refine ⟨296488351232036618332051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395317801642715491109401 296488351232036618332051)
                      ·
                        rfl

theorem cell23_577409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_577409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577409 prefixEnd_577409 := by exact prefixLift 577409
  have htrace : WordTrace (prefixWord ++ tailWord_577409) baseStart_577409 baseEnd_577409 := by
    simpa [prefixWord, tailWord_577409, baseEnd_577409] using wordTrace_append hprefix tailTrace_577409
  have hstable : (prefixWord ++ tailWord_577409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577409).length < 2 ^ (prefixWord ++ tailWord_577409).sum := by decide
  have hdescent : baseEnd_577409 < baseStart_577409 := by decide
  rcases family_descends (prefixWord ++ tailWord_577409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577431 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_577431 : Nat := 118140960795 + 577431 * 2 ^ 59
def prefixEnd_577431 : Nat := 4983230072969 + 3 ^ 40 * 577431 * 2
def baseEnd_577431 : Nat := 296499647806435532256949

theorem tailTrace_577431 : CollatzResearch.WordTrace tailWord_577431 prefixEnd_577431 296499647806435532256949 := by
  unfold tailWord_577431
  simp only [CollatzResearch.WordTrace]
  refine ⟨21060638771073579208580147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14040425847382386139053431 21060638771073579208580147)
  ·
    refine ⟨31590958156610368812870221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21060638771073579208580147 31590958156610368812870221)
    ·
      refine ⟨11846609308728888304826333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31590958156610368812870221 11846609308728888304826333)
      ·
        refine ⟨4442478490773333114309875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11846609308728888304826333 4442478490773333114309875)
        ·
          refine ⟨6663717736159999671464813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4442478490773333114309875 6663717736159999671464813)
          ·
            refine ⟨2498894151059999876799305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6663717736159999671464813 2498894151059999876799305)
            ·
              refine ⟨1874170613294999907599479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2498894151059999876799305 1874170613294999907599479)
              ·
                refine ⟨2811255919942499861399219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874170613294999907599479 2811255919942499861399219)
                ·
                  refine ⟨4216883879913749792098829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2811255919942499861399219 4216883879913749792098829)
                  ·
                    refine ⟨1581331454967656172037061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4216883879913749792098829 1581331454967656172037061)
                    ·
                      refine ⟨296499647806435532256949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1581331454967656172037061 296499647806435532256949)
                      ·
                        rfl

theorem cell23_577431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_577431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577431 prefixEnd_577431 := by exact prefixLift 577431
  have htrace : WordTrace (prefixWord ++ tailWord_577431) baseStart_577431 baseEnd_577431 := by
    simpa [prefixWord, tailWord_577431, baseEnd_577431] using wordTrace_append hprefix tailTrace_577431
  have hstable : (prefixWord ++ tailWord_577431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577431).length < 2 ^ (prefixWord ++ tailWord_577431).sum := by decide
  have hdescent : baseEnd_577431 < baseStart_577431 := by decide
  rcases family_descends (prefixWord ++ tailWord_577431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577432 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 5]
def baseStart_577432 : Nat := 118140960795 + 577432 * 2 ^ 59
def prefixEnd_577432 : Nat := 4983230072969 + 3 ^ 40 * 577432 * 2
def baseEnd_577432 : Nat := 32944462365232225371605

theorem tailTrace_577432 : CollatzResearch.WordTrace tailWord_577432 prefixEnd_577432 32944462365232225371605 := by
  unfold tailWord_577432
  simp only [CollatzResearch.WordTrace]
  refine ⟨10530337622034978189683275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14040450162713304252911033 10530337622034978189683275)
  ·
    refine ⟨15795506433052467284524913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10530337622034978189683275 15795506433052467284524913)
    ·
      refine ⟨11846629824789350463393685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15795506433052467284524913 11846629824789350463393685)
      ·
        refine ⟨555310773037000802971579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11846629824789350463393685 555310773037000802971579)
        ·
          refine ⟨832966159555501204457369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555310773037000802971579 832966159555501204457369)
          ·
            refine ⟨624724619666625903343027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832966159555501204457369 624724619666625903343027)
            ·
              refine ⟨937086929499938855014541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624724619666625903343027 937086929499938855014541)
              ·
                refine ⟨351407598562477070630453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937086929499938855014541 351407598562477070630453)
                ·
                  refine ⟨32944462365232225371605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351407598562477070630453 32944462365232225371605)
                  ·
                    rfl

theorem cell23_577432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 5].length) (baseStart_577432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577432 prefixEnd_577432 := by exact prefixLift 577432
  have htrace : WordTrace (prefixWord ++ tailWord_577432) baseStart_577432 baseEnd_577432 := by
    simpa [prefixWord, tailWord_577432, baseEnd_577432] using wordTrace_append hprefix tailTrace_577432
  have hstable : (prefixWord ++ tailWord_577432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577432).length < 2 ^ (prefixWord ++ tailWord_577432).sum := by decide
  have hdescent : baseEnd_577432 < baseStart_577432 := by decide
  rcases family_descends (prefixWord ++ tailWord_577432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577471 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 6]
def baseStart_577471 : Nat := 118140960795 + 577471 * 2 ^ 59
def prefixEnd_577471 : Nat := 4983230072969 + 3 ^ 40 * 577471 * 2
def baseEnd_577471 : Nat := 32946687448068375084085

theorem tailTrace_577471 : CollatzResearch.WordTrace tailWord_577471 prefixEnd_577471 32946687448068375084085 := by
  unfold tailWord_577471
  simp only [CollatzResearch.WordTrace]
  refine ⟨21062097690928666040036267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14041398460619110693357511 21062097690928666040036267)
  ·
    refine ⟨31593146536392999060054401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21062097690928666040036267 31593146536392999060054401)
    ·
      refine ⟨23694859902294749295040801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31593146536392999060054401 23694859902294749295040801)
      ·
        refine ⟨17771144926721061971280601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23694859902294749295040801 17771144926721061971280601)
        ·
          refine ⟨13328358695040796478460451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17771144926721061971280601 13328358695040796478460451)
          ·
            refine ⟨19992538042561194717690677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13328358695040796478460451 19992538042561194717690677)
            ·
              refine ⟨1874300441490112004783501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19992538042561194717690677 1874300441490112004783501)
              ·
                refine ⟨702862665558792001793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1874300441490112004783501 702862665558792001793813)
                ·
                  refine ⟨32946687448068375084085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 702862665558792001793813 32946687448068375084085)
                  ·
                    rfl

theorem cell23_577471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 6].length) (baseStart_577471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577471 prefixEnd_577471 := by exact prefixLift 577471
  have htrace : WordTrace (prefixWord ++ tailWord_577471) baseStart_577471 baseEnd_577471 := by
    simpa [prefixWord, tailWord_577471, baseEnd_577471] using wordTrace_append hprefix tailTrace_577471
  have hstable : (prefixWord ++ tailWord_577471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577471).length < 2 ^ (prefixWord ++ tailWord_577471).sum := by decide
  have hdescent : baseEnd_577471 < baseStart_577471 := by decide
  rcases family_descends (prefixWord ++ tailWord_577471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577518 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_577518 : Nat := 118140960795 + 577518 * 2 ^ 59
def prefixEnd_577518 : Nat := 4983230072969 + 3 ^ 40 * 577518 * 2
def baseEnd_577518 : Nat := 98848106874458897289683

theorem tailTrace_577518 : CollatzResearch.WordTrace tailWord_577518 prefixEnd_577518 98848106874458897289683 := by
  unfold tailWord_577518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2632976490219799133374651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14042541281172262044664805 2632976490219799133374651)
  ·
    refine ⟨3949464735329698700061977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2632976490219799133374651 3949464735329698700061977)
    ·
      refine ⟨2962098551497274025046483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3949464735329698700061977 2962098551497274025046483)
      ·
        refine ⟨4443147827245911037569725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2962098551497274025046483 4443147827245911037569725)
        ·
          refine ⟨1666180435217216639088647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4443147827245911037569725 1666180435217216639088647)
          ·
            refine ⟨2499270652825824958632971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666180435217216639088647 2499270652825824958632971)
            ·
              refine ⟨3748905979238737437949457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499270652825824958632971 3748905979238737437949457)
              ·
                refine ⟨2811679484429053078462093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3748905979238737437949457 2811679484429053078462093)
                ·
                  refine ⟨1054379806660894904423285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2811679484429053078462093 1054379806660894904423285)
                  ·
                    refine ⟨98848106874458897289683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1054379806660894904423285 98848106874458897289683)
                    ·
                      rfl

theorem cell23_577518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_577518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577518 prefixEnd_577518 := by exact prefixLift 577518
  have htrace : WordTrace (prefixWord ++ tailWord_577518) baseStart_577518 baseEnd_577518 := by
    simpa [prefixWord, tailWord_577518, baseEnd_577518] using wordTrace_append hprefix tailTrace_577518
  have hstable : (prefixWord ++ tailWord_577518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577518).length < 2 ^ (prefixWord ++ tailWord_577518).sum := by decide
  have hdescent : baseEnd_577518 < baseStart_577518 := by decide
  rcases family_descends (prefixWord ++ tailWord_577518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577531 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 1, 6]
def baseStart_577531 : Nat := 118140960795 + 577531 * 2 ^ 59
def prefixEnd_577531 : Nat := 4983230072969 + 3 ^ 40 * 577531 * 2
def baseEnd_577531 : Nat := 98850331957295047002163

theorem tailTrace_577531 : CollatzResearch.WordTrace tailWord_577531 prefixEnd_577531 98850331957295047002163 := by
  unfold tailWord_577531
  simp only [CollatzResearch.WordTrace]
  refine ⟨21064286070711296287220447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14042857380474197524813631 21064286070711296287220447)
  ·
    refine ⟨31596429106066944430830671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21064286070711296287220447 31596429106066944430830671)
    ·
      refine ⟨47394643659100416646246007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31596429106066944430830671 47394643659100416646246007)
      ·
        refine ⟨71091965488650624969369011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47394643659100416646246007 71091965488650624969369011)
        ·
          refine ⟨106637948232975937454053517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71091965488650624969369011 106637948232975937454053517)
          ·
            refine ⟨39989230587365976545270069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106637948232975937454053517 39989230587365976545270069)
            ·
              refine ⟨3748990367565560301119069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39989230587365976545270069 3748990367565560301119069)
              ·
                refine ⟨1405871387837085112919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3748990367565560301119069 1405871387837085112919651)
                ·
                  refine ⟨2108807081755627669379477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1405871387837085112919651 2108807081755627669379477)
                  ·
                    refine ⟨98850331957295047002163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2108807081755627669379477 98850331957295047002163)
                    ·
                      rfl

theorem cell23_577531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 6].length) (baseStart_577531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577531 prefixEnd_577531 := by exact prefixLift 577531
  have htrace : WordTrace (prefixWord ++ tailWord_577531) baseStart_577531 baseEnd_577531 := by
    simpa [prefixWord, tailWord_577531, baseEnd_577531] using wordTrace_append hprefix tailTrace_577531
  have hstable : (prefixWord ++ tailWord_577531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577531).length < 2 ^ (prefixWord ++ tailWord_577531).sum := by decide
  have hdescent : baseEnd_577531 < baseStart_577531 := by decide
  rcases family_descends (prefixWord ++ tailWord_577531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577548 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_577548 : Nat := 118140960795 + 577548 * 2 ^ 59
def prefixEnd_577548 : Nat := 4983230072969 + 3 ^ 40 * 577548 * 2
def baseEnd_577548 : Nat := 98853241681003858164637

theorem tailTrace_577548 : CollatzResearch.WordTrace tailWord_577548 prefixEnd_577548 98853241681003858164637 := by
  unfold tailWord_577548
  simp only [CollatzResearch.WordTrace]
  refine ⟨10532453055824854095294649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14043270741099805460392865 10532453055824854095294649)
  ·
    refine ⟨7899339791868640571470987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10532453055824854095294649 7899339791868640571470987)
    ·
      refine ⟨11849009687802960857206481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7899339791868640571470987 11849009687802960857206481)
      ·
        refine ⟨8886757265852220642904861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11849009687802960857206481 8886757265852220642904861)
        ·
          refine ⟨3332533974694582741089323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8886757265852220642904861 3332533974694582741089323)
          ·
            refine ⟨4998800962041874111633985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3332533974694582741089323 4998800962041874111633985)
            ·
              refine ⟨3749100721531405583725489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4998800962041874111633985 3749100721531405583725489)
              ·
                refine ⟨2811825541148554187794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3749100721531405583725489 2811825541148554187794117)
                ·
                  refine ⟨527217288965353910211397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2811825541148554187794117 527217288965353910211397)
                  ·
                    refine ⟨98853241681003858164637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 527217288965353910211397 98853241681003858164637)
                    ·
                      rfl

theorem cell23_577548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_577548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577548 prefixEnd_577548 := by exact prefixLift 577548
  have htrace : WordTrace (prefixWord ++ tailWord_577548) baseStart_577548 baseEnd_577548 := by
    simpa [prefixWord, tailWord_577548, baseEnd_577548] using wordTrace_append hprefix tailTrace_577548
  have hstable : (prefixWord ++ tailWord_577548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577548).length < 2 ^ (prefixWord ++ tailWord_577548).sum := by decide
  have hdescent : baseEnd_577548 < baseStart_577548 := by decide
  rcases family_descends (prefixWord ++ tailWord_577548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577555 : List Nat := [1, 1, 1, 2, 1, 4, 6, 1, 1, 1, 4]
def baseStart_577555 : Nat := 118140960795 + 577555 * 2 ^ 59
def prefixEnd_577555 : Nat := 4983230072969 + 3 ^ 40 * 577555 * 2
def baseEnd_577555 : Nat := 296563319407593047106379

theorem tailTrace_577555 : CollatzResearch.WordTrace tailWord_577555 prefixEnd_577555 296563319407593047106379 := by
  unfold tailWord_577555
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065161422624348386094119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14043440948416232257396079 21065161422624348386094119)
  ·
    refine ⟨31597742133936522579141179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21065161422624348386094119 31597742133936522579141179)
    ·
      refine ⟨47396613200904783868711769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31597742133936522579141179 47396613200904783868711769)
      ·
        refine ⟨35547459900678587901533827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47396613200904783868711769 35547459900678587901533827)
        ·
          refine ⟨53321189851017881852300741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35547459900678587901533827 53321189851017881852300741)
          ·
            refine ⟨9997723097065852847306389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53321189851017881852300741 9997723097065852847306389)
            ·
              refine ⟨468643270174961852217487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9997723097065852847306389 468643270174961852217487)
              ·
                refine ⟨702964905262442778326231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468643270174961852217487 702964905262442778326231)
                ·
                  refine ⟨1054447357893664167489347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 702964905262442778326231 1054447357893664167489347)
                  ·
                    refine ⟨1581671036840496251234021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1054447357893664167489347 1581671036840496251234021)
                    ·
                      refine ⟨296563319407593047106379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1581671036840496251234021 296563319407593047106379)
                      ·
                        rfl

theorem cell23_577555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 1, 1, 4].length) (baseStart_577555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577555 prefixEnd_577555 := by exact prefixLift 577555
  have htrace : WordTrace (prefixWord ++ tailWord_577555) baseStart_577555 baseEnd_577555 := by
    simpa [prefixWord, tailWord_577555, baseEnd_577555] using wordTrace_append hprefix tailTrace_577555
  have hstable : (prefixWord ++ tailWord_577555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577555).length < 2 ^ (prefixWord ++ tailWord_577555).sum := by decide
  have hdescent : baseEnd_577555 < baseStart_577555 := by decide
  rcases family_descends (prefixWord ++ tailWord_577555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577565 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 4, 4]
def baseStart_577565 : Nat := 118140960795 + 577565 * 2 ^ 59
def prefixEnd_577565 : Nat := 4983230072969 + 3 ^ 40 * 577565 * 2
def baseEnd_577565 : Nat := 98856151404712669327111

theorem tailTrace_577565 : CollatzResearch.WordTrace tailWord_577565 prefixEnd_577565 98856151404712669327111 := by
  unfold tailWord_577565
  simp only [CollatzResearch.WordTrace]
  refine ⟨21065526152588120093958149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14043684101725413395972099 21065526152588120093958149)
  ·
    refine ⟨3949786153610272517617153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21065526152588120093958149 3949786153610272517617153)
    ·
      refine ⟨2962339615207704388212865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3949786153610272517617153 2962339615207704388212865)
      ·
        refine ⟨2221754711405778291159649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2962339615207704388212865 2221754711405778291159649)
        ·
          refine ⟨1666316033554333718369737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2221754711405778291159649 1666316033554333718369737)
          ·
            refine ⟨1249737025165750288777303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1666316033554333718369737 1249737025165750288777303)
            ·
              refine ⟨1874605537748625433165955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1249737025165750288777303 1874605537748625433165955)
              ·
                refine ⟨2811908306622938149748933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1874605537748625433165955 2811908306622938149748933)
                ·
                  refine ⟨527232807491800903077925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2811908306622938149748933 527232807491800903077925)
                  ·
                    refine ⟨98856151404712669327111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 527232807491800903077925 98856151404712669327111)
                    ·
                      rfl

theorem cell23_577565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_577565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577565 prefixEnd_577565 := by exact prefixLift 577565
  have htrace : WordTrace (prefixWord ++ tailWord_577565) baseStart_577565 baseEnd_577565 := by
    simpa [prefixWord, tailWord_577565, baseEnd_577565] using wordTrace_append hprefix tailTrace_577565
  have hstable : (prefixWord ++ tailWord_577565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577565).length < 2 ^ (prefixWord ++ tailWord_577565).sum := by decide
  have hdescent : baseEnd_577565 < baseStart_577565 := by decide
  rcases family_descends (prefixWord ++ tailWord_577565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577585 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 4]
def baseStart_577585 : Nat := 118140960795 + 577585 * 2 ^ 59
def prefixEnd_577585 : Nat := 4983230072969 + 3 ^ 40 * 577585 * 2
def baseEnd_577585 : Nat := 296578723827227929731241

theorem tailTrace_577585 : CollatzResearch.WordTrace tailWord_577585 prefixEnd_577585 296578723827227929731241 := by
  unfold tailWord_577585
  simp only [CollatzResearch.WordTrace]
  refine ⟨21066255612515663509686209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14044170408343775673124139 21066255612515663509686209)
  ·
    refine ⟨15799691709386747632264657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21066255612515663509686209 15799691709386747632264657)
    ·
      refine ⟨11849768782040060724198493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15799691709386747632264657 11849768782040060724198493)
      ·
        refine ⟨4443663293265022771574435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11849768782040060724198493 4443663293265022771574435)
        ·
          refine ⟨6665494939897534157361653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4443663293265022771574435 6665494939897534157361653)
          ·
            refine ⟨624890150615393827252655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6665494939897534157361653 624890150615393827252655)
            ·
              refine ⟨937335225923090740878983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624890150615393827252655 937335225923090740878983)
              ·
                refine ⟨1406002838884636111318475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937335225923090740878983 1406002838884636111318475)
                ·
                  refine ⟨2109004258326954166977713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406002838884636111318475 2109004258326954166977713)
                  ·
                    refine ⟨1581753193745215625233285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109004258326954166977713 1581753193745215625233285)
                    ·
                      refine ⟨296578723827227929731241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1581753193745215625233285 296578723827227929731241)
                      ·
                        rfl

theorem cell23_577585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_577585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577585 prefixEnd_577585 := by exact prefixLift 577585
  have htrace : WordTrace (prefixWord ++ tailWord_577585) baseStart_577585 baseEnd_577585 := by
    simpa [prefixWord, tailWord_577585, baseEnd_577585] using wordTrace_append hprefix tailTrace_577585
  have hstable : (prefixWord ++ tailWord_577585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577585).length < 2 ^ (prefixWord ++ tailWord_577585).sum := by decide
  have hdescent : baseEnd_577585 < baseStart_577585 := by decide
  rcases family_descends (prefixWord ++ tailWord_577585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577591 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 2, 7]
def baseStart_577591 : Nat := 118140960795 + 577591 * 2 ^ 59
def prefixEnd_577591 : Nat := 4983230072969 + 3 ^ 40 * 577591 * 2
def baseEnd_577591 : Nat := 98860601570384968752071

theorem tailTrace_577591 : CollatzResearch.WordTrace tailWord_577591 prefixEnd_577591 98860601570384968752071 := by
  unfold tailWord_577591
  simp only [CollatzResearch.WordTrace]
  refine ⟨21066474450493926534404627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14044316300329284356269751 21066474450493926534404627)
  ·
    refine ⟨31599711675740889801606941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21066474450493926534404627 31599711675740889801606941)
    ·
      refine ⟨11849891878402833675602603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31599711675740889801606941 11849891878402833675602603)
      ·
        refine ⟨17774837817604250513403905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11849891878402833675602603 17774837817604250513403905)
        ·
          refine ⟨13331128363203187885052929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17774837817604250513403905 13331128363203187885052929)
          ·
            refine ⟨9998346272402390913789697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13331128363203187885052929 9998346272402390913789697)
            ·
              refine ⟨7498759704301793185342273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9998346272402390913789697 7498759704301793185342273)
              ·
                refine ⟨5624069778226344889006705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7498759704301793185342273 5624069778226344889006705)
                ·
                  refine ⟨4218052333669758666755029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5624069778226344889006705 4218052333669758666755029)
                  ·
                    refine ⟨98860601570384968752071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4218052333669758666755029 98860601570384968752071)
                    ·
                      rfl

theorem cell23_577591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_577591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577591 prefixEnd_577591 := by exact prefixLift 577591
  have htrace : WordTrace (prefixWord ++ tailWord_577591) baseStart_577591 baseEnd_577591 := by
    simpa [prefixWord, tailWord_577591, baseEnd_577591] using wordTrace_append hprefix tailTrace_577591
  have hstable : (prefixWord ++ tailWord_577591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577591).length < 2 ^ (prefixWord ++ tailWord_577591).sum := by decide
  have hdescent : baseEnd_577591 < baseStart_577591 := by decide
  rcases family_descends (prefixWord ++ tailWord_577591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577592 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_577592 : Nat := 118140960795 + 577592 * 2 ^ 59
def prefixEnd_577592 : Nat := 4983230072969 + 3 ^ 40 * 577592 * 2
def baseEnd_577592 : Nat := 296582318191809402343709

theorem tailTrace_577592 : CollatzResearch.WordTrace tailWord_577592 prefixEnd_577592 296582318191809402343709 := by
  unfold tailWord_577592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10533255461745151852595515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14044340615660202470127353 10533255461745151852595515)
  ·
    refine ⟨15799883192617727778893273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10533255461745151852595515 15799883192617727778893273)
    ·
      refine ⟨11849912394463295834169955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15799883192617727778893273 11849912394463295834169955)
      ·
        refine ⟨17774868591694943751254933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11849912394463295834169955 17774868591694943751254933)
        ·
          refine ⟨833196965235700488340075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17774868591694943751254933 833196965235700488340075)
          ·
            refine ⟨1249795447853550732510113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833196965235700488340075 1249795447853550732510113)
            ·
              refine ⟨937346585890163049382585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1249795447853550732510113 937346585890163049382585)
              ·
                refine ⟨703009939417622287036939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937346585890163049382585 703009939417622287036939)
                ·
                  refine ⟨1054514909126433430555409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703009939417622287036939 1054514909126433430555409)
                  ·
                    refine ⟨790886181844825072916557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1054514909126433430555409 790886181844825072916557)
                    ·
                      refine ⟨296582318191809402343709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 790886181844825072916557 296582318191809402343709)
                      ·
                        rfl

theorem cell23_577592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_577592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577592 prefixEnd_577592 := by exact prefixLift 577592
  have htrace : WordTrace (prefixWord ++ tailWord_577592) baseStart_577592 baseEnd_577592 := by
    simpa [prefixWord, tailWord_577592, baseEnd_577592] using wordTrace_append hprefix tailTrace_577592
  have hstable : (prefixWord ++ tailWord_577592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577592).length < 2 ^ (prefixWord ++ tailWord_577592).sum := by decide
  have hdescent : baseEnd_577592 < baseStart_577592 := by decide
  rcases family_descends (prefixWord ++ tailWord_577592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577648 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_577648 : Nat := 118140960795 + 577648 * 2 ^ 59
def prefixEnd_577648 : Nat := 4983230072969 + 3 ^ 40 * 577648 * 2
def baseEnd_577648 : Nat := 296611073108461183243451

theorem tailTrace_577648 : CollatzResearch.WordTrace tailWord_577648 prefixEnd_577648 296611073108461183243451 := by
  unfold tailWord_577648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10534276705643712634614799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14045702274191616846153065 10534276705643712634614799)
  ·
    refine ⟨15801415058465568951922199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10534276705643712634614799 15801415058465568951922199)
    ·
      refine ⟨23702122587698353427883299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15801415058465568951922199 23702122587698353427883299)
      ·
        refine ⟨35553183881547530141824949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23702122587698353427883299 35553183881547530141824949)
        ·
          refine ⟨3333110988895080950796089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35553183881547530141824949 3333110988895080950796089)
          ·
            refine ⟨2499833241671310713097067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3333110988895080950796089 2499833241671310713097067)
            ·
              refine ⟨3749749862506966069645601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2499833241671310713097067 3749749862506966069645601)
              ·
                refine ⟨2812312396880224552234201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3749749862506966069645601 2812312396880224552234201)
                ·
                  refine ⟨2109234297660168414175651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812312396880224552234201 2109234297660168414175651)
                  ·
                    refine ⟨3163851446490252621263477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2109234297660168414175651 3163851446490252621263477)
                    ·
                      refine ⟨296611073108461183243451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3163851446490252621263477 296611073108461183243451)
                      ·
                        rfl

theorem cell23_577648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_577648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577648 prefixEnd_577648 := by exact prefixLift 577648
  have htrace : WordTrace (prefixWord ++ tailWord_577648) baseStart_577648 baseEnd_577648 := by
    simpa [prefixWord, tailWord_577648, baseEnd_577648] using wordTrace_append hprefix tailTrace_577648
  have hstable : (prefixWord ++ tailWord_577648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577648).length < 2 ^ (prefixWord ++ tailWord_577648).sum := by decide
  have hdescent : baseEnd_577648 < baseStart_577648 := by decide
  rcases family_descends (prefixWord ++ tailWord_577648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577685 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 5]
def baseStart_577685 : Nat := 118140960795 + 577685 * 2 ^ 59
def prefixEnd_577685 : Nat := 4983230072969 + 3 ^ 40 * 577685 * 2
def baseEnd_577685 : Nat := 32958896876964170942309

theorem tailTrace_577685 : CollatzResearch.WordTrace tailWord_577685 prefixEnd_577685 32958896876964170942309 := by
  unfold tailWord_577685
  simp only [CollatzResearch.WordTrace]
  refine ⟨21069902912153380588326509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14046601941435587058884339 21069902912153380588326509)
  ·
    refine ⟨7901213592057517720622441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21069902912153380588326509 7901213592057517720622441)
    ·
      refine ⟨5925910194043138290466831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7901213592057517720622441 5925910194043138290466831)
      ·
        refine ⟨8888865291064707435700247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5925910194043138290466831 8888865291064707435700247)
        ·
          refine ⟨13333297936597061153550371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8888865291064707435700247 13333297936597061153550371)
          ·
            refine ⟨19999946904895591730325557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13333297936597061153550371 19999946904895591730325557)
            ·
              refine ⟨1874995022333961724718021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19999946904895591730325557 1874995022333961724718021)
              ·
                refine ⟨351561566687617823384629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1874995022333961724718021 351561566687617823384629)
                ·
                  refine ⟨32958896876964170942309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351561566687617823384629 32958896876964170942309)
                  ·
                    rfl

theorem cell23_577685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 5].length) (baseStart_577685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577685 prefixEnd_577685 := by exact prefixLift 577685
  have htrace : WordTrace (prefixWord ++ tailWord_577685) baseStart_577685 baseEnd_577685 := by
    simpa [prefixWord, tailWord_577685, baseEnd_577685] using wordTrace_append hprefix tailTrace_577685
  have hstable : (prefixWord ++ tailWord_577685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577685).length < 2 ^ (prefixWord ++ tailWord_577685).sum := by decide
  have hdescent : baseEnd_577685 < baseStart_577685 := by decide
  rcases family_descends (prefixWord ++ tailWord_577685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577695 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_577695 : Nat := 118140960795 + 577695 * 2 ^ 59
def prefixEnd_577695 : Nat := 4983230072969 + 3 ^ 40 * 577695 * 2
def baseEnd_577695 : Nat := 296635206699222499355735

theorem tailTrace_577695 : CollatzResearch.WordTrace tailWord_577695 prefixEnd_577695 296635206699222499355735 := by
  unfold tailWord_577695
  simp only [CollatzResearch.WordTrace]
  refine ⟨21070267642117152296190539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14046845094744768197460359 21070267642117152296190539)
  ·
    refine ⟨31605401463175728444285809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21070267642117152296190539 31605401463175728444285809)
    ·
      refine ⟨23704051097381796333214357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31605401463175728444285809 23704051097381796333214357)
      ·
        refine ⟨1111127395189771703119423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23704051097381796333214357 1111127395189771703119423)
        ·
          refine ⟨1666691092784657554679135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111127395189771703119423 1666691092784657554679135)
          ·
            refine ⟨2500036639176986332018703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666691092784657554679135 2500036639176986332018703)
            ·
              refine ⟨3750054958765479498028055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2500036639176986332018703 3750054958765479498028055)
              ·
                refine ⟨5625082438148219247042083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3750054958765479498028055 5625082438148219247042083)
                ·
                  refine ⟨8437623657222328870563125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5625082438148219247042083 8437623657222328870563125)
                  ·
                    refine ⟨791027217864593331615293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8437623657222328870563125 791027217864593331615293)
                    ·
                      refine ⟨296635206699222499355735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791027217864593331615293 296635206699222499355735)
                      ·
                        rfl

theorem cell23_577695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_577695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577695 prefixEnd_577695 := by exact prefixLift 577695
  have htrace : WordTrace (prefixWord ++ tailWord_577695) baseStart_577695 baseEnd_577695 := by
    simpa [prefixWord, tailWord_577695, baseEnd_577695] using wordTrace_append hprefix tailTrace_577695
  have hstable : (prefixWord ++ tailWord_577695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577695).length < 2 ^ (prefixWord ++ tailWord_577695).sum := by decide
  have hdescent : baseEnd_577695 < baseStart_577695 := by decide
  rcases family_descends (prefixWord ++ tailWord_577695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577730 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_577730 : Nat := 118140960795 + 577730 * 2 ^ 59
def prefixEnd_577730 : Nat := 4983230072969 + 3 ^ 40 * 577730 * 2
def baseEnd_577730 : Nat := 296653178522129862418075

theorem tailTrace_577730 : CollatzResearch.WordTrace tailWord_577730 prefixEnd_577730 296653178522129862418075 := by
  unfold tailWord_577730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5267886049247588318428661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14047696131326902182476429 5267886049247588318428661)
  ·
    refine ⟨493864317116961404852687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5267886049247588318428661 493864317116961404852687)
    ·
      refine ⟨740796475675442107279031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 493864317116961404852687 740796475675442107279031)
      ·
        refine ⟨1111194713513163160918547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 740796475675442107279031 1111194713513163160918547)
        ·
          refine ⟨1666792070269744741377821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111194713513163160918547 1666792070269744741377821)
          ·
            refine ⟨625047026351154278016683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1666792070269744741377821 625047026351154278016683)
            ·
              refine ⟨937570539526731417025025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625047026351154278016683 937570539526731417025025)
              ·
                refine ⟨703177904645048562768769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 937570539526731417025025 703177904645048562768769)
                ·
                  refine ⟨527383428483786422076577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 703177904645048562768769 527383428483786422076577)
                  ·
                    refine ⟨395537571362839816557433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527383428483786422076577 395537571362839816557433)
                    ·
                      refine ⟨296653178522129862418075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395537571362839816557433 296653178522129862418075)
                      ·
                        rfl

theorem cell23_577730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_577730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577730 prefixEnd_577730 := by exact prefixLift 577730
  have htrace : WordTrace (prefixWord ++ tailWord_577730) baseStart_577730 baseEnd_577730 := by
    simpa [prefixWord, tailWord_577730, baseEnd_577730] using wordTrace_append hprefix tailTrace_577730
  have hstable : (prefixWord ++ tailWord_577730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577730).length < 2 ^ (prefixWord ++ tailWord_577730).sum := by decide
  have hdescent : baseEnd_577730 < baseStart_577730 := by decide
  rcases family_descends (prefixWord ++ tailWord_577730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577745 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 3, 4]
def baseStart_577745 : Nat := 118140960795 + 577745 * 2 ^ 59
def prefixEnd_577745 : Nat := 4983230072969 + 3 ^ 40 * 577745 * 2
def baseEnd_577745 : Nat := 98886960243982434576835

theorem tailTrace_577745 : CollatzResearch.WordTrace tailWord_577745 prefixEnd_577745 98886960243982434576835 := by
  unfold tailWord_577745
  simp only [CollatzResearch.WordTrace]
  refine ⟨21072091291936010835510689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14048060861290673890340459 21072091291936010835510689)
  ·
    refine ⟨15804068468952008126633017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21072091291936010835510689 15804068468952008126633017)
    ·
      refine ⟨11853051351714006094974763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804068468952008126633017 11853051351714006094974763)
      ·
        refine ⟨17779577027571009142462145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11853051351714006094974763 17779577027571009142462145)
        ·
          refine ⟨13334682770678256856846609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17779577027571009142462145 13334682770678256856846609)
          ·
            refine ⟨10001012078008692642634957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13334682770678256856846609 10001012078008692642634957)
            ·
              refine ⟨3750379529253259740988109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10001012078008692642634957 3750379529253259740988109)
              ·
                refine ⟨1406392323469972402870541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3750379529253259740988109 1406392323469972402870541)
                ·
                  refine ⟨527397121301239651076453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1406392323469972402870541 527397121301239651076453)
                  ·
                    refine ⟨98886960243982434576835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 527397121301239651076453 98886960243982434576835)
                    ·
                      rfl

theorem cell23_577745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_577745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577745 prefixEnd_577745 := by exact prefixLift 577745
  have htrace : WordTrace (prefixWord ++ tailWord_577745) baseStart_577745 baseEnd_577745 := by
    simpa [prefixWord, tailWord_577745, baseEnd_577745] using wordTrace_append hprefix tailTrace_577745
  have hstable : (prefixWord ++ tailWord_577745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577745).length < 2 ^ (prefixWord ++ tailWord_577745).sum := by decide
  have hdescent : baseEnd_577745 < baseStart_577745 := by decide
  rcases family_descends (prefixWord ++ tailWord_577745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577752 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2]
def baseStart_577752 : Nat := 118140960795 + 577752 * 2 ^ 59
def prefixEnd_577752 : Nat := 4983230072969 + 3 ^ 40 * 577752 * 2
def baseEnd_577752 : Nat := 296664475096528776342973

theorem tailTrace_577752 : CollatzResearch.WordTrace tailWord_577752 prefixEnd_577752 296664475096528776342973 := by
  unfold tailWord_577752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536173301455325515507755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14048231068607100687343673 10536173301455325515507755)
  ·
    refine ⟨15804259952182988273261633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10536173301455325515507755 15804259952182988273261633)
    ·
      refine ⟨11853194964137241204946225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15804259952182988273261633 11853194964137241204946225)
      ·
        refine ⟨8889896223102930903709669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11853194964137241204946225 8889896223102930903709669)
        ·
          refine ⟨1666855541831799544445563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8889896223102930903709669 1666855541831799544445563)
          ·
            refine ⟨2500283312747699316668345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1666855541831799544445563 2500283312747699316668345)
            ·
              refine ⟨1875212484560774487501259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2500283312747699316668345 1875212484560774487501259)
              ·
                refine ⟨2812818726841161731251889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875212484560774487501259 2812818726841161731251889)
                ·
                  refine ⟨2109614045130871298438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2812818726841161731251889 2109614045130871298438917)
                  ·
                    refine ⟨395552633462038368457297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2109614045130871298438917 395552633462038368457297)
                    ·
                      refine ⟨296664475096528776342973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395552633462038368457297 296664475096528776342973)
                      ·
                        rfl

theorem cell23_577752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_577752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577752 prefixEnd_577752 := by exact prefixLift 577752
  have htrace : WordTrace (prefixWord ++ tailWord_577752) baseStart_577752 baseEnd_577752 := by
    simpa [prefixWord, tailWord_577752, baseEnd_577752] using wordTrace_append hprefix tailTrace_577752
  have hstable : (prefixWord ++ tailWord_577752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577752).length < 2 ^ (prefixWord ++ tailWord_577752).sum := by decide
  have hdescent : baseEnd_577752 < baseStart_577752 := by decide
  rcases family_descends (prefixWord ++ tailWord_577752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577796 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_577796 : Nat := 118140960795 + 577796 * 2 ^ 59
def prefixEnd_577796 : Nat := 4983230072969 + 3 ^ 40 * 577796 * 2
def baseEnd_577796 : Nat := 98895689415108868064257

theorem tailTrace_577796 : CollatzResearch.WordTrace tailWord_577796 prefixEnd_577796 98895689415108868064257 := by
  unfold tailWord_577796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10536975707375623272808621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14049300943167497697078161 10536975707375623272808621)
  ·
    refine ⟨3951365890265858727303233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10536975707375623272808621 3951365890265858727303233)
    ·
      refine ⟨2963524417699394045477425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3951365890265858727303233 2963524417699394045477425)
      ·
        refine ⟨2222643313274545534108069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2963524417699394045477425 2222643313274545534108069)
        ·
          refine ⟨416745621238977287645263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2222643313274545534108069 416745621238977287645263)
          ·
            refine ⟨625118431858465931467895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416745621238977287645263 625118431858465931467895)
            ·
              refine ⟨937677647787698897201843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625118431858465931467895 937677647787698897201843)
              ·
                refine ⟨1406516471681548345802765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937677647787698897201843 1406516471681548345802765)
                ·
                  refine ⟨527443676880580629676037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1406516471681548345802765 527443676880580629676037)
                  ·
                    refine ⟨98895689415108868064257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 527443676880580629676037 98895689415108868064257)
                    ·
                      rfl

theorem cell23_577796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_577796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577796 prefixEnd_577796 := by exact prefixLift 577796
  have htrace : WordTrace (prefixWord ++ tailWord_577796) baseStart_577796 baseEnd_577796 := by
    simpa [prefixWord, tailWord_577796, baseEnd_577796] using wordTrace_append hprefix tailTrace_577796
  have hstable : (prefixWord ++ tailWord_577796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577796).length < 2 ^ (prefixWord ++ tailWord_577796).sum := by decide
  have hdescent : baseEnd_577796 < baseStart_577796 := by decide
  rcases family_descends (prefixWord ++ tailWord_577796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577855 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_577855 : Nat := 118140960795 + 577855 * 2 ^ 59
def prefixEnd_577855 : Nat := 4983230072969 + 3 ^ 40 * 577855 * 2
def baseEnd_577855 : Nat := 296717363603941873354999

theorem tailTrace_577855 : CollatzResearch.WordTrace tailWord_577855 prefixEnd_577855 296717363603941873354999 := by
  unfold tailWord_577855
  simp only [CollatzResearch.WordTrace]
  refine ⟨21076103321537499622015019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14050735547691666414676679 21076103321537499622015019)
  ·
    refine ⟨31614154982306249433022529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21076103321537499622015019 31614154982306249433022529)
    ·
      refine ⟨23710616236729687074766897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31614154982306249433022529 23710616236729687074766897)
      ·
        refine ⟨17782962177547265306075173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23710616236729687074766897 17782962177547265306075173)
        ·
          refine ⟨3334305408290112244889095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17782962177547265306075173 3334305408290112244889095)
          ·
            refine ⟨5001458112435168367333643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334305408290112244889095 5001458112435168367333643)
            ·
              refine ⟨7502187168652752551000465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001458112435168367333643 7502187168652752551000465)
              ·
                refine ⟨5626640376489564413250349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7502187168652752551000465 5626640376489564413250349)
                ·
                  refine ⟨2109990141183586654968881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5626640376489564413250349 2109990141183586654968881)
                  ·
                    refine ⟨1582492605887689991226661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2109990141183586654968881 1582492605887689991226661)
                    ·
                      refine ⟨296717363603941873354999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1582492605887689991226661 296717363603941873354999)
                      ·
                        rfl

theorem cell23_577855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_577855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577855 prefixEnd_577855 := by exact prefixLift 577855
  have htrace : WordTrace (prefixWord ++ tailWord_577855) baseStart_577855 baseEnd_577855 := by
    simpa [prefixWord, tailWord_577855, baseEnd_577855] using wordTrace_append hprefix tailTrace_577855
  have hstable : (prefixWord ++ tailWord_577855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577855).length < 2 ^ (prefixWord ++ tailWord_577855).sum := by decide
  have hdescent : baseEnd_577855 < baseStart_577855 := by decide
  rcases family_descends (prefixWord ++ tailWord_577855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577872 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_577872 : Nat := 118140960795 + 577872 * 2 ^ 59
def prefixEnd_577872 : Nat := 4983230072969 + 3 ^ 40 * 577872 * 2
def baseEnd_577872 : Nat := 296726092775068306842421

theorem tailTrace_577872 : CollatzResearch.WordTrace tailWord_577872 prefixEnd_577872 296726092775068306842421 := by
  unfold tailWord_577872
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538361681237955762691935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14051148908317274350255913 10538361681237955762691935)
  ·
    refine ⟨15807542521856933644037903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10538361681237955762691935 15807542521856933644037903)
    ·
      refine ⟨23711313782785400466056855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15807542521856933644037903 23711313782785400466056855)
      ·
        refine ⟨35566970674178100699085283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23711313782785400466056855 35566970674178100699085283)
        ·
          refine ⟨53350456011267151048627925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35566970674178100699085283 53350456011267151048627925)
          ·
            refine ⟨1250401312764073852702217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53350456011267151048627925 1250401312764073852702217)
            ·
              refine ⟨937800984573055389526663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250401312764073852702217 937800984573055389526663)
              ·
                refine ⟨1406701476859583084289995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937800984573055389526663 1406701476859583084289995)
                ·
                  refine ⟨2110052215289374626434993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406701476859583084289995 2110052215289374626434993)
                  ·
                    refine ⟨1582539161467030969826245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2110052215289374626434993 1582539161467030969826245)
                    ·
                      refine ⟨296726092775068306842421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1582539161467030969826245 296726092775068306842421)
                      ·
                        rfl

theorem cell23_577872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_577872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577872 prefixEnd_577872 := by exact prefixLift 577872
  have htrace : WordTrace (prefixWord ++ tailWord_577872) baseStart_577872 baseEnd_577872 := by
    simpa [prefixWord, tailWord_577872, baseEnd_577872] using wordTrace_append hprefix tailTrace_577872
  have hstable : (prefixWord ++ tailWord_577872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577872).length < 2 ^ (prefixWord ++ tailWord_577872).sum := by decide
  have hdescent : baseEnd_577872 < baseStart_577872 := by decide
  rcases family_descends (prefixWord ++ tailWord_577872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577876 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 3, 2, 2]
def baseStart_577876 : Nat := 118140960795 + 577876 * 2 ^ 59
def prefixEnd_577876 : Nat := 4983230072969 + 3 ^ 40 * 577876 * 2
def baseEnd_577876 : Nat := 296728146697686291192403

theorem tailTrace_577876 : CollatzResearch.WordTrace tailWord_577876 prefixEnd_577876 296728146697686291192403 := by
  unfold tailWord_577876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538434627230710104264741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14051246169640946805686321 10538434627230710104264741)
  ·
    refine ⟨1975956492605758144549639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10538434627230710104264741 1975956492605758144549639)
    ·
      refine ⟨2963934738908637216824459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1975956492605758144549639 2963934738908637216824459)
      ·
        refine ⟨4445902108362955825236689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2963934738908637216824459 4445902108362955825236689)
        ·
          refine ⟨3334426581272216868927517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4445902108362955825236689 3334426581272216868927517)
          ·
            refine ⟨1250409967977081325847819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3334426581272216868927517 1250409967977081325847819)
            ·
              refine ⟨1875614951965621988771729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250409967977081325847819 1875614951965621988771729)
              ·
                refine ⟨1406711213974216491578797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875614951965621988771729 1406711213974216491578797)
                ·
                  refine ⟨527516705240331184342049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1406711213974216491578797 527516705240331184342049)
                  ·
                    refine ⟨395637528930248388256537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527516705240331184342049 395637528930248388256537)
                    ·
                      refine ⟨296728146697686291192403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395637528930248388256537 296728146697686291192403)
                      ·
                        rfl

theorem cell23_577876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_577876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577876 prefixEnd_577876 := by exact prefixLift 577876
  have htrace : WordTrace (prefixWord ++ tailWord_577876) baseStart_577876 baseEnd_577876 := by
    simpa [prefixWord, tailWord_577876, baseEnd_577876] using wordTrace_append hprefix tailTrace_577876
  have hstable : (prefixWord ++ tailWord_577876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577876).length < 2 ^ (prefixWord ++ tailWord_577876).sum := by decide
  have hdescent : baseEnd_577876 < baseStart_577876 := by decide
  rcases family_descends (prefixWord ++ tailWord_577876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577892 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_577892 : Nat := 118140960795 + 577892 * 2 ^ 59
def prefixEnd_577892 : Nat := 4983230072969 + 3 ^ 40 * 577892 * 2
def baseEnd_577892 : Nat := 296736362388158228592329

theorem tailTrace_577892 : CollatzResearch.WordTrace tailWord_577892 prefixEnd_577892 296736362388158228592329 := by
  unfold tailWord_577892
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538726411201727470555965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14051635214935636627407953 10538726411201727470555965)
  ·
    refine ⟨3952022404200647801458487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10538726411201727470555965 3952022404200647801458487)
    ·
      refine ⟨5928033606300971702187731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3952022404200647801458487 5928033606300971702187731)
      ·
        refine ⟨8892050409451457553281597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5928033606300971702187731 8892050409451457553281597)
        ·
          refine ⟨3334518903544296582480599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8892050409451457553281597 3334518903544296582480599)
          ·
            refine ⟨5001778355316444873720899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3334518903544296582480599 5001778355316444873720899)
            ·
              refine ⟨7502667532974667310581349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5001778355316444873720899 7502667532974667310581349)
              ·
                refine ⟨1406750162432750120734003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7502667532974667310581349 1406750162432750120734003)
                ·
                  refine ⟨2110125243649125181101005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1406750162432750120734003 2110125243649125181101005)
                  ·
                    refine ⟨791296966368421942912877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2110125243649125181101005 791296966368421942912877)
                    ·
                      refine ⟨296736362388158228592329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791296966368421942912877 296736362388158228592329)
                      ·
                        rfl

theorem cell23_577892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_577892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577892 prefixEnd_577892 := by exact prefixLift 577892
  have htrace : WordTrace (prefixWord ++ tailWord_577892) baseStart_577892 baseEnd_577892 := by
    simpa [prefixWord, tailWord_577892, baseEnd_577892] using wordTrace_append hprefix tailTrace_577892
  have hstable : (prefixWord ++ tailWord_577892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577892).length < 2 ^ (prefixWord ++ tailWord_577892).sum := by decide
  have hdescent : baseEnd_577892 < baseStart_577892 := by decide
  rcases family_descends (prefixWord ++ tailWord_577892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577893 : List Nat := [1, 3, 1, 3, 1, 4, 2, 3, 1, 2, 2]
def baseStart_577893 : Nat := 118140960795 + 577893 * 2 ^ 59
def prefixEnd_577893 : Nat := 4983230072969 + 3 ^ 40 * 577893 * 2
def baseEnd_577893 : Nat := 296736875868812724679825

theorem tailTrace_577893 : CollatzResearch.WordTrace tailWord_577893 prefixEnd_577893 296736875868812724679825 := by
  unfold tailWord_577893
  simp only [CollatzResearch.WordTrace]
  refine ⟨21077489295399832111898333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14051659530266554741265555 21077489295399832111898333)
  ·
    refine ⟨7904058485774937041961875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21077489295399832111898333 7904058485774937041961875)
    ·
      refine ⟨11856087728662405562942813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7904058485774937041961875 11856087728662405562942813)
      ·
        refine ⟨4446032898248402086103555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11856087728662405562942813 4446032898248402086103555)
        ·
          refine ⟨6669049347372603129155333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446032898248402086103555 6669049347372603129155333)
          ·
            refine ⟨1250446752632363086716625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6669049347372603129155333 1250446752632363086716625)
            ·
              refine ⟨937835064474272315037469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250446752632363086716625 937835064474272315037469)
              ·
                refine ⟨351688149177852118139051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 937835064474272315037469 351688149177852118139051)
                ·
                  refine ⟨527532223766778177208577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351688149177852118139051 527532223766778177208577)
                  ·
                    refine ⟨395649167825083632906433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527532223766778177208577 395649167825083632906433)
                    ·
                      refine ⟨296736875868812724679825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395649167825083632906433 296736875868812724679825)
                      ·
                        rfl

theorem cell23_577893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_577893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577893 prefixEnd_577893 := by exact prefixLift 577893
  have htrace : WordTrace (prefixWord ++ tailWord_577893) baseStart_577893 baseEnd_577893 := by
    simpa [prefixWord, tailWord_577893, baseEnd_577893] using wordTrace_append hprefix tailTrace_577893
  have hstable : (prefixWord ++ tailWord_577893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577893).length < 2 ^ (prefixWord ++ tailWord_577893).sum := by decide
  have hdescent : baseEnd_577893 < baseStart_577893 := by decide
  rcases family_descends (prefixWord ++ tailWord_577893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577896 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_577896 : Nat := 118140960795 + 577896 * 2 ^ 59
def prefixEnd_577896 : Nat := 4983230072969 + 3 ^ 40 * 577896 * 2
def baseEnd_577896 : Nat := 296738416310776212942311

theorem tailTrace_577896 : CollatzResearch.WordTrace tailWord_577896 prefixEnd_577896 296738416310776212942311 := by
  unfold tailWord_577896
  simp only [CollatzResearch.WordTrace]
  refine ⟨10538799357194481812128771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14051732476259309082838361 10538799357194481812128771)
  ·
    refine ⟨15808199035791722718193157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10538799357194481812128771 15808199035791722718193157)
    ·
      refine ⟨2964037319210948009661217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15808199035791722718193157 2964037319210948009661217)
      ·
        refine ⟨2223027989408211007245913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2964037319210948009661217 2223027989408211007245913)
        ·
          refine ⟨1667270992056158255434435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2223027989408211007245913 1667270992056158255434435)
          ·
            refine ⟨2500906488084237383151653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667270992056158255434435 2500906488084237383151653)
            ·
              refine ⟨468919966515794509340935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2500906488084237383151653 468919966515794509340935)
              ·
                refine ⟨703379949773691764011403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 468919966515794509340935 703379949773691764011403)
                ·
                  refine ⟨1055069924660537646017105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703379949773691764011403 1055069924660537646017105)
                  ·
                    refine ⟨791302443495403234512829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055069924660537646017105 791302443495403234512829)
                    ·
                      refine ⟨296738416310776212942311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791302443495403234512829 296738416310776212942311)
                      ·
                        rfl

theorem cell23_577896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_577896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577896 prefixEnd_577896 := by exact prefixLift 577896
  have htrace : WordTrace (prefixWord ++ tailWord_577896) baseStart_577896 baseEnd_577896 := by
    simpa [prefixWord, tailWord_577896, baseEnd_577896] using wordTrace_append hprefix tailTrace_577896
  have hstable : (prefixWord ++ tailWord_577896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577896).length < 2 ^ (prefixWord ++ tailWord_577896).sum := by decide
  have hdescent : baseEnd_577896 < baseStart_577896 := by decide
  rcases family_descends (prefixWord ++ tailWord_577896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577910 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_577910 : Nat := 118140960795 + 577910 * 2 ^ 59
def prefixEnd_577910 : Nat := 4983230072969 + 3 ^ 40 * 577910 * 2
def baseEnd_577910 : Nat := 296745605039939158167247

theorem tailTrace_577910 : CollatzResearch.WordTrace tailWord_577910 prefixEnd_577910 296745605039939158167247 := by
  unfold tailWord_577910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317381833521140250954199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14052072890892162676844789 1317381833521140250954199)
  ·
    refine ⟨1976072750281710376431299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317381833521140250954199 1976072750281710376431299)
    ·
      refine ⟨2964109125422565564646949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976072750281710376431299 2964109125422565564646949)
      ·
        refine ⟨555770461016731043371303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2964109125422565564646949 555770461016731043371303)
        ·
          refine ⟨833655691525096565056955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555770461016731043371303 833655691525096565056955)
          ·
            refine ⟨1250483537287644847585433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833655691525096565056955 1250483537287644847585433)
            ·
              refine ⟨937862652965733635689075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1250483537287644847585433 937862652965733635689075)
              ·
                refine ⟨1406793979448600453533613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 937862652965733635689075 1406793979448600453533613)
                ·
                  refine ⟨527547742293225170075105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1406793979448600453533613 527547742293225170075105)
                  ·
                    refine ⟨395660806719918877556329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 527547742293225170075105 395660806719918877556329)
                    ·
                      refine ⟨296745605039939158167247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395660806719918877556329 296745605039939158167247)
                      ·
                        rfl

theorem cell23_577910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_577910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577910 prefixEnd_577910 := by exact prefixLift 577910
  have htrace : WordTrace (prefixWord ++ tailWord_577910) baseStart_577910 baseEnd_577910 := by
    simpa [prefixWord, tailWord_577910, baseEnd_577910] using wordTrace_append hprefix tailTrace_577910
  have hstable : (prefixWord ++ tailWord_577910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577910).length < 2 ^ (prefixWord ++ tailWord_577910).sum := by decide
  have hdescent : baseEnd_577910 < baseStart_577910 := by decide
  rcases family_descends (prefixWord ++ tailWord_577910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577952 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_577952 : Nat := 118140960795 + 577952 * 2 ^ 59
def prefixEnd_577952 : Nat := 4983230072969 + 3 ^ 40 * 577952 * 2
def baseEnd_577952 : Nat := 296767171227427993842053

theorem tailTrace_577952 : CollatzResearch.WordTrace tailWord_577952 prefixEnd_577952 296767171227427993842053 := by
  unfold tailWord_577952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10539820601093042594148055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14053094134790723458864073 10539820601093042594148055)
  ·
    refine ⟨15809730901639563891222083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10539820601093042594148055 15809730901639563891222083)
    ·
      refine ⟨23714596352459345836833125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15809730901639563891222083 23714596352459345836833125)
      ·
        refine ⟨4446486816086127344406211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23714596352459345836833125 4446486816086127344406211)
        ·
          refine ⟨6669730224129191016609317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4446486816086127344406211 6669730224129191016609317)
          ·
            refine ⟨1250574417024223315614247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6669730224129191016609317 1250574417024223315614247)
            ·
              refine ⟨1875861625536334973421371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250574417024223315614247 1875861625536334973421371)
              ·
                refine ⟨2813792438304502460132057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1875861625536334973421371 2813792438304502460132057)
                ·
                  refine ⟨2110344328728376845099043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2813792438304502460132057 2110344328728376845099043)
                  ·
                    refine ⟨3165516493092565267648565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2110344328728376845099043 3165516493092565267648565)
                    ·
                      refine ⟨296767171227427993842053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3165516493092565267648565 296767171227427993842053)
                      ·
                        rfl

theorem cell23_577952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_577952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577952 prefixEnd_577952 := by exact prefixLift 577952
  have htrace : WordTrace (prefixWord ++ tailWord_577952) baseStart_577952 baseEnd_577952 := by
    simpa [prefixWord, tailWord_577952, baseEnd_577952] using wordTrace_append hprefix tailTrace_577952
  have hstable : (prefixWord ++ tailWord_577952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577952).length < 2 ^ (prefixWord ++ tailWord_577952).sum := by decide
  have hdescent : baseEnd_577952 < baseStart_577952 := by decide
  rcases family_descends (prefixWord ++ tailWord_577952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577995 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_577995 : Nat := 118140960795 + 577995 * 2 ^ 59
def prefixEnd_577995 : Nat := 4983230072969 + 3 ^ 40 * 577995 * 2
def baseEnd_577995 : Nat := 296789250895571325604355

theorem tailTrace_577995 : CollatzResearch.WordTrace tailWord_577995 prefixEnd_577995 296789250895571325604355 := by
  unfold tailWord_577995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21081209541030303532111439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14054139694020202354740959 21081209541030303532111439)
  ·
    refine ⟨31621814311545455298167159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21081209541030303532111439 31621814311545455298167159)
    ·
      refine ⟨47432721467318182947250739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31621814311545455298167159 47432721467318182947250739)
      ·
        refine ⟨71149082200977274420876109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47432721467318182947250739 71149082200977274420876109)
        ·
          refine ⟨26680905825366477907828541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71149082200977274420876109 26680905825366477907828541)
          ·
            refine ⟨10005339684512429215435703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26680905825366477907828541 10005339684512429215435703)
            ·
              refine ⟨15008009526768643823153555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10005339684512429215435703 15008009526768643823153555)
              ·
                refine ⟨22512014290152965734730333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15008009526768643823153555 22512014290152965734730333)
                ·
                  refine ⟨8442005358807362150523875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22512014290152965734730333 8442005358807362150523875)
                  ·
                    refine ⟨12663008038211043225785813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8442005358807362150523875 12663008038211043225785813)
                    ·
                      refine ⟨296789250895571325604355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12663008038211043225785813 296789250895571325604355)
                      ·
                        rfl

theorem cell23_577995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_577995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_577995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_577995 prefixEnd_577995 := by exact prefixLift 577995
  have htrace : WordTrace (prefixWord ++ tailWord_577995) baseStart_577995 baseEnd_577995 := by
    simpa [prefixWord, tailWord_577995, baseEnd_577995] using wordTrace_append hprefix tailTrace_577995
  have hstable : (prefixWord ++ tailWord_577995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577995).length < 2 ^ (prefixWord ++ tailWord_577995).sum := by decide
  have hdescent : baseEnd_577995 < baseStart_577995 := by decide
  rcases family_descends (prefixWord ++ tailWord_577995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578006 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_578006 : Nat := 118140960795 + 578006 * 2 ^ 59
def prefixEnd_578006 : Nat := 4983230072969 + 3 ^ 40 * 578006 * 2
def baseEnd_578006 : Nat := 32977211020307864729645

theorem tailTrace_578006 : CollatzResearch.WordTrace tailWord_578006 prefixEnd_578006 32977211020307864729645 := by
  unfold tailWord_578006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317600671499403275672617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14054407162660301607174581 1317600671499403275672617)
  ·
    refine ⟨988200503624552456754463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1317600671499403275672617 988200503624552456754463)
    ·
      refine ⟨1482300755436828685131695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 988200503624552456754463 1482300755436828685131695)
      ·
        refine ⟨2223451133155243027697543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482300755436828685131695 2223451133155243027697543)
        ·
          refine ⟨3335176699732864541546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2223451133155243027697543 3335176699732864541546315)
          ·
            refine ⟨5002765049599296812319473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3335176699732864541546315 5002765049599296812319473)
            ·
              refine ⟨3752073787199472609239605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5002765049599296812319473 3752073787199472609239605)
              ·
                refine ⟨351756917549950557116213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3752073787199472609239605 351756917549950557116213)
                ·
                  refine ⟨32977211020307864729645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351756917549950557116213 32977211020307864729645)
                  ·
                    rfl

theorem cell23_578006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_578006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578006 prefixEnd_578006 := by exact prefixLift 578006
  have htrace : WordTrace (prefixWord ++ tailWord_578006) baseStart_578006 baseEnd_578006 := by
    simpa [prefixWord, tailWord_578006, baseEnd_578006] using wordTrace_append hprefix tailTrace_578006
  have hstable : (prefixWord ++ tailWord_578006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578006).length < 2 ^ (prefixWord ++ tailWord_578006).sum := by decide
  have hdescent : baseEnd_578006 < baseStart_578006 := by decide
  rcases family_descends (prefixWord ++ tailWord_578006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578029 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_578029 : Nat := 118140960795 + 578029 * 2 ^ 59
def prefixEnd_578029 : Nat := 4983230072969 + 3 ^ 40 * 578029 * 2
def baseEnd_578029 : Nat := 296806709237824192579199

theorem tailTrace_578029 : CollatzResearch.WordTrace tailWord_578029 prefixEnd_578029 296806709237824192579199 := by
  unfold tailWord_578029
  simp only [CollatzResearch.WordTrace]
  refine ⟨21082449622907127338849141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14054966415271418225899427 21082449622907127338849141)
  ·
    refine ⟨1976479652147543188017107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21082449622907127338849141 1976479652147543188017107)
    ·
      refine ⟨2964719478221314782025661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976479652147543188017107 2964719478221314782025661)
      ·
        refine ⟨1111769804332993043259623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2964719478221314782025661 1111769804332993043259623)
        ·
          refine ⟨1667654706499489564889435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1111769804332993043259623 1667654706499489564889435)
          ·
            refine ⟨2501482059749234347334153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667654706499489564889435 2501482059749234347334153)
            ·
              refine ⟨1876111544811925760500615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501482059749234347334153 1876111544811925760500615)
              ·
                refine ⟨2814167317217888640750923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876111544811925760500615 2814167317217888640750923)
                ·
                  refine ⟨4221250975826832961126385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814167317217888640750923 4221250975826832961126385)
                  ·
                    refine ⟨3165938231870124720844789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4221250975826832961126385 3165938231870124720844789)
                    ·
                      refine ⟨296806709237824192579199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3165938231870124720844789 296806709237824192579199)
                      ·
                        rfl

theorem cell23_578029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_578029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578029 prefixEnd_578029 := by exact prefixLift 578029
  have htrace : WordTrace (prefixWord ++ tailWord_578029) baseStart_578029 baseEnd_578029 := by
    simpa [prefixWord, tailWord_578029, baseEnd_578029] using wordTrace_append hprefix tailTrace_578029
  have hstable : (prefixWord ++ tailWord_578029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578029).length < 2 ^ (prefixWord ++ tailWord_578029).sum := by decide
  have hdescent : baseEnd_578029 < baseStart_578029 := by decide
  rcases family_descends (prefixWord ++ tailWord_578029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578049 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_578049 : Nat := 118140960795 + 578049 * 2 ^ 59
def prefixEnd_578049 : Nat := 4983230072969 + 3 ^ 40 * 578049 * 2
def baseEnd_578049 : Nat := 98938992950304704776369

theorem tailTrace_578049 : CollatzResearch.WordTrace tailWord_578049 prefixEnd_578049 98938992950304704776369 := by
  unfold tailWord_578049
  simp only [CollatzResearch.WordTrace]
  refine ⟨21083179082834670754577201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14055452721889780503051467 21083179082834670754577201)
  ·
    refine ⟨15812384312126003065932901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21083179082834670754577201 15812384312126003065932901)
    ·
      refine ⟨2964822058523625574862419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15812384312126003065932901 2964822058523625574862419)
      ·
        refine ⟨4447233087785438362293629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2964822058523625574862419 4447233087785438362293629)
        ·
          refine ⟨1667712407919539385860111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4447233087785438362293629 1667712407919539385860111)
          ·
            refine ⟨2501568611879309078790167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1667712407919539385860111 2501568611879309078790167)
            ·
              refine ⟨3752352917818963618185251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2501568611879309078790167 3752352917818963618185251)
              ·
                refine ⟨5628529376728445427277877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3752352917818963618185251 5628529376728445427277877)
                ·
                  refine ⟨527674629068291758807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5628529376728445427277877 527674629068291758807301)
                  ·
                    refine ⟨98938992950304704776369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 527674629068291758807301 98938992950304704776369)
                    ·
                      rfl

theorem cell23_578049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_578049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578049 prefixEnd_578049 := by exact prefixLift 578049
  have htrace : WordTrace (prefixWord ++ tailWord_578049) baseStart_578049 baseEnd_578049 := by
    simpa [prefixWord, tailWord_578049, baseEnd_578049] using wordTrace_append hprefix tailTrace_578049
  have hstable : (prefixWord ++ tailWord_578049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578049).length < 2 ^ (prefixWord ++ tailWord_578049).sum := by decide
  have hdescent : baseEnd_578049 < baseStart_578049 := by decide
  rcases family_descends (prefixWord ++ tailWord_578049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578059 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3]
def baseStart_578059 : Nat := 118140960795 + 578059 * 2 ^ 59
def prefixEnd_578059 : Nat := 4983230072969 + 3 ^ 40 * 578059 * 2
def baseEnd_578059 : Nat := 296822113657459075204061

theorem tailTrace_578059 : CollatzResearch.WordTrace tailWord_578059 prefixEnd_578059 296822113657459075204061 := by
  unfold tailWord_578059
  simp only [CollatzResearch.WordTrace]
  refine ⟨21083543812798442462441231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14055695875198961641627487 21083543812798442462441231)
  ·
    refine ⟨31625315719197663693661847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21083543812798442462441231 31625315719197663693661847)
    ·
      refine ⟨47437973578796495540492771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31625315719197663693661847 47437973578796495540492771)
      ·
        refine ⟨71156960368194743310739157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47437973578796495540492771 71156960368194743310739157)
        ·
          refine ⟨1667741258629564296345449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 71156960368194743310739157 1667741258629564296345449)
          ·
            refine ⟨1250805943972173222259087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1667741258629564296345449 1250805943972173222259087)
            ·
              refine ⟨1876208915958259833388631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250805943972173222259087 1876208915958259833388631)
              ·
                refine ⟨2814313373937389750082947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1876208915958259833388631 2814313373937389750082947)
                ·
                  refine ⟨4221470060906084625124421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2814313373937389750082947 4221470060906084625124421)
                  ·
                    refine ⟨791525636419890867210829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4221470060906084625124421 791525636419890867210829)
                    ·
                      refine ⟨296822113657459075204061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791525636419890867210829 296822113657459075204061)
                      ·
                        rfl

theorem cell23_578059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3].length) (baseStart_578059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578059 prefixEnd_578059 := by exact prefixLift 578059
  have htrace : WordTrace (prefixWord ++ tailWord_578059) baseStart_578059 baseEnd_578059 := by
    simpa [prefixWord, tailWord_578059, baseEnd_578059] using wordTrace_append hprefix tailTrace_578059
  have hstable : (prefixWord ++ tailWord_578059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578059).length < 2 ^ (prefixWord ++ tailWord_578059).sum := by decide
  have hdescent : baseEnd_578059 < baseStart_578059 := by decide
  rcases family_descends (prefixWord ++ tailWord_578059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578092 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_578092 : Nat := 118140960795 + 578092 * 2 ^ 59
def prefixEnd_578092 : Nat := 4983230072969 + 3 ^ 40 * 578092 * 2
def baseEnd_578092 : Nat := 98946352839685815363803

theorem tailTrace_578092 : CollatzResearch.WordTrace tailWord_578092 prefixEnd_578092 98946352839685815363803 := by
  unfold tailWord_578092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10542373710839444549196265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14056498281119259398928353 10542373710839444549196265)
  ·
    refine ⟨7906780283129583411897199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10542373710839444549196265 7906780283129583411897199)
    ·
      refine ⟨11860170424694375117845799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7906780283129583411897199 11860170424694375117845799)
      ·
        refine ⟨17790255637041562676768699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11860170424694375117845799 17790255637041562676768699)
        ·
          refine ⟨26685383455562344015153049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17790255637041562676768699 26685383455562344015153049)
          ·
            refine ⟨20014037591671758011364787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26685383455562344015153049 20014037591671758011364787)
            ·
              refine ⟨30021056387507637017047181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20014037591671758011364787 30021056387507637017047181)
              ·
                refine ⟨11257896145315363881392693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30021056387507637017047181 11257896145315363881392693)
                ·
                  refine ⟨1055427763623315363880565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11257896145315363881392693 1055427763623315363880565)
                  ·
                    refine ⟨98946352839685815363803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1055427763623315363880565 98946352839685815363803)
                    ·
                      rfl

theorem cell23_578092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_578092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578092 prefixEnd_578092 := by exact prefixLift 578092
  have htrace : WordTrace (prefixWord ++ tailWord_578092) baseStart_578092 baseEnd_578092 := by
    simpa [prefixWord, tailWord_578092, baseEnd_578092] using wordTrace_append hprefix tailTrace_578092
  have hstable : (prefixWord ++ tailWord_578092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578092).length < 2 ^ (prefixWord ++ tailWord_578092).sum := by decide
  have hdescent : baseEnd_578092 < baseStart_578092 := by decide
  rcases family_descends (prefixWord ++ tailWord_578092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578099 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 5, 2]
def baseStart_578099 : Nat := 118140960795 + 578099 * 2 ^ 59
def prefixEnd_578099 : Nat := 4983230072969 + 3 ^ 40 * 578099 * 2
def baseEnd_578099 : Nat := 296842652883638918703877

theorem tailTrace_578099 : CollatzResearch.WordTrace tailWord_578099 prefixEnd_578099 296842652883638918703877 := by
  unfold tailWord_578099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21085002732653529293897351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14056668488435686195931567 21085002732653529293897351)
  ·
    refine ⟨31627504098980293940846027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21085002732653529293897351 31627504098980293940846027)
    ·
      refine ⟨47441256148470440911269041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31627504098980293940846027 47441256148470440911269041)
      ·
        refine ⟨35580942111352830683451781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47441256148470440911269041 35580942111352830683451781)
        ·
          refine ⟨6671426645878655753147209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35580942111352830683451781 6671426645878655753147209)
          ·
            refine ⟨5003569984408991814860407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6671426645878655753147209 5003569984408991814860407)
            ·
              refine ⟨7505354976613487722290611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5003569984408991814860407 7505354976613487722290611)
              ·
                refine ⟨11258032464920231583435917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7505354976613487722290611 11258032464920231583435917)
                ·
                  refine ⟨4221762174345086843788469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11258032464920231583435917 4221762174345086843788469)
                  ·
                    refine ⟨395790203844851891605169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4221762174345086843788469 395790203844851891605169)
                    ·
                      refine ⟨296842652883638918703877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395790203844851891605169 296842652883638918703877)
                      ·
                        rfl

theorem cell23_578099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5, 2].length) (baseStart_578099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578099 prefixEnd_578099 := by exact prefixLift 578099
  have htrace : WordTrace (prefixWord ++ tailWord_578099) baseStart_578099 baseEnd_578099 := by
    simpa [prefixWord, tailWord_578099, baseEnd_578099] using wordTrace_append hprefix tailTrace_578099
  have hstable : (prefixWord ++ tailWord_578099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578099).length < 2 ^ (prefixWord ++ tailWord_578099).sum := by decide
  have hdescent : baseEnd_578099 < baseStart_578099 := by decide
  rcases family_descends (prefixWord ++ tailWord_578099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578106 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_578106 : Nat := 118140960795 + 578106 * 2 ^ 59
def prefixEnd_578106 : Nat := 4983230072969 + 3 ^ 40 * 578106 * 2
def baseEnd_578106 : Nat := 296846247248220391316345

theorem tailTrace_578106 : CollatzResearch.WordTrace tailWord_578106 prefixEnd_578106 296846247248220391316345 := by
  unfold tailWord_578106
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271314510907042372350543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14056838695752112992934781 5271314510907042372350543)
  ·
    refine ⟨7906971766360563558525815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5271314510907042372350543 7906971766360563558525815)
    ·
      refine ⟨11860457649540845337788723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7906971766360563558525815 11860457649540845337788723)
      ·
        refine ⟨17790686474311268006683085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11860457649540845337788723 17790686474311268006683085)
        ·
          refine ⟨6671507427866725502506157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17790686474311268006683085 6671507427866725502506157)
          ·
            refine ⟨2501815285450022063439809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6671507427866725502506157 2501815285450022063439809)
            ·
              refine ⟨1876361464087516547579857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2501815285450022063439809 1876361464087516547579857)
              ·
                refine ⟨1407271098065637410684893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1876361464087516547579857 1407271098065637410684893)
                ·
                  refine ⟨527726661774614029006835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1407271098065637410684893 527726661774614029006835)
                  ·
                    refine ⟨791589992661921043510253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527726661774614029006835 791589992661921043510253)
                    ·
                      refine ⟨296846247248220391316345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791589992661921043510253 296846247248220391316345)
                      ·
                        rfl

theorem cell23_578106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_578106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578106 prefixEnd_578106 := by exact prefixLift 578106
  have htrace : WordTrace (prefixWord ++ tailWord_578106) baseStart_578106 baseEnd_578106 := by
    simpa [prefixWord, tailWord_578106, baseEnd_578106] using wordTrace_append hprefix tailTrace_578106
  have hstable : (prefixWord ++ tailWord_578106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578106).length < 2 ^ (prefixWord ++ tailWord_578106).sum := by decide
  have hdescent : baseEnd_578106 < baseStart_578106 := by decide
  rcases family_descends (prefixWord ++ tailWord_578106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578123 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 1, 1, 3]
def baseStart_578123 : Nat := 118140960795 + 578123 * 2 ^ 59
def prefixEnd_578123 : Nat := 4983230072969 + 3 ^ 40 * 578123 * 2
def baseEnd_578123 : Nat := 296854976419346824803767

theorem tailTrace_578123 : CollatzResearch.WordTrace tailWord_578123 prefixEnd_578123 296854976419346824803767 := by
  unfold tailWord_578123
  simp only [CollatzResearch.WordTrace]
  refine ⟨21085878084566581392771023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14057252056377720928514015 21085878084566581392771023)
  ·
    refine ⟨31628817126849872089156535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21085878084566581392771023 31628817126849872089156535)
    ·
      refine ⟨47443225690274808133734803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31628817126849872089156535 47443225690274808133734803)
      ·
        refine ⟨71164838535412212200602205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47443225690274808133734803 71164838535412212200602205)
        ·
          refine ⟨26686814450779579575225827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71164838535412212200602205 26686814450779579575225827)
          ·
            refine ⟨40030221676169369362838741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26686814450779579575225827 40030221676169369362838741)
            ·
              refine ⟨938208320535219594441533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 40030221676169369362838741 938208320535219594441533)
              ·
                refine ⟨351828120200707347915575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938208320535219594441533 351828120200707347915575)
                ·
                  refine ⟨527742180301061021873363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351828120200707347915575 527742180301061021873363)
                  ·
                    refine ⟨791613270451591532810045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527742180301061021873363 791613270451591532810045)
                    ·
                      refine ⟨296854976419346824803767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791613270451591532810045 296854976419346824803767)
                      ·
                        rfl

theorem cell23_578123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 1, 1, 3].length) (baseStart_578123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578123 prefixEnd_578123 := by exact prefixLift 578123
  have htrace : WordTrace (prefixWord ++ tailWord_578123) baseStart_578123 baseEnd_578123 := by
    simpa [prefixWord, tailWord_578123, baseEnd_578123] using wordTrace_append hprefix tailTrace_578123
  have hstable : (prefixWord ++ tailWord_578123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578123).length < 2 ^ (prefixWord ++ tailWord_578123).sum := by decide
  have hdescent : baseEnd_578123 < baseStart_578123 := by decide
  rcases family_descends (prefixWord ++ tailWord_578123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578140 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_578140 : Nat := 118140960795 + 578140 * 2 ^ 59
def prefixEnd_578140 : Nat := 4983230072969 + 3 ^ 40 * 578140 * 2
def baseEnd_578140 : Nat := 296863705590473258291189

theorem tailTrace_578140 : CollatzResearch.WordTrace tailWord_578140 prefixEnd_578140 296863705590473258291189 := by
  unfold tailWord_578140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10543249062752496648069937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14057665417003328864093249 10543249062752496648069937)
  ·
    refine ⟨7907436797064372486052453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10543249062752496648069937 7907436797064372486052453)
    ·
      refine ⟨1482644399449569841134835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7907436797064372486052453 1482644399449569841134835)
      ·
        refine ⟨2223966599174354761702253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1482644399449569841134835 2223966599174354761702253)
        ·
          refine ⟨833987474690383035638345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2223966599174354761702253 833987474690383035638345)
          ·
            refine ⟨625490606017787276728759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 833987474690383035638345 625490606017787276728759)
            ·
              refine ⟨938235909026680915093139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625490606017787276728759 938235909026680915093139)
              ·
                refine ⟨1407353863540021372639709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938235909026680915093139 1407353863540021372639709)
                ·
                  refine ⟨527757698827508014739891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1407353863540021372639709 527757698827508014739891)
                  ·
                    refine ⟨791636548241262022109837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527757698827508014739891 791636548241262022109837)
                    ·
                      refine ⟨296863705590473258291189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791636548241262022109837 296863705590473258291189)
                      ·
                        rfl

theorem cell23_578140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_578140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578140 prefixEnd_578140 := by exact prefixLift 578140
  have htrace : WordTrace (prefixWord ++ tailWord_578140) baseStart_578140 baseEnd_578140 := by
    simpa [prefixWord, tailWord_578140, baseEnd_578140] using wordTrace_append hprefix tailTrace_578140
  have hstable : (prefixWord ++ tailWord_578140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578140).length < 2 ^ (prefixWord ++ tailWord_578140).sum := by decide
  have hdescent : baseEnd_578140 < baseStart_578140 := by decide
  rcases family_descends (prefixWord ++ tailWord_578140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578179 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3]
def baseStart_578179 : Nat := 118140960795 + 578179 * 2 ^ 59
def prefixEnd_578179 : Nat := 4983230072969 + 3 ^ 40 * 578179 * 2
def baseEnd_578179 : Nat := 296883731335998605703509

theorem tailTrace_578179 : CollatzResearch.WordTrace tailWord_578179 prefixEnd_578179 296883731335998605703509 := by
  unfold tailWord_578179
  simp only [CollatzResearch.WordTrace]
  refine ⟨21087920572363702956809591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14058613714909135304539727 21087920572363702956809591)
  ·
    refine ⟨31631880858545554435214387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21087920572363702956809591 31631880858545554435214387)
    ·
      refine ⟨47447821287818331652821581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31631880858545554435214387 47447821287818331652821581)
      ·
        refine ⟨17792932982931874369808093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47447821287818331652821581 17792932982931874369808093)
        ·
          refine ⟨6672349868599452888678035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17792932982931874369808093 6672349868599452888678035)
          ·
            refine ⟨10008524802899179333017053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6672349868599452888678035 10008524802899179333017053)
            ·
              refine ⟨3753196801087192249881395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10008524802899179333017053 3753196801087192249881395)
              ·
                refine ⟨5629795201630788374822093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3753196801087192249881395 5629795201630788374822093)
                ·
                  refine ⟨2111173200611545640558285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5629795201630788374822093 2111173200611545640558285)
                  ·
                    refine ⟨791689950229329615209357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2111173200611545640558285 791689950229329615209357)
                    ·
                      refine ⟨296883731335998605703509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791689950229329615209357 296883731335998605703509)
                      ·
                        rfl

theorem cell23_578179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_578179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578179 prefixEnd_578179 := by exact prefixLift 578179
  have htrace : WordTrace (prefixWord ++ tailWord_578179) baseStart_578179 baseEnd_578179 := by
    simpa [prefixWord, tailWord_578179, baseEnd_578179] using wordTrace_append hprefix tailTrace_578179
  have hstable : (prefixWord ++ tailWord_578179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578179).length < 2 ^ (prefixWord ++ tailWord_578179).sum := by decide
  have hdescent : baseEnd_578179 < baseStart_578179 := by decide
  rcases family_descends (prefixWord ++ tailWord_578179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578183 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 1, 2, 3]
def baseStart_578183 : Nat := 118140960795 + 578183 * 2 ^ 59
def prefixEnd_578183 : Nat := 4983230072969 + 3 ^ 40 * 578183 * 2
def baseEnd_578183 : Nat := 296885785258616590053491

theorem tailTrace_578183 : CollatzResearch.WordTrace tailWord_578183 prefixEnd_578183 296885785258616590053491 := by
  unfold tailWord_578183
  simp only [CollatzResearch.WordTrace]
  refine ⟨21088066464349211639955203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14058710976232807759970135 21088066464349211639955203)
  ·
    refine ⟨31632099696523817459932805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21088066464349211639955203 31632099696523817459932805)
    ·
      refine ⟨5931018693098215773737401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31632099696523817459932805 5931018693098215773737401)
      ·
        refine ⟨4448264019823661830303051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5931018693098215773737401 4448264019823661830303051)
        ·
          refine ⟨6672396029735492745454577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4448264019823661830303051 6672396029735492745454577)
          ·
            refine ⟨5004297022301619559090933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6672396029735492745454577 5004297022301619559090933)
            ·
              refine ⟨469152845840776833664775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5004297022301619559090933 469152845840776833664775)
              ·
                refine ⟨703729268761165250497163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469152845840776833664775 703729268761165250497163)
                ·
                  refine ⟨1055593903141747875745745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703729268761165250497163 1055593903141747875745745)
                  ·
                    refine ⟨791695427356310906809309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1055593903141747875745745 791695427356310906809309)
                    ·
                      refine ⟨296885785258616590053491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791695427356310906809309 296885785258616590053491)
                      ·
                        rfl

theorem cell23_578183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_578183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578183 prefixEnd_578183 := by exact prefixLift 578183
  have htrace : WordTrace (prefixWord ++ tailWord_578183) baseStart_578183 baseEnd_578183 := by
    simpa [prefixWord, tailWord_578183, baseEnd_578183] using wordTrace_append hprefix tailTrace_578183
  have hstable : (prefixWord ++ tailWord_578183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578183).length < 2 ^ (prefixWord ++ tailWord_578183).sum := by decide
  have hdescent : baseEnd_578183 < baseStart_578183 := by decide
  rcases family_descends (prefixWord ++ tailWord_578183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578192 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_578192 : Nat := 118140960795 + 578192 * 2 ^ 59
def prefixEnd_578192 : Nat := 4983230072969 + 3 ^ 40 * 578192 * 2
def baseEnd_578192 : Nat := 296890406584507054840949

theorem tailTrace_578192 : CollatzResearch.WordTrace tailWord_578192 prefixEnd_578192 296890406584507054840949 := by
  unfold tailWord_578192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10544197360658303088516415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14058929814211070784688553 10544197360658303088516415)
  ·
    refine ⟨15816296040987454632774623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10544197360658303088516415 15816296040987454632774623)
    ·
      refine ⟨23724444061481181949161935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15816296040987454632774623 23724444061481181949161935)
      ·
        refine ⟨35586666092221772923742903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23724444061481181949161935 35586666092221772923742903)
        ·
          refine ⟨53379999138332659385614355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35586666092221772923742903 53379999138332659385614355)
          ·
            refine ⟨80069998707498989078421533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53379999138332659385614355 80069998707498989078421533)
            ·
              refine ⟨30026249515312120904408075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80069998707498989078421533 30026249515312120904408075)
              ·
                refine ⟨45039374272968181356612113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30026249515312120904408075 45039374272968181356612113)
                ·
                  refine ⟨33779530704726136017459085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45039374272968181356612113 33779530704726136017459085)
                  ·
                    refine ⟨12667324014272301006547157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33779530704726136017459085 12667324014272301006547157)
                    ·
                      refine ⟨296890406584507054840949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12667324014272301006547157 296890406584507054840949)
                      ·
                        rfl

theorem cell23_578192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_578192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578192 prefixEnd_578192 := by exact prefixLift 578192
  have htrace : WordTrace (prefixWord ++ tailWord_578192) baseStart_578192 baseEnd_578192 := by
    simpa [prefixWord, tailWord_578192, baseEnd_578192] using wordTrace_append hprefix tailTrace_578192
  have hstable : (prefixWord ++ tailWord_578192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578192).length < 2 ^ (prefixWord ++ tailWord_578192).sum := by decide
  have hdescent : baseEnd_578192 < baseStart_578192 := by decide
  rcases family_descends (prefixWord ++ tailWord_578192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578240 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2]
def baseStart_578240 : Nat := 118140960795 + 578240 * 2 ^ 59
def prefixEnd_578240 : Nat := 4983230072969 + 3 ^ 40 * 578240 * 2
def baseEnd_578240 : Nat := 296915053655922867040729

theorem tailTrace_578240 : CollatzResearch.WordTrace tailWord_578240 prefixEnd_578240 296915053655922867040729 := by
  unfold tailWord_578240
  simp only [CollatzResearch.WordTrace]
  refine ⟨10545072712571355187390087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14060096950095140249853449 10545072712571355187390087)
  ·
    refine ⟨15817609068857032781085131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10545072712571355187390087 15817609068857032781085131)
    ·
      refine ⟨23726413603285549171627697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15817609068857032781085131 23726413603285549171627697)
      ·
        refine ⟨17794810202464161878720773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23726413603285549171627697 17794810202464161878720773)
        ·
          refine ⟨3336526912962030352260145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17794810202464161878720773 3336526912962030352260145)
          ·
            refine ⟨2502395184721522764195109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3336526912962030352260145 2502395184721522764195109)
            ·
              refine ⟨469199097135285518286583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2502395184721522764195109 469199097135285518286583)
              ·
                refine ⟨703798645702928277429875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469199097135285518286583 703798645702928277429875)
                ·
                  refine ⟨1055697968554392416144813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 703798645702928277429875 1055697968554392416144813)
                  ·
                    refine ⟨395886738207897156054305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1055697968554392416144813 395886738207897156054305)
                    ·
                      refine ⟨296915053655922867040729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 395886738207897156054305 296915053655922867040729)
                      ·
                        rfl

theorem cell23_578240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 1, 3, 2].length) (baseStart_578240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578240 prefixEnd_578240 := by exact prefixLift 578240
  have htrace : WordTrace (prefixWord ++ tailWord_578240) baseStart_578240 baseEnd_578240 := by
    simpa [prefixWord, tailWord_578240, baseEnd_578240] using wordTrace_append hprefix tailTrace_578240
  have hstable : (prefixWord ++ tailWord_578240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578240).length < 2 ^ (prefixWord ++ tailWord_578240).sum := by decide
  have hdescent : baseEnd_578240 < baseStart_578240 := by decide
  rcases family_descends (prefixWord ++ tailWord_578240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578289 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_578289 : Nat := 118140960795 + 578289 * 2 ^ 59
def prefixEnd_578289 : Nat := 4983230072969 + 3 ^ 40 * 578289 * 2
def baseEnd_578289 : Nat := 98980071402664391776001

theorem tailTrace_578289 : CollatzResearch.WordTrace tailWord_578289 prefixEnd_578289 98980071402664391776001 := by
  unfold tailWord_578289
  simp only [CollatzResearch.WordTrace]
  refine ⟨21091932601965191743313921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14061288401310127828875947 21091932601965191743313921)
  ·
    refine ⟨15818949451473893807485441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21091932601965191743313921 15818949451473893807485441)
    ·
      refine ⟨11864212088605420355614081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15818949451473893807485441 11864212088605420355614081)
      ·
        refine ⟨8898159066454065266710561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11864212088605420355614081 8898159066454065266710561)
        ·
          refine ⟨6673619299840548950032921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8898159066454065266710561 6673619299840548950032921)
          ·
            refine ⟨5005214474880411712524691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6673619299840548950032921 5005214474880411712524691)
            ·
              refine ⟨7507821712320617568787037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5005214474880411712524691 7507821712320617568787037)
              ·
                refine ⟨2815433142120231588295139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7507821712320617568787037 2815433142120231588295139)
                ·
                  refine ⟨4223149713180347382442709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2815433142120231588295139 4223149713180347382442709)
                  ·
                    refine ⟨98980071402664391776001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4223149713180347382442709 98980071402664391776001)
                    ·
                      rfl

theorem cell23_578289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_578289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578289 prefixEnd_578289 := by exact prefixLift 578289
  have htrace : WordTrace (prefixWord ++ tailWord_578289) baseStart_578289 baseEnd_578289 := by
    simpa [prefixWord, tailWord_578289, baseEnd_578289] using wordTrace_append hprefix tailTrace_578289
  have hstable : (prefixWord ++ tailWord_578289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578289).length < 2 ^ (prefixWord ++ tailWord_578289).sum := by decide
  have hdescent : baseEnd_578289 < baseStart_578289 := by decide
  rcases family_descends (prefixWord ++ tailWord_578289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578339 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_578339 : Nat := 118140960795 + 578339 * 2 ^ 59
def prefixEnd_578339 : Nat := 4983230072969 + 3 ^ 40 * 578339 * 2
def baseEnd_578339 : Nat := 296965888240717979702773

theorem tailTrace_578339 : CollatzResearch.WordTrace tailWord_578339 prefixEnd_578339 296965888240717979702773 := by
  unfold tailWord_578339
  simp only [CollatzResearch.WordTrace]
  refine ⟨21093756251784050282634071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14062504167856033521756047 21093756251784050282634071)
  ·
    refine ⟨31640634377676075423951107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21093756251784050282634071 31640634377676075423951107)
    ·
      refine ⟨47460951566514113135926661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31640634377676075423951107 47460951566514113135926661)
      ·
        refine ⟨8898928418721396212986249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47460951566514113135926661 8898928418721396212986249)
        ·
          refine ⟨6674196314041047159739687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8898928418721396212986249 6674196314041047159739687)
          ·
            refine ⟨10011294471061570739609531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6674196314041047159739687 10011294471061570739609531)
            ·
              refine ⟨15016941706592356109414297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10011294471061570739609531 15016941706592356109414297)
              ·
                refine ⟨11262706279944267082060723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15016941706592356109414297 11262706279944267082060723)
                ·
                  refine ⟨16894059419916400623091085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11262706279944267082060723 16894059419916400623091085)
                  ·
                    refine ⟨6335272282468650233659157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16894059419916400623091085 6335272282468650233659157)
                    ·
                      refine ⟨296965888240717979702773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6335272282468650233659157 296965888240717979702773)
                      ·
                        rfl

theorem cell23_578339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_578339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578339 prefixEnd_578339 := by exact prefixLift 578339
  have htrace : WordTrace (prefixWord ++ tailWord_578339) baseStart_578339 baseEnd_578339 := by
    simpa [prefixWord, tailWord_578339, baseEnd_578339] using wordTrace_append hprefix tailTrace_578339
  have hstable : (prefixWord ++ tailWord_578339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578339).length < 2 ^ (prefixWord ++ tailWord_578339).sum := by decide
  have hdescent : baseEnd_578339 < baseStart_578339 := by decide
  rcases family_descends (prefixWord ++ tailWord_578339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578393 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 3]
def baseStart_578393 : Nat := 118140960795 + 578393 * 2 ^ 59
def prefixEnd_578393 : Nat := 4983230072969 + 3 ^ 40 * 578393 * 2
def baseEnd_578393 : Nat := 296993616196060768427525

theorem tailTrace_578393 : CollatzResearch.WordTrace tailWord_578393 prefixEnd_578393 296993616196060768427525 := by
  unfold tailWord_578393
  simp only [CollatzResearch.WordTrace]
  refine ⟨21095725793588417505099833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14063817195725611670066555 21095725793588417505099833)
  ·
    refine ⟨15821794345191313128824875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21095725793588417505099833 15821794345191313128824875)
    ·
      refine ⟨23732691517786969693237313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15821794345191313128824875 23732691517786969693237313)
      ·
        refine ⟨17799518638340227269927985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23732691517786969693237313 17799518638340227269927985)
        ·
          refine ⟨13349638978755170452445989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17799518638340227269927985 13349638978755170452445989)
          ·
            refine ⟨2503057308516594459833623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13349638978755170452445989 2503057308516594459833623)
            ·
              refine ⟨3754585962774891689750435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503057308516594459833623 3754585962774891689750435)
              ·
                refine ⟨5631878944162337534625653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3754585962774891689750435 5631878944162337534625653)
                ·
                  refine ⟨527988651015219143871155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5631878944162337534625653 527988651015219143871155)
                  ·
                    refine ⟨791982976522828715806733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527988651015219143871155 791982976522828715806733)
                    ·
                      refine ⟨296993616196060768427525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 791982976522828715806733 296993616196060768427525)
                      ·
                        rfl

theorem cell23_578393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_578393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578393 prefixEnd_578393 := by exact prefixLift 578393
  have htrace : WordTrace (prefixWord ++ tailWord_578393) baseStart_578393 baseEnd_578393 := by
    simpa [prefixWord, tailWord_578393, baseEnd_578393] using wordTrace_append hprefix tailTrace_578393
  have hstable : (prefixWord ++ tailWord_578393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578393).length < 2 ^ (prefixWord ++ tailWord_578393).sum := by decide
  have hdescent : baseEnd_578393 < baseStart_578393 := by decide
  rcases family_descends (prefixWord ++ tailWord_578393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578434 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_578434 : Nat := 118140960795 + 578434 * 2 ^ 59
def prefixEnd_578434 : Nat := 4983230072969 + 3 ^ 40 * 578434 * 2
def baseEnd_578434 : Nat := 33001629878099456446093

theorem tailTrace_578434 : CollatzResearch.WordTrace tailWord_578434 prefixEnd_578434 33001629878099456446093 := by
  unfold tailWord_578434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274305296609970376835589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14064814124293254338228237 5274305296609970376835589)
  ·
    refine ⟨988932243114369445656673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5274305296609970376835589 988932243114369445656673)
    ·
      refine ⟨741699182335777084242505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 988932243114369445656673 741699182335777084242505)
      ·
        refine ⟨556274386751832813181879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 741699182335777084242505 556274386751832813181879)
        ·
          refine ⟨834411580127749219772819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556274386751832813181879 834411580127749219772819)
          ·
            refine ⟨1251617370191623829659229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834411580127749219772819 1251617370191623829659229)
            ·
              refine ⟨469356513821858936122211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1251617370191623829659229 469356513821858936122211)
              ·
                refine ⟨704034770732788404183317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469356513821858936122211 704034770732788404183317)
                ·
                  refine ⟨33001629878099456446093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 704034770732788404183317 33001629878099456446093)
                  ·
                    rfl

theorem cell23_578434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_578434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578434 prefixEnd_578434 := by exact prefixLift 578434
  have htrace : WordTrace (prefixWord ++ tailWord_578434) baseStart_578434 baseEnd_578434 := by
    simpa [prefixWord, tailWord_578434, baseEnd_578434] using wordTrace_append hprefix tailTrace_578434
  have hstable : (prefixWord ++ tailWord_578434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578434).length < 2 ^ (prefixWord ++ tailWord_578434).sum := by decide
  have hdescent : baseEnd_578434 < baseStart_578434 := by decide
  rcases family_descends (prefixWord ++ tailWord_578434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578443 : List Nat := [1, 1, 1, 1, 4, 2, 2, 5, 2, 4]
def baseStart_578443 : Nat := 118140960795 + 578443 * 2 ^ 59
def prefixEnd_578443 : Nat := 4983230072969 + 3 ^ 40 * 578443 * 2
def baseEnd_578443 : Nat := 99006430076261857600765

theorem tailTrace_578443 : CollatzResearch.WordTrace tailWord_578443 prefixEnd_578443 99006430076261857600765 := by
  unfold tailWord_578443
  simp only [CollatzResearch.WordTrace]
  refine ⟨21097549443407276044419983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14065032962271517362946655 21097549443407276044419983)
  ·
    refine ⟨31646324165110914066629975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21097549443407276044419983 31646324165110914066629975)
    ·
      refine ⟨47469486247666371099944963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31646324165110914066629975 47469486247666371099944963)
      ·
        refine ⟨71204229371499556649917445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47469486247666371099944963 71204229371499556649917445)
        ·
          refine ⟨13350793007156166871859521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71204229371499556649917445 13350793007156166871859521)
          ·
            refine ⟨10013094755367125153894641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13350793007156166871859521 10013094755367125153894641)
            ·
              refine ⟨7509821066525343865420981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10013094755367125153894641 7509821066525343865420981)
              ·
                refine ⟨704045724986750987383217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7509821066525343865420981 704045724986750987383217)
                ·
                  refine ⟨528034293740063240537413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704045724986750987383217 528034293740063240537413)
                  ·
                    refine ⟨99006430076261857600765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528034293740063240537413 99006430076261857600765)
                    ·
                      rfl

theorem cell23_578443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 4].length) (baseStart_578443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578443 prefixEnd_578443 := by exact prefixLift 578443
  have htrace : WordTrace (prefixWord ++ tailWord_578443) baseStart_578443 baseEnd_578443 := by
    simpa [prefixWord, tailWord_578443, baseEnd_578443] using wordTrace_append hprefix tailTrace_578443
  have hstable : (prefixWord ++ tailWord_578443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578443).length < 2 ^ (prefixWord ++ tailWord_578443).sum := by decide
  have hdescent : baseEnd_578443 < baseStart_578443 := by decide
  rcases family_descends (prefixWord ++ tailWord_578443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578454 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_578454 : Nat := 118140960795 + 578454 * 2 ^ 59
def prefixEnd_578454 : Nat := 4983230072969 + 3 ^ 40 * 578454 * 2
def baseEnd_578454 : Nat := 297024938515985029764745

theorem tailTrace_578454 : CollatzResearch.WordTrace tailWord_578454 prefixEnd_578454 297024938515985029764745 := by
  unfold tailWord_578454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318621915397964057691901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14065300430911616615380277 1318621915397964057691901)
  ·
    refine ⟨494483218274236521634463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1318621915397964057691901 494483218274236521634463)
    ·
      refine ⟨741724827411354782451695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494483218274236521634463 741724827411354782451695)
      ·
        refine ⟨1112587241117032173677543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741724827411354782451695 1112587241117032173677543)
        ·
          refine ⟨1668880861675548260516315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112587241117032173677543 1668880861675548260516315)
          ·
            refine ⟨2503321292513322390774473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668880861675548260516315 2503321292513322390774473)
            ·
              refine ⟨1877490969384991793080855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2503321292513322390774473 1877490969384991793080855)
              ·
                refine ⟨2816236454077487689621283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877490969384991793080855 2816236454077487689621283)
                ·
                  refine ⟨4224354681116231534431925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2816236454077487689621283 4224354681116231534431925)
                  ·
                    refine ⟨396033251354646706352993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4224354681116231534431925 396033251354646706352993)
                    ·
                      refine ⟨297024938515985029764745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396033251354646706352993 297024938515985029764745)
                      ·
                        rfl

theorem cell23_578454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_578454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578454 prefixEnd_578454 := by exact prefixLift 578454
  have htrace : WordTrace (prefixWord ++ tailWord_578454) baseStart_578454 baseEnd_578454 := by
    simpa [prefixWord, tailWord_578454, baseEnd_578454] using wordTrace_append hprefix tailTrace_578454
  have hstable : (prefixWord ++ tailWord_578454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578454).length < 2 ^ (prefixWord ++ tailWord_578454).sum := by decide
  have hdescent : baseEnd_578454 < baseStart_578454 := by decide
  rcases family_descends (prefixWord ++ tailWord_578454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578504 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3]
def baseStart_578504 : Nat := 118140960795 + 578504 * 2 ^ 59
def prefixEnd_578504 : Nat := 4983230072969 + 3 ^ 40 * 578504 * 2
def baseEnd_578504 : Nat := 297050612548709834139515

theorem tailTrace_578504 : CollatzResearch.WordTrace tailWord_578504 prefixEnd_578504 297050612548709834139515 := by
  unfold tailWord_578504
  simp only [CollatzResearch.WordTrace]
  refine ⟨10549887148093141731195283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14066516197457522308260377 10549887148093141731195283)
  ·
    refine ⟨15824830722139712596792925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10549887148093141731195283 15824830722139712596792925)
    ·
      refine ⟨5934311520802392223797347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15824830722139712596792925 5934311520802392223797347)
      ·
        refine ⟨8901467281203588335696021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5934311520802392223797347 8901467281203588335696021)
        ·
          refine ⟨417256278806418203235751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8901467281203588335696021 417256278806418203235751)
          ·
            refine ⟨625884418209627304853627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417256278806418203235751 625884418209627304853627)
            ·
              refine ⟨938826627314440957280441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625884418209627304853627 938826627314440957280441)
              ·
                refine ⟨704119970485830717960331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 938826627314440957280441 704119970485830717960331)
                ·
                  refine ⟨1056179955728746076940497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704119970485830717960331 1056179955728746076940497)
                  ·
                    refine ⟨792134966796559557705373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056179955728746076940497 792134966796559557705373)
                    ·
                      refine ⟨297050612548709834139515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 792134966796559557705373 297050612548709834139515)
                      ·
                        rfl

theorem cell23_578504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_578504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578504 prefixEnd_578504 := by exact prefixLift 578504
  have htrace : WordTrace (prefixWord ++ tailWord_578504) baseStart_578504 baseEnd_578504 := by
    simpa [prefixWord, tailWord_578504, baseEnd_578504] using wordTrace_append hprefix tailTrace_578504
  have hstable : (prefixWord ++ tailWord_578504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578504).length < 2 ^ (prefixWord ++ tailWord_578504).sum := by decide
  have hdescent : baseEnd_578504 < baseStart_578504 := by decide
  rcases family_descends (prefixWord ++ tailWord_578504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578506 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_578506 : Nat := 118140960795 + 578506 * 2 ^ 59
def prefixEnd_578506 : Nat := 4983230072969 + 3 ^ 40 * 578506 * 2
def baseEnd_578506 : Nat := 297051639510018826314505

theorem tailTrace_578506 : CollatzResearch.WordTrace tailWord_578506 prefixEnd_578506 297051639510018826314505 := by
  unfold tailWord_578506
  simp only [CollatzResearch.WordTrace]
  refine ⟨5274961810544759450990843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14066564828119358535975581 5274961810544759450990843)
  ·
    refine ⟨7912442715817139176486265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5274961810544759450990843 7912442715817139176486265)
    ·
      refine ⟨5934332036862854382364699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7912442715817139176486265 5934332036862854382364699)
      ·
        refine ⟨8901498055294281573547049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5934332036862854382364699 8901498055294281573547049)
        ·
          refine ⟨6676123541470711180160287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8901498055294281573547049 6676123541470711180160287)
          ·
            refine ⟨10014185312206066770240431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6676123541470711180160287 10014185312206066770240431)
            ·
              refine ⟨15021277968309100155360647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10014185312206066770240431 15021277968309100155360647)
              ·
                refine ⟨22531916952463650233040971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15021277968309100155360647 22531916952463650233040971)
                ·
                  refine ⟨33797875428695475349561457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22531916952463650233040971 33797875428695475349561457)
                  ·
                    refine ⟨25348406571521606512171093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33797875428695475349561457 25348406571521606512171093)
                    ·
                      refine ⟨297051639510018826314505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 25348406571521606512171093 297051639510018826314505)
                      ·
                        rfl

theorem cell23_578506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_578506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578506 prefixEnd_578506 := by exact prefixLift 578506
  have htrace : WordTrace (prefixWord ++ tailWord_578506) baseStart_578506 baseEnd_578506 := by
    simpa [prefixWord, tailWord_578506, baseEnd_578506] using wordTrace_append hprefix tailTrace_578506
  have hstable : (prefixWord ++ tailWord_578506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578506).length < 2 ^ (prefixWord ++ tailWord_578506).sum := by decide
  have hdescent : baseEnd_578506 < baseStart_578506 := by decide
  rcases family_descends (prefixWord ++ tailWord_578506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578543 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_578543 : Nat := 118140960795 + 578543 * 2 ^ 59
def prefixEnd_578543 : Nat := 4983230072969 + 3 ^ 40 * 578543 * 2
def baseEnd_578543 : Nat := 297070638294235181551835

theorem tailTrace_578543 : CollatzResearch.WordTrace tailWord_578543 prefixEnd_578543 297070638294235181551835 := by
  unfold tailWord_578543
  simp only [CollatzResearch.WordTrace]
  refine ⟨21101196743044993123060283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14067464495363328748706855 21101196743044993123060283)
  ·
    refine ⟨31651795114567489684590425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21101196743044993123060283 31651795114567489684590425)
    ·
      refine ⟨23738846335925617263442819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31651795114567489684590425 23738846335925617263442819)
      ·
        refine ⟨35608269503888425895164229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23738846335925617263442819 35608269503888425895164229)
        ·
          refine ⟨6676550531979079855343293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35608269503888425895164229 6676550531979079855343293)
          ·
            refine ⟨2503706449492154945753735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6676550531979079855343293 2503706449492154945753735)
            ·
              refine ⟨3755559674238232418630603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2503706449492154945753735 3755559674238232418630603)
              ·
                refine ⟨5633339511357348627945905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3755559674238232418630603 5633339511357348627945905)
                ·
                  refine ⟨4225004633518011470959429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5633339511357348627945905 4225004633518011470959429)
                  ·
                    refine ⟨792188368784627150804893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4225004633518011470959429 792188368784627150804893)
                    ·
                      refine ⟨297070638294235181551835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 792188368784627150804893 297070638294235181551835)
                      ·
                        rfl

theorem cell23_578543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_578543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578543 prefixEnd_578543 := by exact prefixLift 578543
  have htrace : WordTrace (prefixWord ++ tailWord_578543) baseStart_578543 baseEnd_578543 := by
    simpa [prefixWord, tailWord_578543, baseEnd_578543] using wordTrace_append hprefix tailTrace_578543
  have hstable : (prefixWord ++ tailWord_578543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578543).length < 2 ^ (prefixWord ++ tailWord_578543).sum := by decide
  have hdescent : baseEnd_578543 < baseStart_578543 := by decide
  rcases family_descends (prefixWord ++ tailWord_578543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578550 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_578550 : Nat := 118140960795 + 578550 * 2 ^ 59
def prefixEnd_578550 : Nat := 4983230072969 + 3 ^ 40 * 578550 * 2
def baseEnd_578550 : Nat := 99024744219605551388101

theorem tailTrace_578550 : CollatzResearch.WordTrace tailWord_578550 prefixEnd_578550 99024744219605551388101 := by
  unfold tailWord_578550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318840753376227082410319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14067634702679755545710069 1318840753376227082410319)
  ·
    refine ⟨1978261130064340623615479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318840753376227082410319 1978261130064340623615479)
    ·
      refine ⟨2967391695096510935423219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978261130064340623615479 2967391695096510935423219)
      ·
        refine ⟨4451087542644766403134829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967391695096510935423219 4451087542644766403134829)
        ·
          refine ⟨1669157828491787401175561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4451087542644766403134829 1669157828491787401175561)
          ·
            refine ⟨1251868371368840550881671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1669157828491787401175561 1251868371368840550881671)
            ·
              refine ⟨1877802557053260826322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251868371368840550881671 1877802557053260826322507)
              ·
                refine ⟨2816703835579891239483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877802557053260826322507 2816703835579891239483761)
                ·
                  refine ⟨2112527876684918429612821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816703835579891239483761 2112527876684918429612821)
                  ·
                    refine ⟨99024744219605551388101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2112527876684918429612821 99024744219605551388101)
                    ·
                      rfl

theorem cell23_578550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_578550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578550 prefixEnd_578550 := by exact prefixLift 578550
  have htrace : WordTrace (prefixWord ++ tailWord_578550) baseStart_578550 baseEnd_578550 := by
    simpa [prefixWord, tailWord_578550, baseEnd_578550] using wordTrace_append hprefix tailTrace_578550
  have hstable : (prefixWord ++ tailWord_578550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578550).length < 2 ^ (prefixWord ++ tailWord_578550).sum := by decide
  have hdescent : baseEnd_578550 < baseStart_578550 := by decide
  rcases family_descends (prefixWord ++ tailWord_578550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578553 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_578553 : Nat := 118140960795 + 578553 * 2 ^ 59
def prefixEnd_578553 : Nat := 4983230072969 + 3 ^ 40 * 578553 * 2
def baseEnd_578553 : Nat := 297075773100780142426789

theorem tailTrace_578553 : CollatzResearch.WordTrace tailWord_578553 prefixEnd_578553 297075773100780142426789 := by
  unfold tailWord_578553
  simp only [CollatzResearch.WordTrace]
  refine ⟨21101561473008764830924313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14067707648672509887282875 21101561473008764830924313)
  ·
    refine ⟨15826171104756573623193235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21101561473008764830924313 15826171104756573623193235)
    ·
      refine ⟨23739256657134860434789853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15826171104756573623193235 23739256657134860434789853)
      ·
        refine ⟨8902221246425572663046195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23739256657134860434789853 8902221246425572663046195)
        ·
          refine ⟨13353331869638358994569293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8902221246425572663046195 13353331869638358994569293)
          ·
            refine ⟨5007499451114384622963485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13353331869638358994569293 5007499451114384622963485)
            ·
              refine ⟨1877812294167894233611307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5007499451114384622963485 1877812294167894233611307)
              ·
                refine ⟨2816718441251841350416961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1877812294167894233611307 2816718441251841350416961)
                ·
                  refine ⟨2112538830938881012812721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2816718441251841350416961 2112538830938881012812721)
                  ·
                    refine ⟨1584404123204160759609541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2112538830938881012812721 1584404123204160759609541)
                    ·
                      refine ⟨297075773100780142426789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1584404123204160759609541 297075773100780142426789)
                      ·
                        rfl

theorem cell23_578553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_578553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578553 prefixEnd_578553 := by exact prefixLift 578553
  have htrace : WordTrace (prefixWord ++ tailWord_578553) baseStart_578553 baseEnd_578553 := by
    simpa [prefixWord, tailWord_578553, baseEnd_578553] using wordTrace_append hprefix tailTrace_578553
  have hstable : (prefixWord ++ tailWord_578553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578553).length < 2 ^ (prefixWord ++ tailWord_578553).sum := by decide
  have hdescent : baseEnd_578553 < baseStart_578553 := by decide
  rcases family_descends (prefixWord ++ tailWord_578553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578578 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_578578 : Nat := 118140960795 + 578578 * 2 ^ 59
def prefixEnd_578578 : Nat := 4983230072969 + 3 ^ 40 * 578578 * 2
def baseEnd_578578 : Nat := 297088610117142544614175

theorem tailTrace_578578 : CollatzResearch.WordTrace tailWord_578578 prefixEnd_578578 297088610117142544614175 := by
  unfold tailWord_578578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275618324479548525146097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14068315531945462733722925 5275618324479548525146097)
  ·
    refine ⟨3956713743359661393859573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5275618324479548525146097 3956713743359661393859573)
    ·
      refine ⟨370941913439968255674335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3956713743359661393859573 370941913439968255674335)
      ·
        refine ⟨556412870159952383511503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370941913439968255674335 556412870159952383511503)
        ·
          refine ⟨834619305239928575267255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556412870159952383511503 834619305239928575267255)
          ·
            refine ⟨1251928957859892862900883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834619305239928575267255 1251928957859892862900883)
            ·
              refine ⟨1877893436789839294351325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1251928957859892862900883 1877893436789839294351325)
              ·
                refine ⟨704210038796189735381747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1877893436789839294351325 704210038796189735381747)
                ·
                  refine ⟨1056315058194284603072621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704210038796189735381747 1056315058194284603072621)
                  ·
                    refine ⟨396118146822856726152233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056315058194284603072621 396118146822856726152233)
                    ·
                      refine ⟨297088610117142544614175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396118146822856726152233 297088610117142544614175)
                      ·
                        rfl

theorem cell23_578578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_578578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578578 prefixEnd_578578 := by exact prefixLift 578578
  have htrace : WordTrace (prefixWord ++ tailWord_578578) baseStart_578578 baseEnd_578578 := by
    simpa [prefixWord, tailWord_578578, baseEnd_578578] using wordTrace_append hprefix tailTrace_578578
  have hstable : (prefixWord ++ tailWord_578578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578578).length < 2 ^ (prefixWord ++ tailWord_578578).sum := by decide
  have hdescent : baseEnd_578578 < baseStart_578578 := by decide
  rcases family_descends (prefixWord ++ tailWord_578578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578654 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_578654 : Nat := 118140960795 + 578654 * 2 ^ 59
def prefixEnd_578654 : Nat := 4983230072969 + 3 ^ 40 * 578654 * 2
def baseEnd_578654 : Nat := 297127634646884247263825

theorem tailTrace_578654 : CollatzResearch.WordTrace tailWord_578654 prefixEnd_578654 297127634646884247263825 := by
  unfold tailWord_578654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638155655705357385043877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14070163497095239386900677 2638155655705357385043877)
  ·
    refine ⟨494654185444754509695727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2638155655705357385043877 494654185444754509695727)
    ·
      refine ⟨741981278167131764543591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494654185444754509695727 741981278167131764543591)
      ·
        refine ⟨1112971917250697646815387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741981278167131764543591 1112971917250697646815387)
        ·
          refine ⟨1669457875876046470223081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112971917250697646815387 1669457875876046470223081)
          ·
            refine ⟨1252093406907034852667311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1669457875876046470223081 1252093406907034852667311)
            ·
              refine ⟨1878140110360552279000967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252093406907034852667311 1878140110360552279000967)
              ·
                refine ⟨2817210165540828418501451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878140110360552279000967 2817210165540828418501451)
                ·
                  refine ⟨4225815248311242627752177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2817210165540828418501451 4225815248311242627752177)
                  ·
                    refine ⟨3169361436233431970814133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4225815248311242627752177 3169361436233431970814133)
                    ·
                      refine ⟨297127634646884247263825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3169361436233431970814133 297127634646884247263825)
                      ·
                        rfl

theorem cell23_578654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_578654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578654 prefixEnd_578654 := by exact prefixLift 578654
  have htrace : WordTrace (prefixWord ++ tailWord_578654) baseStart_578654 baseEnd_578654 := by
    simpa [prefixWord, tailWord_578654, baseEnd_578654] using wordTrace_append hprefix tailTrace_578654
  have hstable : (prefixWord ++ tailWord_578654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578654).length < 2 ^ (prefixWord ++ tailWord_578654).sum := by decide
  have hdescent : baseEnd_578654 < baseStart_578654 := by decide
  rcases family_descends (prefixWord ++ tailWord_578654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578657 : List Nat := [1, 2, 3, 1, 1, 2, 2, 6, 1, 4]
def baseStart_578657 : Nat := 118140960795 + 578657 * 2 ^ 59
def prefixEnd_578657 : Nat := 4983230072969 + 3 ^ 40 * 578657 * 2
def baseEnd_578657 : Nat := 99043058362949245175437

theorem tailTrace_578657 : CollatzResearch.WordTrace tailWord_578657 prefixEnd_578657 99043058362949245175437 := by
  unfold tailWord_578657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21105354664631990592710225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14070236443087993728473483 21105354664631990592710225)
  ·
    refine ⟨15829015998473992944532669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21105354664631990592710225 15829015998473992944532669)
    ·
      refine ⟨5935880999427747354199751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15829015998473992944532669 5935880999427747354199751)
      ·
        refine ⟨8903821499141621031299627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5935880999427747354199751 8903821499141621031299627)
        ·
          refine ⟨13355732248712431546949441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8903821499141621031299627 13355732248712431546949441)
          ·
            refine ⟨10016799186534323660212081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13355732248712431546949441 10016799186534323660212081)
            ·
              refine ⟨7512599389900742745159061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10016799186534323660212081 7512599389900742745159061)
              ·
                refine ⟨352153096401597316179331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7512599389900742745159061 352153096401597316179331)
                ·
                  refine ⟨528229644602395974268997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352153096401597316179331 528229644602395974268997)
                  ·
                    refine ⟨99043058362949245175437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528229644602395974268997 99043058362949245175437)
                    ·
                      rfl

theorem cell23_578657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_578657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578657 prefixEnd_578657 := by exact prefixLift 578657
  have htrace : WordTrace (prefixWord ++ tailWord_578657) baseStart_578657 baseEnd_578657 := by
    simpa [prefixWord, tailWord_578657, baseEnd_578657] using wordTrace_append hprefix tailTrace_578657
  have hstable : (prefixWord ++ tailWord_578657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578657).length < 2 ^ (prefixWord ++ tailWord_578657).sum := by decide
  have hdescent : baseEnd_578657 < baseStart_578657 := by decide
  rcases family_descends (prefixWord ++ tailWord_578657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578700 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_578700 : Nat := 118140960795 + 578700 * 2 ^ 59
def prefixEnd_578700 : Nat := 4983230072969 + 3 ^ 40 * 578700 * 2
def baseEnd_578700 : Nat := 99050418252330355762871

theorem tailTrace_578700 : CollatzResearch.WordTrace tailWord_578700 prefixEnd_578700 99050418252330355762871 := by
  unfold tailWord_578700
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553461501738104468262777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14071282002317472624350369 10553461501738104468262777)
  ·
    refine ⟨7915096126303578351197083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10553461501738104468262777 7915096126303578351197083)
    ·
      refine ⟨11872644189455367526795625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7915096126303578351197083 11872644189455367526795625)
      ·
        refine ⟨8904483142091525645096719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11872644189455367526795625 8904483142091525645096719)
        ·
          refine ⟨13356724713137288467645079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8904483142091525645096719 13356724713137288467645079)
          ·
            refine ⟨20035087069705932701467619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13356724713137288467645079 20035087069705932701467619)
            ·
              refine ⟨30052630604558899052201429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20035087069705932701467619 30052630604558899052201429)
              ·
                refine ⟨704358529794349196535971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30052630604558899052201429 704358529794349196535971)
                ·
                  refine ⟨1056537794691523794803957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704358529794349196535971 1056537794691523794803957)
                  ·
                    refine ⟨99050418252330355762871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1056537794691523794803957 99050418252330355762871)
                    ·
                      rfl

theorem cell23_578700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_578700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578700 prefixEnd_578700 := by exact prefixLift 578700
  have htrace : WordTrace (prefixWord ++ tailWord_578700) baseStart_578700 baseEnd_578700 := by
    simpa [prefixWord, tailWord_578700, baseEnd_578700] using wordTrace_append hprefix tailTrace_578700
  have hstable : (prefixWord ++ tailWord_578700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578700).length < 2 ^ (prefixWord ++ tailWord_578700).sum := by decide
  have hdescent : baseEnd_578700 < baseStart_578700 := by decide
  rcases family_descends (prefixWord ++ tailWord_578700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578703 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_578703 : Nat := 118140960795 + 578703 * 2 ^ 59
def prefixEnd_578703 : Nat := 4983230072969 + 3 ^ 40 * 578703 * 2
def baseEnd_578703 : Nat := 297152795198954555551099

theorem tailTrace_578703 : CollatzResearch.WordTrace tailWord_578703 prefixEnd_578703 297152795198954555551099 := by
  unfold tailWord_578703
  simp only [CollatzResearch.WordTrace]
  refine ⟨21107032422465340448884763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14071354948310226965923175 21107032422465340448884763)
  ·
    refine ⟨31660548633698010673327145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21107032422465340448884763 31660548633698010673327145)
    ·
      refine ⟨23745411475273508004995359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31660548633698010673327145 23745411475273508004995359)
      ·
        refine ⟨35618117212910262007493039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23745411475273508004995359 35618117212910262007493039)
        ·
          refine ⟨53427175819365393011239559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35618117212910262007493039 53427175819365393011239559)
          ·
            refine ⟨80140763729048089516859339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53427175819365393011239559 80140763729048089516859339)
            ·
              refine ⟨120211145593572134275289009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80140763729048089516859339 120211145593572134275289009)
              ·
                refine ⟨90158359195179100706466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120211145593572134275289009 90158359195179100706466757)
                ·
                  refine ⟨16904692349096081382462517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90158359195179100706466757 16904692349096081382462517)
                  ·
                    refine ⟨1584814907727757629605861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16904692349096081382462517 1584814907727757629605861)
                    ·
                      refine ⟨297152795198954555551099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1584814907727757629605861 297152795198954555551099)
                      ·
                        rfl

theorem cell23_578703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_578703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578703 prefixEnd_578703 := by exact prefixLift 578703
  have htrace : WordTrace (prefixWord ++ tailWord_578703) baseStart_578703 baseEnd_578703 := by
    simpa [prefixWord, tailWord_578703, baseEnd_578703] using wordTrace_append hprefix tailTrace_578703
  have hstable : (prefixWord ++ tailWord_578703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578703).length < 2 ^ (prefixWord ++ tailWord_578703).sum := by decide
  have hdescent : baseEnd_578703 < baseStart_578703 := by decide
  rcases family_descends (prefixWord ++ tailWord_578703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578707 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 2, 3, 2]
def baseStart_578707 : Nat := 118140960795 + 578707 * 2 ^ 59
def prefixEnd_578707 : Nat := 4983230072969 + 3 ^ 40 * 578707 * 2
def baseEnd_578707 : Nat := 297154849121572539901081

theorem tailTrace_578707 : CollatzResearch.WordTrace tailWord_578707 prefixEnd_578707 297154849121572539901081 := by
  unfold tailWord_578707
  simp only [CollatzResearch.WordTrace]
  refine ⟨21107178314450849132030375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14071452209633899421353583 21107178314450849132030375)
  ·
    refine ⟨31660767471676273698045563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21107178314450849132030375 31660767471676273698045563)
    ·
      refine ⟨47491151207514410547068345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31660767471676273698045563 47491151207514410547068345)
      ·
        refine ⟨35618363405635807910301259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47491151207514410547068345 35618363405635807910301259)
        ·
          refine ⟨53427545108453711865451889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35618363405635807910301259 53427545108453711865451889)
          ·
            refine ⟨40070658831340283899088917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53427545108453711865451889 40070658831340283899088917)
            ·
              refine ⟨1878312132719075807769793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40070658831340283899088917 1878312132719075807769793)
              ·
                refine ⟨1408734099539306855827345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878312132719075807769793 1408734099539306855827345)
                ·
                  refine ⟨1056550574654480141870509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1408734099539306855827345 1056550574654480141870509)
                  ·
                    refine ⟨396206465495430053201441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056550574654480141870509 396206465495430053201441)
                    ·
                      refine ⟨297154849121572539901081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396206465495430053201441 297154849121572539901081)
                      ·
                        rfl

theorem cell23_578707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3, 2].length) (baseStart_578707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578707 prefixEnd_578707 := by exact prefixLift 578707
  have htrace : WordTrace (prefixWord ++ tailWord_578707) baseStart_578707 baseEnd_578707 := by
    simpa [prefixWord, tailWord_578707, baseEnd_578707] using wordTrace_append hprefix tailTrace_578707
  have hstable : (prefixWord ++ tailWord_578707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578707).length < 2 ^ (prefixWord ++ tailWord_578707).sum := by decide
  have hdescent : baseEnd_578707 < baseStart_578707 := by decide
  rcases family_descends (prefixWord ++ tailWord_578707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578720 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_578720 : Nat := 118140960795 + 578720 * 2 ^ 59
def prefixEnd_578720 : Nat := 4983230072969 + 3 ^ 40 * 578720 * 2
def baseEnd_578720 : Nat := 297161524370080989038521

theorem tailTrace_578720 : CollatzResearch.WordTrace tailWord_578720 prefixEnd_578720 297161524370080989038521 := by
  unfold tailWord_578720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10553826231701876176126807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14071768308935834901502409 10553826231701876176126807)
  ·
    refine ⟨15830739347552814264190211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10553826231701876176126807 15830739347552814264190211)
    ·
      refine ⟨23746109021329221396285317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15830739347552814264190211 23746109021329221396285317)
      ·
        refine ⟨4452395441499229011803497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23746109021329221396285317 4452395441499229011803497)
        ·
          refine ⟨3339296581124421758852623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4452395441499229011803497 3339296581124421758852623)
          ·
            refine ⟨5008944871686632638278935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3339296581124421758852623 5008944871686632638278935)
            ·
              refine ⟨7513417307529948957418403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5008944871686632638278935 7513417307529948957418403)
              ·
                refine ⟨11270125961294923436127605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7513417307529948957418403 11270125961294923436127605)
                ·
                  refine ⟨1056574308871399072136963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11270125961294923436127605 1056574308871399072136963)
                  ·
                    refine ⟨1584861463307098608205445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056574308871399072136963 1584861463307098608205445)
                    ·
                      refine ⟨297161524370080989038521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1584861463307098608205445 297161524370080989038521)
                      ·
                        rfl

theorem cell23_578720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_578720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578720 prefixEnd_578720 := by exact prefixLift 578720
  have htrace : WordTrace (prefixWord ++ tailWord_578720) baseStart_578720 baseEnd_578720 := by
    simpa [prefixWord, tailWord_578720, baseEnd_578720] using wordTrace_append hprefix tailTrace_578720
  have hstable : (prefixWord ++ tailWord_578720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578720).length < 2 ^ (prefixWord ++ tailWord_578720).sum := by decide
  have hdescent : baseEnd_578720 < baseStart_578720 := by decide
  rcases family_descends (prefixWord ++ tailWord_578720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578737 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_578737 : Nat := 118140960795 + 578737 * 2 ^ 59
def prefixEnd_578737 : Nat := 4983230072969 + 3 ^ 40 * 578737 * 2
def baseEnd_578737 : Nat := 297170253541207422525943

theorem tailTrace_578737 : CollatzResearch.WordTrace tailWord_578737 prefixEnd_578737 297170253541207422525943 := by
  unfold tailWord_578737
  simp only [CollatzResearch.WordTrace]
  refine ⟨21108272504342164255622465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14072181669561442837081643 21108272504342164255622465)
  ·
    refine ⟨15831204378256623191716849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21108272504342164255622465 15831204378256623191716849)
    ·
      refine ⟨11873403283692467393787637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15831204378256623191716849 11873403283692467393787637)
      ·
        refine ⟨1113131557846168818167591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11873403283692467393787637 1113131557846168818167591)
        ·
          refine ⟨1669697336769253227251387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113131557846168818167591 1669697336769253227251387)
          ·
            refine ⟨2504546005153879840877081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1669697336769253227251387 2504546005153879840877081)
            ·
              refine ⟨1878409503865409880657811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2504546005153879840877081 1878409503865409880657811)
              ·
                refine ⟨2817614255798114820986717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878409503865409880657811 2817614255798114820986717)
                ·
                  refine ⟨1056605345924293057870019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2817614255798114820986717 1056605345924293057870019)
                  ·
                    refine ⟨1584908018886439586805029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1056605345924293057870019 1584908018886439586805029)
                    ·
                      refine ⟨297170253541207422525943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1584908018886439586805029 297170253541207422525943)
                      ·
                        rfl

theorem cell23_578737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_578737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578737 prefixEnd_578737 := by exact prefixLift 578737
  have htrace : WordTrace (prefixWord ++ tailWord_578737) baseStart_578737 baseEnd_578737 := by
    simpa [prefixWord, tailWord_578737, baseEnd_578737] using wordTrace_append hprefix tailTrace_578737
  have hstable : (prefixWord ++ tailWord_578737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578737).length < 2 ^ (prefixWord ++ tailWord_578737).sum := by decide
  have hdescent : baseEnd_578737 < baseStart_578737 := by decide
  rcases family_descends (prefixWord ++ tailWord_578737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578781 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_578781 : Nat := 118140960795 + 578781 * 2 ^ 59
def prefixEnd_578781 : Nat := 4983230072969 + 3 ^ 40 * 578781 * 2
def baseEnd_578781 : Nat := 99064282230001750125247

theorem tailTrace_578781 : CollatzResearch.WordTrace tailWord_578781 prefixEnd_578781 99064282230001750125247 := by
  unfold tailWord_578781
  simp only [CollatzResearch.WordTrace]
  refine ⟨21109877316182759770224197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14073251544121839846816131 21109877316182759770224197)
  ·
    refine ⟨3958101996784267456917037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21109877316182759770224197 3958101996784267456917037)
    ·
      refine ⟨1484288248794100296343889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3958101996784267456917037 1484288248794100296343889)
      ·
        refine ⟨1113216186595575222257917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1484288248794100296343889 1113216186595575222257917)
        ·
          refine ⟨417456069973340708346719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1113216186595575222257917 417456069973340708346719)
          ·
            refine ⟨626184104960011062520079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417456069973340708346719 626184104960011062520079)
            ·
              refine ⟨939276157440016593780119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626184104960011062520079 939276157440016593780119)
              ·
                refine ⟨1408914236160024890670179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939276157440016593780119 1408914236160024890670179)
                ·
                  refine ⟨2113371354240037336005269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408914236160024890670179 2113371354240037336005269)
                  ·
                    refine ⟨99064282230001750125247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2113371354240037336005269 99064282230001750125247)
                    ·
                      rfl

theorem cell23_578781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_578781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578781 prefixEnd_578781 := by exact prefixLift 578781
  have htrace : WordTrace (prefixWord ++ tailWord_578781) baseStart_578781 baseEnd_578781 := by
    simpa [prefixWord, tailWord_578781, baseEnd_578781] using wordTrace_append hprefix tailTrace_578781
  have hstable : (prefixWord ++ tailWord_578781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578781).length < 2 ^ (prefixWord ++ tailWord_578781).sum := by decide
  have hdescent : baseEnd_578781 < baseStart_578781 := by decide
  rcases family_descends (prefixWord ++ tailWord_578781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578791 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_578791 : Nat := 118140960795 + 578791 * 2 ^ 59
def prefixEnd_578791 : Nat := 4983230072969 + 3 ^ 40 * 578791 * 2
def baseEnd_578791 : Nat := 297197981496550211250695

theorem tailTrace_578791 : CollatzResearch.WordTrace tailWord_578791 prefixEnd_578791 297197981496550211250695 := by
  unfold tailWord_578791
  simp only [CollatzResearch.WordTrace]
  refine ⟨21110242046146531478088227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14073494697431020985392151 21110242046146531478088227)
  ·
    refine ⟨31665363069219797217132341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21110242046146531478088227 31665363069219797217132341)
    ·
      refine ⟨2968627787739355989106157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31665363069219797217132341 2968627787739355989106157)
      ·
        refine ⟨1113235420402258495914809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2968627787739355989106157 1113235420402258495914809)
        ·
          refine ⟨834926565301693871936107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113235420402258495914809 834926565301693871936107)
          ·
            refine ⟨1252389847952540807904161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834926565301693871936107 1252389847952540807904161)
            ·
              refine ⟨939292385964405605928121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1252389847952540807904161 939292385964405605928121)
              ·
                refine ⟨704469289473304204446091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939292385964405605928121 704469289473304204446091)
                ·
                  refine ⟨1056703934209956306669137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704469289473304204446091 1056703934209956306669137)
                  ·
                    refine ⟨792527950657467230001853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1056703934209956306669137 792527950657467230001853)
                    ·
                      refine ⟨297197981496550211250695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 792527950657467230001853 297197981496550211250695)
                      ·
                        rfl

theorem cell23_578791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_578791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578791 prefixEnd_578791 := by exact prefixLift 578791
  have htrace : WordTrace (prefixWord ++ tailWord_578791) baseStart_578791 baseEnd_578791 := by
    simpa [prefixWord, tailWord_578791, baseEnd_578791] using wordTrace_append hprefix tailTrace_578791
  have hstable : (prefixWord ++ tailWord_578791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578791).length < 2 ^ (prefixWord ++ tailWord_578791).sum := by decide
  have hdescent : baseEnd_578791 < baseStart_578791 := by decide
  rcases family_descends (prefixWord ++ tailWord_578791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578848 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2]
def baseStart_578848 : Nat := 118140960795 + 578848 * 2 ^ 59
def prefixEnd_578848 : Nat := 4983230072969 + 3 ^ 40 * 578848 * 2
def baseEnd_578848 : Nat := 297227249893856488237933

theorem tailTrace_578848 : CollatzResearch.WordTrace tailWord_578848 prefixEnd_578848 297227249893856488237933 := by
  unfold tailWord_578848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556160503470015106456599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14074880671293353475275465 10556160503470015106456599)
  ·
    refine ⟨15834240755205022659684899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556160503470015106456599 15834240755205022659684899)
    ·
      refine ⟨23751361132807533989527349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15834240755205022659684899 23751361132807533989527349)
      ·
        refine ⟨2226690106200706311518189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23751361132807533989527349 2226690106200706311518189)
        ·
          refine ⟨835008789825264866819321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2226690106200706311518189 835008789825264866819321)
          ·
            refine ⟨626256592368948650114491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835008789825264866819321 626256592368948650114491)
            ·
              refine ⟨939384888553422975171737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626256592368948650114491 939384888553422975171737)
              ·
                refine ⟨704538666415067231378803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939384888553422975171737 704538666415067231378803)
                ·
                  refine ⟨1056807999622600847068205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704538666415067231378803 1056807999622600847068205)
                  ·
                    refine ⟨396302999858475317650577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1056807999622600847068205 396302999858475317650577)
                    ·
                      refine ⟨297227249893856488237933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396302999858475317650577 297227249893856488237933)
                      ·
                        rfl

theorem cell23_578848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_578848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578848 prefixEnd_578848 := by exact prefixLift 578848
  have htrace : WordTrace (prefixWord ++ tailWord_578848) baseStart_578848 baseEnd_578848 := by
    simpa [prefixWord, tailWord_578848, baseEnd_578848] using wordTrace_append hprefix tailTrace_578848
  have hstable : (prefixWord ++ tailWord_578848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578848).length < 2 ^ (prefixWord ++ tailWord_578848).sum := by decide
  have hdescent : baseEnd_578848 < baseStart_578848 := by decide
  rcases family_descends (prefixWord ++ tailWord_578848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578861 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_578861 : Nat := 118140960795 + 578861 * 2 ^ 59
def prefixEnd_578861 : Nat := 4983230072969 + 3 ^ 40 * 578861 * 2
def baseEnd_578861 : Nat := 297233925142364937375373

theorem tailTrace_578861 : CollatzResearch.WordTrace tailWord_578861 prefixEnd_578861 297233925142364937375373 := by
  unfold tailWord_578861
  simp only [CollatzResearch.WordTrace]
  refine ⟨21112795155892933433136437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14075196770595288955424291 21112795155892933433136437)
  ·
    refine ⟨1979324545864962509356541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21112795155892933433136437 1979324545864962509356541)
    ·
      refine ⟨742246704699360941008703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1979324545864962509356541 742246704699360941008703)
      ·
        refine ⟨1113370057049041411513055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742246704699360941008703 1113370057049041411513055)
        ·
          refine ⟨1670055085573562117269583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113370057049041411513055 1670055085573562117269583)
          ·
            refine ⟨2505082628360343175904375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1670055085573562117269583 2505082628360343175904375)
            ·
              refine ⟨3757623942540514763856563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2505082628360343175904375 3757623942540514763856563)
              ·
                refine ⟨5636435913810772145784845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3757623942540514763856563 5636435913810772145784845)
                ·
                  refine ⟨2113663467679039554669317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5636435913810772145784845 2113663467679039554669317)
                  ·
                    refine ⟨396311900189819916500497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2113663467679039554669317 396311900189819916500497)
                    ·
                      refine ⟨297233925142364937375373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396311900189819916500497 297233925142364937375373)
                      ·
                        rfl

theorem cell23_578861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_578861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578861 prefixEnd_578861 := by exact prefixLift 578861
  have htrace : WordTrace (prefixWord ++ tailWord_578861) baseStart_578861 baseEnd_578861 := by
    simpa [prefixWord, tailWord_578861, baseEnd_578861] using wordTrace_append hprefix tailTrace_578861
  have hstable : (prefixWord ++ tailWord_578861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578861).length < 2 ^ (prefixWord ++ tailWord_578861).sum := by decide
  have hdescent : baseEnd_578861 < baseStart_578861 := by decide
  rcases family_descends (prefixWord ++ tailWord_578861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578878 : List Nat := [4, 2, 1, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_578878 : Nat := 118140960795 + 578878 * 2 ^ 59
def prefixEnd_578878 : Nat := 4983230072969 + 3 ^ 40 * 578878 * 2
def baseEnd_578878 : Nat := 297242654313491370862795

theorem tailTrace_578878 : CollatzResearch.WordTrace tailWord_578878 prefixEnd_578878 297242654313491370862795 := by
  unfold tailWord_578878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2639176899603918167063161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14075610131220896891003525 2639176899603918167063161)
  ·
    refine ⟨1979382674702938625297371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2639176899603918167063161 1979382674702938625297371)
    ·
      refine ⟨2969074012054407937946057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1979382674702938625297371 2969074012054407937946057)
      ·
        refine ⟨2226805509040805953459543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2969074012054407937946057 2226805509040805953459543)
        ·
          refine ⟨3340208263561208930189315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226805509040805953459543 3340208263561208930189315)
          ·
            refine ⟨5010312395341813395283973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340208263561208930189315 5010312395341813395283973)
            ·
              refine ⟨939433574126590011615745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5010312395341813395283973 939433574126590011615745)
              ·
                refine ⟨704575180594942508711809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 939433574126590011615745 704575180594942508711809)
                ·
                  refine ⟨528431385446206881533857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704575180594942508711809 528431385446206881533857)
                  ·
                    refine ⟨396323539084655161150393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528431385446206881533857 396323539084655161150393)
                    ·
                      refine ⟨297242654313491370862795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396323539084655161150393 297242654313491370862795)
                      ·
                        rfl

theorem cell23_578878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_578878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578878 prefixEnd_578878 := by exact prefixLift 578878
  have htrace : WordTrace (prefixWord ++ tailWord_578878) baseStart_578878 baseEnd_578878 := by
    simpa [prefixWord, tailWord_578878, baseEnd_578878] using wordTrace_append hprefix tailTrace_578878
  have hstable : (prefixWord ++ tailWord_578878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578878).length < 2 ^ (prefixWord ++ tailWord_578878).sum := by decide
  have hdescent : baseEnd_578878 < baseStart_578878 := by decide
  rcases family_descends (prefixWord ++ tailWord_578878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578917 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_578917 : Nat := 118140960795 + 578917 * 2 ^ 59
def prefixEnd_578917 : Nat := 4983230072969 + 3 ^ 40 * 578917 * 2
def baseEnd_578917 : Nat := 297262680059016718275115

theorem tailTrace_578917 : CollatzResearch.WordTrace tailWord_578917 prefixEnd_578917 297262680059016718275115 := by
  unfold tailWord_578917
  simp only [CollatzResearch.WordTrace]
  refine ⟨21114837643690054997175005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14076558429126703331450003 21114837643690054997175005)
  ·
    refine ⟨7918064116383770623940627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21114837643690054997175005 7918064116383770623940627)
    ·
      refine ⟨11877096174575655935910941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7918064116383770623940627 11877096174575655935910941)
      ·
        refine ⟨4453911065465870975966603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11877096174575655935910941 4453911065465870975966603)
        ·
          refine ⟨6680866598198806463949905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453911065465870975966603 6680866598198806463949905)
          ·
            refine ⟨5010649948649104847962429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6680866598198806463949905 5010649948649104847962429)
            ·
              refine ⟨1878993730743414317985911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5010649948649104847962429 1878993730743414317985911)
              ·
                refine ⟨2818490596115121476978867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1878993730743414317985911 2818490596115121476978867)
                ·
                  refine ⟨4227735894172682215468301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818490596115121476978867 4227735894172682215468301)
                  ·
                    refine ⟨1585400960314755830800613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4227735894172682215468301 1585400960314755830800613)
                    ·
                      refine ⟨297262680059016718275115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1585400960314755830800613 297262680059016718275115)
                      ·
                        rfl

theorem cell23_578917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_578917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578917 prefixEnd_578917 := by exact prefixLift 578917
  have htrace : WordTrace (prefixWord ++ tailWord_578917) baseStart_578917 baseEnd_578917 := by
    simpa [prefixWord, tailWord_578917, baseEnd_578917] using wordTrace_append hprefix tailTrace_578917
  have hstable : (prefixWord ++ tailWord_578917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578917).length < 2 ^ (prefixWord ++ tailWord_578917).sum := by decide
  have hdescent : baseEnd_578917 < baseStart_578917 := by decide
  rcases family_descends (prefixWord ++ tailWord_578917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578927 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 5, 4]
def baseStart_578927 : Nat := 118140960795 + 578927 * 2 ^ 59
def prefixEnd_578927 : Nat := 4983230072969 + 3 ^ 40 * 578927 * 2
def baseEnd_578927 : Nat := 99089271621853893050023

theorem tailTrace_578927 : CollatzResearch.WordTrace tailWord_578927 prefixEnd_578927 99089271621853893050023 := by
  unfold tailWord_578927
  simp only [CollatzResearch.WordTrace]
  refine ⟨21115202373653826705039035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14076801582435884470026023 21115202373653826705039035)
  ·
    refine ⟨31672803560480740057558553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21115202373653826705039035 31672803560480740057558553)
    ·
      refine ⟨23754602670360555043168915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31672803560480740057558553 23754602670360555043168915)
      ·
        refine ⟨35631904005540832564753373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23754602670360555043168915 35631904005540832564753373)
        ·
          refine ⟨13361964002077812211782515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35631904005540832564753373 13361964002077812211782515)
          ·
            refine ⟨20042946003116718317673773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13361964002077812211782515 20042946003116718317673773)
            ·
              refine ⟨7516104751168769369127665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20042946003116718317673773 7516104751168769369127665)
              ·
                refine ⟨5637078563376577026845749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7516104751168769369127665 5637078563376577026845749)
                ·
                  refine ⟨528476115316554096266789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5637078563376577026845749 528476115316554096266789)
                  ·
                    refine ⟨99089271621853893050023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528476115316554096266789 99089271621853893050023)
                    ·
                      rfl

theorem cell23_578927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_578927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578927 prefixEnd_578927 := by exact prefixLift 578927
  have htrace : WordTrace (prefixWord ++ tailWord_578927) baseStart_578927 baseEnd_578927 := by
    simpa [prefixWord, tailWord_578927, baseEnd_578927] using wordTrace_append hprefix tailTrace_578927
  have hstable : (prefixWord ++ tailWord_578927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578927).length < 2 ^ (prefixWord ++ tailWord_578927).sum := by decide
  have hdescent : baseEnd_578927 < baseStart_578927 := by decide
  rcases family_descends (prefixWord ++ tailWord_578927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578967 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_578967 : Nat := 118140960795 + 578967 * 2 ^ 59
def prefixEnd_578967 : Nat := 4983230072969 + 3 ^ 40 * 578967 * 2
def baseEnd_578967 : Nat := 297288354091741522649885

theorem tailTrace_578967 : CollatzResearch.WordTrace tailWord_578967 prefixEnd_578967 297288354091741522649885 := by
  unfold tailWord_578967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116661293508913536495155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14077774195672609024330103 21116661293508913536495155)
  ·
    refine ⟨31674991940263370304742733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21116661293508913536495155 31674991940263370304742733)
    ·
      refine ⟨11878121977598763864278525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31674991940263370304742733 11878121977598763864278525)
      ·
        refine ⟨4454295741599536449104447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11878121977598763864278525 4454295741599536449104447)
        ·
          refine ⟨6681443612399304673656671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454295741599536449104447 6681443612399304673656671)
          ·
            refine ⟨10022165418598957010485007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6681443612399304673656671 10022165418598957010485007)
            ·
              refine ⟨15033248127898435515727511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10022165418598957010485007 15033248127898435515727511)
              ·
                refine ⟨22549872191847653273591267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15033248127898435515727511 22549872191847653273591267)
                ·
                  refine ⟨33824808287771479910386901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22549872191847653273591267 33824808287771479910386901)
                  ·
                    refine ⟨792768944244644060399693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33824808287771479910386901 792768944244644060399693)
                    ·
                      refine ⟨297288354091741522649885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 792768944244644060399693 297288354091741522649885)
                      ·
                        rfl

theorem cell23_578967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_578967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578967 prefixEnd_578967 := by exact prefixLift 578967
  have htrace : WordTrace (prefixWord ++ tailWord_578967) baseStart_578967 baseEnd_578967 := by
    simpa [prefixWord, tailWord_578967, baseEnd_578967] using wordTrace_append hprefix tailTrace_578967
  have hstable : (prefixWord ++ tailWord_578967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578967).length < 2 ^ (prefixWord ++ tailWord_578967).sum := by decide
  have hdescent : baseEnd_578967 < baseStart_578967 := by decide
  rcases family_descends (prefixWord ++ tailWord_578967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578978 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_578978 : Nat := 118140960795 + 578978 * 2 ^ 59
def prefixEnd_578978 : Nat := 4983230072969 + 3 ^ 40 * 578978 * 2
def baseEnd_578978 : Nat := 99098000792980326537445

theorem tailTrace_578978 : CollatzResearch.WordTrace tailWord_578978 prefixEnd_578978 99098000792980326537445 := by
  unfold tailWord_578978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279265624117265603786397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14078041664312708276763725 5279265624117265603786397)
  ·
    refine ⟨1979724609043974601419899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5279265624117265603786397 1979724609043974601419899)
    ·
      refine ⟨2969586913565961902129849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1979724609043974601419899 2969586913565961902129849)
      ·
        refine ⟨2227190185174471426597387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2969586913565961902129849 2227190185174471426597387)
        ·
          refine ⟨3340785277761707139896081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227190185174471426597387 3340785277761707139896081)
          ·
            refine ⟨2505588958321280354922061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3340785277761707139896081 2505588958321280354922061)
            ·
              refine ⟨939595859370480133095773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2505588958321280354922061 939595859370480133095773)
              ·
                refine ⟨352348447263930049910915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 939595859370480133095773 352348447263930049910915)
                ·
                  refine ⟨528522670895895074866373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352348447263930049910915 528522670895895074866373)
                  ·
                    refine ⟨99098000792980326537445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528522670895895074866373 99098000792980326537445)
                    ·
                      rfl

theorem cell23_578978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_578978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578978 prefixEnd_578978 := by exact prefixLift 578978
  have htrace : WordTrace (prefixWord ++ tailWord_578978) baseStart_578978 baseEnd_578978 := by
    simpa [prefixWord, tailWord_578978, baseEnd_578978] using wordTrace_append hprefix tailTrace_578978
  have hstable : (prefixWord ++ tailWord_578978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578978).length < 2 ^ (prefixWord ++ tailWord_578978).sum := by decide
  have hdescent : baseEnd_578978 < baseStart_578978 := by decide
  rcases family_descends (prefixWord ++ tailWord_578978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_578994 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_578994 : Nat := 118140960795 + 578994 * 2 ^ 59
def prefixEnd_578994 : Nat := 4983230072969 + 3 ^ 40 * 578994 * 2
def baseEnd_578994 : Nat := 297302218069412917012261

theorem tailTrace_578994 : CollatzResearch.WordTrace tailWord_578994 prefixEnd_578994 297302218069412917012261 := by
  unfold tailWord_578994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279411516102774286932009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14078430709607398098485357 5279411516102774286932009)
  ·
    refine ⟨3959558637077080715199007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5279411516102774286932009 3959558637077080715199007)
    ·
      refine ⟨5939337955615621072798511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3959558637077080715199007 5939337955615621072798511)
      ·
        refine ⟨8909006933423431609197767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5939337955615621072798511 8909006933423431609197767)
        ·
          refine ⟨13363510400135147413796651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8909006933423431609197767 13363510400135147413796651)
          ·
            refine ⟨20045265600202721120694977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13363510400135147413796651 20045265600202721120694977)
            ·
              refine ⟨15033949200152040840521233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20045265600202721120694977 15033949200152040840521233)
              ·
                refine ⟨11275461900114030630390925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15033949200152040840521233 11275461900114030630390925)
                ·
                  refine ⟨4228298212542761486396597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11275461900114030630390925 4228298212542761486396597)
                  ·
                    refine ⟨396402957425883889349681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4228298212542761486396597 396402957425883889349681)
                    ·
                      refine ⟨297302218069412917012261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396402957425883889349681 297302218069412917012261)
                      ·
                        rfl

theorem cell23_578994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_578994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_578994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_578994 prefixEnd_578994 := by exact prefixLift 578994
  have htrace : WordTrace (prefixWord ++ tailWord_578994) baseStart_578994 baseEnd_578994 := by
    simpa [prefixWord, tailWord_578994, baseEnd_578994] using wordTrace_append hprefix tailTrace_578994
  have hstable : (prefixWord ++ tailWord_578994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_578994).length < 2 ^ (prefixWord ++ tailWord_578994).sum := by decide
  have hdescent : baseEnd_578994 < baseStart_578994 := by decide
  rcases family_descends (prefixWord ++ tailWord_578994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579017 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_579017 : Nat := 118140960795 + 579017 * 2 ^ 59
def prefixEnd_579017 : Nat := 4983230072969 + 3 ^ 40 * 579017 * 2
def baseEnd_579017 : Nat := 99104676041488775674885

theorem tailTrace_579017 : CollatzResearch.WordTrace tailWord_579017 prefixEnd_579017 99104676041488775674885 := by
  unfold tailWord_579017
  simp only [CollatzResearch.WordTrace]
  refine ⟨21118484943327772075815305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14078989962218514717210203 21118484943327772075815305)
  ·
    refine ⟨15838863707495829056861479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21118484943327772075815305 15838863707495829056861479)
    ·
      refine ⟨23758295561243743585292219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15838863707495829056861479 23758295561243743585292219)
      ·
        refine ⟨35637443341865615377938329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23758295561243743585292219 35637443341865615377938329)
        ·
          refine ⟨26728082506399211533453747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35637443341865615377938329 26728082506399211533453747)
          ·
            refine ⟨40092123759598817300180621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26728082506399211533453747 40092123759598817300180621)
            ·
              refine ⟨15034546409849556487567733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40092123759598817300180621 15034546409849556487567733)
              ·
                refine ⟨1409488725923395920709475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15034546409849556487567733 1409488725923395920709475)
                ·
                  refine ⟨2114233088885093881064213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409488725923395920709475 2114233088885093881064213)
                  ·
                    refine ⟨99104676041488775674885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2114233088885093881064213 99104676041488775674885)
                    ·
                      rfl

theorem cell23_579017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_579017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579017 prefixEnd_579017 := by exact prefixLift 579017
  have htrace : WordTrace (prefixWord ++ tailWord_579017) baseStart_579017 baseEnd_579017 := by
    simpa [prefixWord, tailWord_579017, baseEnd_579017] using wordTrace_append hprefix tailTrace_579017
  have hstable : (prefixWord ++ tailWord_579017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579017).length < 2 ^ (prefixWord ++ tailWord_579017).sum := by decide
  have hdescent : baseEnd_579017 < baseStart_579017 := by decide
  rcases family_descends (prefixWord ++ tailWord_579017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579034 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_579034 : Nat := 118140960795 + 579034 * 2 ^ 59
def prefixEnd_579034 : Nat := 4983230072969 + 3 ^ 40 * 579034 * 2
def baseEnd_579034 : Nat := 99107585765197586837359

theorem tailTrace_579034 : CollatzResearch.WordTrace tailWord_579034 prefixEnd_579034 99107585765197586837359 := by
  unfold tailWord_579034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279776246066545994796039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14079403322844122652789437 5279776246066545994796039)
  ·
    refine ⟨7919664369099818992194059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5279776246066545994796039 7919664369099818992194059)
    ·
      refine ⟨11879496553649728488291089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7919664369099818992194059 11879496553649728488291089)
      ·
        refine ⟨8909622415237296366218317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11879496553649728488291089 8909622415237296366218317)
        ·
          refine ⟨3341108405713986137331869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8909622415237296366218317 3341108405713986137331869)
          ·
            refine ⟨1252915652142744801499451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3341108405713986137331869 1252915652142744801499451)
            ·
              refine ⟨1879373478214117202249177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252915652142744801499451 1879373478214117202249177)
              ·
                refine ⟨1409530108660587901686883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1879373478214117202249177 1409530108660587901686883)
                ·
                  refine ⟨2114295162990881852530325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1409530108660587901686883 2114295162990881852530325)
                  ·
                    refine ⟨99107585765197586837359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2114295162990881852530325 99107585765197586837359)
                    ·
                      rfl

theorem cell23_579034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_579034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579034 prefixEnd_579034 := by exact prefixLift 579034
  have htrace : WordTrace (prefixWord ++ tailWord_579034) baseStart_579034 baseEnd_579034 := by
    simpa [prefixWord, tailWord_579034, baseEnd_579034] using wordTrace_append hprefix tailTrace_579034
  have hstable : (prefixWord ++ tailWord_579034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579034).length < 2 ^ (prefixWord ++ tailWord_579034).sum := by decide
  have hdescent : baseEnd_579034 < baseStart_579034 := by decide
  rcases family_descends (prefixWord ++ tailWord_579034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579047 : List Nat := [1, 1, 5, 2, 1, 13]
def baseStart_579047 : Nat := 118140960795 + 579047 * 2 ^ 59
def prefixEnd_579047 : Nat := 4983230072969 + 3 ^ 40 * 579047 * 2
def baseEnd_579047 : Nat := 1223577911704120204319

theorem tailTrace_579047 : CollatzResearch.WordTrace tailWord_579047 prefixEnd_579047 1223577911704120204319 := by
  unfold tailWord_579047
  simp only [CollatzResearch.WordTrace]
  refine ⟨21119579133219087199407395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14079719422146058132938263 21119579133219087199407395)
  ·
    refine ⟨31679368699828630799111093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21119579133219087199407395 31679368699828630799111093)
    ·
      refine ⟨2969940815608934137416665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31679368699828630799111093 2969940815608934137416665)
      ·
        refine ⟨2227455611706700603062499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2969940815608934137416665 2227455611706700603062499)
        ·
          refine ⟨3341183417560050904593749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2227455611706700603062499 3341183417560050904593749)
          ·
            refine ⟨1223577911704120204319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3341183417560050904593749 1223577911704120204319)
            ·
              rfl

theorem cell23_579047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 13].length) (baseStart_579047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579047 prefixEnd_579047 := by exact prefixLift 579047
  have htrace : WordTrace (prefixWord ++ tailWord_579047) baseStart_579047 baseEnd_579047 := by
    simpa [prefixWord, tailWord_579047, baseEnd_579047] using wordTrace_append hprefix tailTrace_579047
  have hstable : (prefixWord ++ tailWord_579047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579047).length < 2 ^ (prefixWord ++ tailWord_579047).sum := by decide
  have hdescent : baseEnd_579047 < baseStart_579047 := by decide
  rcases family_descends (prefixWord ++ tailWord_579047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579054 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_579054 : Nat := 118140960795 + 579054 * 2 ^ 59
def prefixEnd_579054 : Nat := 4983230072969 + 3 ^ 40 * 579054 * 2
def baseEnd_579054 : Nat := 297333026908682682261985

theorem tailTrace_579054 : CollatzResearch.WordTrace tailWord_579054 prefixEnd_579054 297333026908682682261985 := by
  unfold tailWord_579054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2639979305524215924364027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14079889629462484929941477 2639979305524215924364027)
  ·
    refine ⟨3959968958286323886546041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2639979305524215924364027 3959968958286323886546041)
    ·
      refine ⟨2969976718714742914909531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3959968958286323886546041 2969976718714742914909531)
      ·
        refine ⟨4454965078072114372364297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969976718714742914909531 4454965078072114372364297)
        ·
          refine ⟨3341223808554085779273223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4454965078072114372364297 3341223808554085779273223)
          ·
            refine ⟨5011835712831128668909835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341223808554085779273223 5011835712831128668909835)
            ·
              refine ⟨7517753569246693003364753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011835712831128668909835 7517753569246693003364753)
              ·
                refine ⟨5638315176935019752523565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517753569246693003364753 5638315176935019752523565)
                ·
                  refine ⟨2114368191350632407196337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5638315176935019752523565 2114368191350632407196337)
                  ·
                    refine ⟨1585776143512974305397253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2114368191350632407196337 1585776143512974305397253)
                    ·
                      refine ⟨297333026908682682261985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1585776143512974305397253 297333026908682682261985)
                      ·
                        rfl

theorem cell23_579054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_579054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579054 prefixEnd_579054 := by exact prefixLift 579054
  have htrace : WordTrace (prefixWord ++ tailWord_579054) baseStart_579054 baseEnd_579054 := by
    simpa [prefixWord, tailWord_579054, baseEnd_579054] using wordTrace_append hprefix tailTrace_579054
  have hstable : (prefixWord ++ tailWord_579054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579054).length < 2 ^ (prefixWord ++ tailWord_579054).sum := by decide
  have hdescent : baseEnd_579054 < baseStart_579054 := by decide
  rcases family_descends (prefixWord ++ tailWord_579054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579064 : List Nat := [2, 1, 2, 1, 1, 7, 1, 8]
def baseStart_579064 : Nat := 118140960795 + 579064 * 2 ^ 59
def prefixEnd_579064 : Nat := 4983230072969 + 3 ^ 40 * 579064 * 2
def baseEnd_579064 : Nat := 11012524507971394190257

theorem tailTrace_579064 : CollatzResearch.WordTrace tailWord_579064 prefixEnd_579064 11012524507971394190257 := by
  unfold tailWord_579064
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560099587078749551388123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14080132782771666068517497 10560099587078749551388123)
  ·
    refine ⟨15840149380618124327082185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10560099587078749551388123 15840149380618124327082185)
    ·
      refine ⟨11880112035463593245311639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15840149380618124327082185 11880112035463593245311639)
      ·
        refine ⟨17820168053195389867967459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11880112035463593245311639 17820168053195389867967459)
        ·
          refine ⟨26730252079793084801951189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17820168053195389867967459 26730252079793084801951189)
          ·
            refine ⟨626490283120150425045731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26730252079793084801951189 626490283120150425045731)
            ·
              refine ⟨939735424680225637568597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626490283120150425045731 939735424680225637568597)
              ·
                refine ⟨11012524507971394190257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 939735424680225637568597 11012524507971394190257)
                ·
                  rfl

theorem cell23_579064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 8].length) (baseStart_579064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579064 prefixEnd_579064 := by exact prefixLift 579064
  have htrace : WordTrace (prefixWord ++ tailWord_579064) baseStart_579064 baseEnd_579064 := by
    simpa [prefixWord, tailWord_579064, baseEnd_579064] using wordTrace_append hprefix tailTrace_579064
  have hstable : (prefixWord ++ tailWord_579064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579064).length < 2 ^ (prefixWord ++ tailWord_579064).sum := by decide
  have hdescent : baseEnd_579064 < baseStart_579064 := by decide
  rcases family_descends (prefixWord ++ tailWord_579064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579077 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_579077 : Nat := 118140960795 + 579077 * 2 ^ 59
def prefixEnd_579077 : Nat := 4983230072969 + 3 ^ 40 * 579077 * 2
def baseEnd_579077 : Nat := 99114945654578697424793

theorem tailTrace_579077 : CollatzResearch.WordTrace tailWord_579077 prefixEnd_579077 99114945654578697424793 := by
  unfold tailWord_579077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21120673323110402322999485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14080448882073601548666323 21120673323110402322999485)
  ·
    refine ⟨7920252496166400871124807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21120673323110402322999485 7920252496166400871124807)
    ·
      refine ⟨11880378744249601306687211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7920252496166400871124807 11880378744249601306687211)
      ·
        refine ⟨17820568116374401960030817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11880378744249601306687211 17820568116374401960030817)
        ·
          refine ⟨13365426087280801470023113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17820568116374401960030817 13365426087280801470023113)
          ·
            refine ⟨10024069565460601102517335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13365426087280801470023113 10024069565460601102517335)
            ·
              refine ⟨15036104348190901653776003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10024069565460601102517335 15036104348190901653776003)
              ·
                refine ⟨22554156522286352480664005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15036104348190901653776003 22554156522286352480664005)
                ·
                  refine ⟨4228904347928691090124501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22554156522286352480664005 4228904347928691090124501)
                  ·
                    refine ⟨99114945654578697424793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4228904347928691090124501 99114945654578697424793)
                    ·
                      rfl

theorem cell23_579077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_579077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579077 prefixEnd_579077 := by exact prefixLift 579077
  have htrace : WordTrace (prefixWord ++ tailWord_579077) baseStart_579077 baseEnd_579077 := by
    simpa [prefixWord, tailWord_579077, baseEnd_579077] using wordTrace_append hprefix tailTrace_579077
  have hstable : (prefixWord ++ tailWord_579077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579077).length < 2 ^ (prefixWord ++ tailWord_579077).sum := by decide
  have hdescent : baseEnd_579077 < baseStart_579077 := by decide
  rcases family_descends (prefixWord ++ tailWord_579077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579092 : List Nat := [2, 4, 3, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_579092 : Nat := 118140960795 + 579092 * 2 ^ 59
def prefixEnd_579092 : Nat := 4983230072969 + 3 ^ 40 * 579092 * 2
def baseEnd_579092 : Nat := 297352539173553533586811

theorem tailTrace_579092 : CollatzResearch.WordTrace tailWord_579092 prefixEnd_579092 297352539173553533586811 := by
  unfold tailWord_579092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560610209028029942397765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14080813612037373256530353 10560610209028029942397765)
  ·
    refine ⟨1980114414192755614199581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10560610209028029942397765 1980114414192755614199581)
    ·
      refine ⟨742542905322283355324843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1980114414192755614199581 742542905322283355324843)
      ·
        refine ⟨1113814357983425032987265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742542905322283355324843 1113814357983425032987265)
        ·
          refine ⟨835360768487568774740449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1113814357983425032987265 835360768487568774740449)
          ·
            refine ⟨626520576365676581055337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835360768487568774740449 626520576365676581055337)
            ·
              refine ⟨469890432274257435791503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626520576365676581055337 469890432274257435791503)
              ·
                refine ⟨704835648411386153687255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469890432274257435791503 704835648411386153687255)
                ·
                  refine ⟨1057253472617079230530883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 704835648411386153687255 1057253472617079230530883)
                  ·
                    refine ⟨1585880208925618845796325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1057253472617079230530883 1585880208925618845796325)
                    ·
                      refine ⟨297352539173553533586811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1585880208925618845796325 297352539173553533586811)
                      ·
                        rfl

theorem cell23_579092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_579092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579092 prefixEnd_579092 := by exact prefixLift 579092
  have htrace : WordTrace (prefixWord ++ tailWord_579092) baseStart_579092 baseEnd_579092 := by
    simpa [prefixWord, tailWord_579092, baseEnd_579092] using wordTrace_append hprefix tailTrace_579092
  have hstable : (prefixWord ++ tailWord_579092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579092).length < 2 ^ (prefixWord ++ tailWord_579092).sum := by decide
  have hdescent : baseEnd_579092 < baseStart_579092 := by decide
  rcases family_descends (prefixWord ++ tailWord_579092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579102 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_579102 : Nat := 118140960795 + 579102 * 2 ^ 59
def prefixEnd_579102 : Nat := 4983230072969 + 3 ^ 40 * 579102 * 2
def baseEnd_579102 : Nat := 99119224660032831487255

theorem tailTrace_579102 : CollatzResearch.WordTrace tailWord_579102 prefixEnd_579102 99119224660032831487255 := by
  unfold tailWord_579102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640198143502478949082445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14081056765346554395106373 2640198143502478949082445)
  ·
    refine ⟨990074303813429605905917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2640198143502478949082445 990074303813429605905917)
    ·
      refine ⟨371277863930036102214719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 990074303813429605905917 371277863930036102214719)
      ·
        refine ⟨556916795895054153322079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371277863930036102214719 556916795895054153322079)
        ·
          refine ⟨835375193842581229983119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556916795895054153322079 835375193842581229983119)
          ·
            refine ⟨1253062790763871844974679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835375193842581229983119 1253062790763871844974679)
            ·
              refine ⟨1879594186145807767462019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253062790763871844974679 1879594186145807767462019)
              ·
                refine ⟨2819391279218711651193029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1879594186145807767462019 2819391279218711651193029)
                ·
                  refine ⟨528635864853508434598693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2819391279218711651193029 528635864853508434598693)
                  ·
                    refine ⟨99119224660032831487255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528635864853508434598693 99119224660032831487255)
                    ·
                      rfl

theorem cell23_579102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_579102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579102 prefixEnd_579102 := by exact prefixLift 579102
  have htrace : WordTrace (prefixWord ++ tailWord_579102) baseStart_579102 baseEnd_579102 := by
    simpa [prefixWord, tailWord_579102, baseEnd_579102] using wordTrace_append hprefix tailTrace_579102
  have hstable : (prefixWord ++ tailWord_579102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579102).length < 2 ^ (prefixWord ++ tailWord_579102).sum := by decide
  have hdescent : baseEnd_579102 < baseStart_579102 := by decide
  rcases family_descends (prefixWord ++ tailWord_579102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579125 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 2, 1, 3]
def baseStart_579125 : Nat := 118140960795 + 579125 * 2 ^ 59
def prefixEnd_579125 : Nat := 4983230072969 + 3 ^ 40 * 579125 * 2
def baseEnd_579125 : Nat := 297369484035151904474159

theorem tailTrace_579125 : CollatzResearch.WordTrace tailWord_579125 prefixEnd_579125 297369484035151904474159 := by
  unfold tailWord_579125
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122424026936506520746829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14081616017957671013831219 21122424026936506520746829)
  ·
    refine ⟨7920909010101189945280061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21122424026936506520746829 7920909010101189945280061)
    ·
      refine ⟨2970340878787946229480023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7920909010101189945280061 2970340878787946229480023)
      ·
        refine ⟨4455511318181919344220035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2970340878787946229480023 4455511318181919344220035)
        ·
          refine ⟨6683266977272879016330053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455511318181919344220035 6683266977272879016330053)
          ·
            refine ⟨1253112558238664815561885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6683266977272879016330053 1253112558238664815561885)
            ·
              refine ⟨469917209339499305835707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1253112558238664815561885 469917209339499305835707)
              ·
                refine ⟨704875814009248958753561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 469917209339499305835707 704875814009248958753561)
                ·
                  refine ⟨528656860506936719065171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704875814009248958753561 528656860506936719065171)
                  ·
                    refine ⟨792985290760405078597757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528656860506936719065171 792985290760405078597757)
                    ·
                      refine ⟨297369484035151904474159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 792985290760405078597757 297369484035151904474159)
                      ·
                        rfl

theorem cell23_579125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_579125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579125 prefixEnd_579125 := by exact prefixLift 579125
  have htrace : WordTrace (prefixWord ++ tailWord_579125) baseStart_579125 baseEnd_579125 := by
    simpa [prefixWord, tailWord_579125, baseEnd_579125] using wordTrace_append hprefix tailTrace_579125
  have hstable : (prefixWord ++ tailWord_579125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579125).length < 2 ^ (prefixWord ++ tailWord_579125).sum := by decide
  have hdescent : baseEnd_579125 < baseStart_579125 := by decide
  rcases family_descends (prefixWord ++ tailWord_579125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579148 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_579148 : Nat := 118140960795 + 579148 * 2 ^ 59
def prefixEnd_579148 : Nat := 4983230072969 + 3 ^ 40 * 579148 * 2
def baseEnd_579148 : Nat := 297381294090205314486553

theorem tailTrace_579148 : CollatzResearch.WordTrace tailWord_579148 prefixEnd_579148 297381294090205314486553 := by
  unfold tailWord_579148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561631452926590724417049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14082175270568787632556065 10561631452926590724417049)
  ·
    refine ⟨7921223589694943043312787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10561631452926590724417049 7921223589694943043312787)
    ·
      refine ⟨11881835384542414564969181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7921223589694943043312787 11881835384542414564969181)
      ·
        refine ⟨4455688269203405461863443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11881835384542414564969181 4455688269203405461863443)
        ·
          refine ⟨6683532403805108192795165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455688269203405461863443 6683532403805108192795165)
          ·
            refine ⟨2506324651426915572298187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6683532403805108192795165 2506324651426915572298187)
            ·
              refine ⟨3759486977140373358447281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506324651426915572298187 3759486977140373358447281)
              ·
                refine ⟨2819615232855280018835461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759486977140373358447281 2819615232855280018835461)
                ·
                  refine ⟨528677856160365003531649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2819615232855280018835461 528677856160365003531649)
                  ·
                    refine ⟨396508392120273752648737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528677856160365003531649 396508392120273752648737)
                    ·
                      refine ⟨297381294090205314486553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396508392120273752648737 297381294090205314486553)
                      ·
                        rfl

theorem cell23_579148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_579148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579148 prefixEnd_579148 := by exact prefixLift 579148
  have htrace : WordTrace (prefixWord ++ tailWord_579148) baseStart_579148 baseEnd_579148 := by
    simpa [prefixWord, tailWord_579148, baseEnd_579148] using wordTrace_append hprefix tailTrace_579148
  have hstable : (prefixWord ++ tailWord_579148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579148).length < 2 ^ (prefixWord ++ tailWord_579148).sum := by decide
  have hdescent : baseEnd_579148 < baseStart_579148 := by decide
  rcases family_descends (prefixWord ++ tailWord_579148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579171 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 7]
def baseStart_579171 : Nat := 118140960795 + 579171 * 2 ^ 59
def prefixEnd_579171 : Nat := 4983230072969 + 3 ^ 40 * 579171 * 2
def baseEnd_579171 : Nat := 33043678238362080499883

theorem tailTrace_579171 : CollatzResearch.WordTrace tailWord_579171 prefixEnd_579171 33043678238362080499883 := by
  unfold tailWord_579171
  simp only [CollatzResearch.WordTrace]
  refine ⟨21124101784769856376921367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14082734523179904251280911 21124101784769856376921367)
  ·
    refine ⟨31686152677154784565382051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21124101784769856376921367 31686152677154784565382051)
    ·
      refine ⟨47529229015732176848073077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31686152677154784565382051 47529229015732176848073077)
      ·
        refine ⟨4455865220224891579506851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47529229015732176848073077 4455865220224891579506851)
        ·
          refine ⟨6683797830337337369260277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455865220224891579506851 6683797830337337369260277)
          ·
            refine ⟨626606046594125378368151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6683797830337337369260277 626606046594125378368151)
            ·
              refine ⟨939909069891188067552227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626606046594125378368151 939909069891188067552227)
              ·
                refine ⟨1409863604836782101328341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 939909069891188067552227 1409863604836782101328341)
                ·
                  refine ⟨33043678238362080499883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1409863604836782101328341 33043678238362080499883)
                  ·
                    rfl

theorem cell23_579171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 7].length) (baseStart_579171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579171 prefixEnd_579171 := by exact prefixLift 579171
  have htrace : WordTrace (prefixWord ++ tailWord_579171) baseStart_579171 baseEnd_579171 := by
    simpa [prefixWord, tailWord_579171, baseEnd_579171] using wordTrace_append hprefix tailTrace_579171
  have hstable : (prefixWord ++ tailWord_579171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579171).length < 2 ^ (prefixWord ++ tailWord_579171).sum := by decide
  have hdescent : baseEnd_579171 < baseStart_579171 := by decide
  rcases family_descends (prefixWord ++ tailWord_579171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579182 : List Nat := [4, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_579182 : Nat := 118140960795 + 579182 * 2 ^ 59
def prefixEnd_579182 : Nat := 4983230072969 + 3 ^ 40 * 579182 * 2
def baseEnd_579182 : Nat := 297398752432458181461397

theorem tailTrace_579182 : CollatzResearch.WordTrace tailWord_579182 prefixEnd_579182 297398752432458181461397 := by
  unfold tailWord_579182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2640562873466250656946475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14083001991820003503714533 2640562873466250656946475)
  ·
    refine ⟨3960844310199375985419713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2640562873466250656946475 3960844310199375985419713)
    ·
      refine ⟨2970633232649531989064785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3960844310199375985419713 2970633232649531989064785)
      ·
        refine ⟨2227974924487148991798589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970633232649531989064785 2227974924487148991798589)
        ·
          refine ⟨835490596682680871924471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2227974924487148991798589 835490596682680871924471)
          ·
            refine ⟨1253235895024021307886707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 835490596682680871924471 1253235895024021307886707)
            ·
              refine ⟨1879853842536031961830061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253235895024021307886707 1879853842536031961830061)
              ·
                refine ⟨704945190951011985686273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1879853842536031961830061 704945190951011985686273)
                ·
                  refine ⟨528708893213258989264705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 704945190951011985686273 528708893213258989264705)
                  ·
                    refine ⟨396531669909944241948529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528708893213258989264705 396531669909944241948529)
                    ·
                      refine ⟨297398752432458181461397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396531669909944241948529 297398752432458181461397)
                      ·
                        rfl

theorem cell23_579182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_579182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579182 prefixEnd_579182 := by exact prefixLift 579182
  have htrace : WordTrace (prefixWord ++ tailWord_579182) baseStart_579182 baseEnd_579182 := by
    simpa [prefixWord, tailWord_579182, baseEnd_579182] using wordTrace_append hprefix tailTrace_579182
  have hstable : (prefixWord ++ tailWord_579182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579182).length < 2 ^ (prefixWord ++ tailWord_579182).sum := by decide
  have hdescent : baseEnd_579182 < baseStart_579182 := by decide
  rcases family_descends (prefixWord ++ tailWord_579182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579201 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_579201 : Nat := 118140960795 + 579201 * 2 ^ 59
def prefixEnd_579201 : Nat := 4983230072969 + 3 ^ 40 * 579201 * 2
def baseEnd_579201 : Nat := 99136169521631202374603

theorem tailTrace_579201 : CollatzResearch.WordTrace tailWord_579201 prefixEnd_579201 99136169521631202374603 := by
  unfold tailWord_579201
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125195974661171500513457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14083463983107447667008971 21125195974661171500513457)
  ·
    refine ⟨15843896980995878625385093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21125195974661171500513457 15843896980995878625385093)
    ·
      refine ⟨2970730683936727242259705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15843896980995878625385093 2970730683936727242259705)
      ·
        refine ⟨2228048012952545431694779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2970730683936727242259705 2228048012952545431694779)
        ·
          refine ⟨3342072019428818147542169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2228048012952545431694779 3342072019428818147542169)
          ·
            refine ⟨2506554014571613610656627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3342072019428818147542169 2506554014571613610656627)
            ·
              refine ⟨3759831021857420415984941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2506554014571613610656627 3759831021857420415984941)
              ·
                refine ⟨1409936633196532655994353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3759831021857420415984941 1409936633196532655994353)
                ·
                  refine ⟨1057452474897399491995765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1409936633196532655994353 1057452474897399491995765)
                  ·
                    refine ⟨99136169521631202374603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1057452474897399491995765 99136169521631202374603)
                    ·
                      rfl

theorem cell23_579201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_579201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579201 prefixEnd_579201 := by exact prefixLift 579201
  have htrace : WordTrace (prefixWord ++ tailWord_579201) baseStart_579201 baseEnd_579201 := by
    simpa [prefixWord, tailWord_579201, baseEnd_579201] using wordTrace_append hprefix tailTrace_579201
  have hstable : (prefixWord ++ tailWord_579201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579201).length < 2 ^ (prefixWord ++ tailWord_579201).sum := by decide
  have hdescent : baseEnd_579201 < baseStart_579201 := by decide
  rcases family_descends (prefixWord ++ tailWord_579201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579221 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 6, 2]
def baseStart_579221 : Nat := 118140960795 + 579221 * 2 ^ 59
def prefixEnd_579221 : Nat := 4983230072969 + 3 ^ 40 * 579221 * 2
def baseEnd_579221 : Nat := 297418778177983528873717

theorem tailTrace_579221 : CollatzResearch.WordTrace tailWord_579221 prefixEnd_579221 297418778177983528873717 := by
  unfold tailWord_579221
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125925434588714916241517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14083950289725809944161011 21125925434588714916241517)
  ·
    refine ⟨7922222037970768093590569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21125925434588714916241517 7922222037970768093590569)
    ·
      refine ⟨5941666528478076070192927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7922222037970768093590569 5941666528478076070192927)
      ·
        refine ⟨8912499792717114105289391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5941666528478076070192927 8912499792717114105289391)
        ·
          refine ⟨13368749689075671157934087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912499792717114105289391 13368749689075671157934087)
          ·
            refine ⟨20053124533613506736901131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13368749689075671157934087 20053124533613506736901131)
            ·
              refine ⟨30079686800420260105351697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20053124533613506736901131 30079686800420260105351697)
              ·
                refine ⟨22559765100315195079013773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30079686800420260105351697 22559765100315195079013773)
                ·
                  refine ⟨8459911912618198154630165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22559765100315195079013773 8459911912618198154630165)
                  ·
                    refine ⟨396558370903978038498289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8459911912618198154630165 396558370903978038498289)
                    ·
                      refine ⟨297418778177983528873717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396558370903978038498289 297418778177983528873717)
                      ·
                        rfl

theorem cell23_579221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_579221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579221 prefixEnd_579221 := by exact prefixLift 579221
  have htrace : WordTrace (prefixWord ++ tailWord_579221) baseStart_579221 baseEnd_579221 := by
    simpa [prefixWord, tailWord_579221, baseEnd_579221] using wordTrace_append hprefix tailTrace_579221
  have hstable : (prefixWord ++ tailWord_579221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579221).length < 2 ^ (prefixWord ++ tailWord_579221).sum := by decide
  have hdescent : baseEnd_579221 < baseStart_579221 := by decide
  rcases family_descends (prefixWord ++ tailWord_579221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579258 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_579258 : Nat := 118140960795 + 579258 * 2 ^ 59
def prefixEnd_579258 : Nat := 4983230072969 + 3 ^ 40 * 579258 * 2
def baseEnd_579258 : Nat := 297437776962199884111047

theorem tailTrace_579258 : CollatzResearch.WordTrace tailWord_579258 prefixEnd_579258 297437776962199884111047 := by
  unfold tailWord_579258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5281818733863667558834607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14084849956969780156892285 5281818733863667558834607)
  ·
    refine ⟨7922728100795501338251911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5281818733863667558834607 7922728100795501338251911)
    ·
      refine ⟨11884092151193252007377867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7922728100795501338251911 11884092151193252007377867)
      ·
        refine ⟨17826138226789878011066801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11884092151193252007377867 17826138226789878011066801)
        ·
          refine ⟨13369603670092408508300101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17826138226789878011066801 13369603670092408508300101)
          ·
            refine ⟨2506800688142326595306269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13369603670092408508300101 2506800688142326595306269)
            ·
              refine ⟨940050258053372473239851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2506800688142326595306269 940050258053372473239851)
              ·
                refine ⟨1410075387080058709859777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940050258053372473239851 1410075387080058709859777)
                ·
                  refine ⟨1057556540310044032394833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410075387080058709859777 1057556540310044032394833)
                  ·
                    refine ⟨793167405232533024296125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057556540310044032394833 793167405232533024296125)
                    ·
                      refine ⟨297437776962199884111047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793167405232533024296125 297437776962199884111047)
                      ·
                        rfl

theorem cell23_579258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_579258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579258 prefixEnd_579258 := by exact prefixLift 579258
  have htrace : WordTrace (prefixWord ++ tailWord_579258) baseStart_579258 baseEnd_579258 := by
    simpa [prefixWord, tailWord_579258, baseEnd_579258] using wordTrace_append hprefix tailTrace_579258
  have hstable : (prefixWord ++ tailWord_579258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579258).length < 2 ^ (prefixWord ++ tailWord_579258).sum := by decide
  have hdescent : baseEnd_579258 < baseStart_579258 := by decide
  rcases family_descends (prefixWord ++ tailWord_579258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579316 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_579316 : Nat := 118140960795 + 579316 * 2 ^ 59
def prefixEnd_579316 : Nat := 4983230072969 + 3 ^ 40 * 579316 * 2
def baseEnd_579316 : Nat := 99155852946720219061927

theorem tailTrace_579316 : CollatzResearch.WordTrace tailWord_579316 prefixEnd_579316 99155852946720219061927 := by
  unfold tailWord_579316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10564695184622273070474901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14086260246163030760633201 10564695184622273070474901)
  ·
    refine ⟨495220086779169050178511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10564695184622273070474901 495220086779169050178511)
    ·
      refine ⟨742830130168753575267767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495220086779169050178511 742830130168753575267767)
      ·
        refine ⟨1114245195253130362901651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742830130168753575267767 1114245195253130362901651)
        ·
          refine ⟨1671367792879695544352477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114245195253130362901651 1671367792879695544352477)
          ·
            refine ⟨626762922329885829132179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1671367792879695544352477 626762922329885829132179)
            ·
              refine ⟨940144383494828743698269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626762922329885829132179 940144383494828743698269)
              ·
                refine ⟨352554143810560778886851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940144383494828743698269 352554143810560778886851)
                ·
                  refine ⟨528831215715841168330277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352554143810560778886851 528831215715841168330277)
                  ·
                    refine ⟨99155852946720219061927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528831215715841168330277 99155852946720219061927)
                    ·
                      rfl

theorem cell23_579316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_579316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579316 prefixEnd_579316 := by exact prefixLift 579316
  have htrace : WordTrace (prefixWord ++ tailWord_579316) baseStart_579316 baseEnd_579316 := by
    simpa [prefixWord, tailWord_579316, baseEnd_579316] using wordTrace_append hprefix tailTrace_579316
  have hstable : (prefixWord ++ tailWord_579316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579316).length < 2 ^ (prefixWord ++ tailWord_579316).sum := by decide
  have hdescent : baseEnd_579316 < baseStart_579316 := by decide
  rcases family_descends (prefixWord ++ tailWord_579316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579331 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5]
def baseStart_579331 : Nat := 118140960795 + 579331 * 2 ^ 59
def prefixEnd_579331 : Nat := 4983230072969 + 3 ^ 40 * 579331 * 2
def baseEnd_579331 : Nat := 297475261049978098498211

theorem tailTrace_579331 : CollatzResearch.WordTrace tailWord_579331 prefixEnd_579331 297475261049978098498211 := by
  unfold tailWord_579331
  simp only [CollatzResearch.WordTrace]
  refine ⟨21129937464190203702745847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14086624976126802468497231 21129937464190203702745847)
  ·
    refine ⟨31694906196285305554118771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21129937464190203702745847 31694906196285305554118771)
    ·
      refine ⟨47542359294427958331178157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31694906196285305554118771 47542359294427958331178157)
      ·
        refine ⟨17828384735410484374191809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47542359294427958331178157 17828384735410484374191809)
        ·
          refine ⟨13371288551557863280643857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17828384735410484374191809 13371288551557863280643857)
          ·
            refine ⟨10028466413668397460482893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13371288551557863280643857 10028466413668397460482893)
            ·
              refine ⟨3760674905125649047681085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10028466413668397460482893 3760674905125649047681085)
              ·
                refine ⟨1410253089422118392880407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3760674905125649047681085 1410253089422118392880407)
                ·
                  refine ⟨2115379634133177589320611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410253089422118392880407 2115379634133177589320611)
                  ·
                    refine ⟨3173069451199766383980917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115379634133177589320611 3173069451199766383980917)
                    ·
                      refine ⟨297475261049978098498211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3173069451199766383980917 297475261049978098498211)
                      ·
                        rfl

theorem cell23_579331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_579331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579331 prefixEnd_579331 := by exact prefixLift 579331
  have htrace : WordTrace (prefixWord ++ tailWord_579331) baseStart_579331 baseEnd_579331 := by
    simpa [prefixWord, tailWord_579331, baseEnd_579331] using wordTrace_append hprefix tailTrace_579331
  have hstable : (prefixWord ++ tailWord_579331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579331).length < 2 ^ (prefixWord ++ tailWord_579331).sum := by decide
  have hdescent : baseEnd_579331 < baseStart_579331 := by decide
  rcases family_descends (prefixWord ++ tailWord_579331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579338 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_579338 : Nat := 118140960795 + 579338 * 2 ^ 59
def prefixEnd_579338 : Nat := 4983230072969 + 3 ^ 40 * 579338 * 2
def baseEnd_579338 : Nat := 99159618471519857036893

theorem tailTrace_579338 : CollatzResearch.WordTrace tailWord_579338 prefixEnd_579338 99159618471519857036893 := by
  unfold tailWord_579338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282548193791210974562667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14086795183443229265500445 5282548193791210974562667)
  ·
    refine ⟨7923822290686816461844001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5282548193791210974562667 7923822290686816461844001)
    ·
      refine ⟨5942866718015112346383001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7923822290686816461844001 5942866718015112346383001)
      ·
        refine ⟨4457150038511334259787251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5942866718015112346383001 4457150038511334259787251)
        ·
          refine ⟨6685725057767001389680877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4457150038511334259787251 6685725057767001389680877)
          ·
            refine ⟨2507146896662625521130329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6685725057767001389680877 2507146896662625521130329)
            ·
              refine ⟨1880360172496969140847747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2507146896662625521130329 1880360172496969140847747)
              ·
                refine ⟨2820540258745453711271621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1880360172496969140847747 2820540258745453711271621)
                ·
                  refine ⟨528851298514772570863429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2820540258745453711271621 528851298514772570863429)
                  ·
                    refine ⟨99159618471519857036893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 528851298514772570863429 99159618471519857036893)
                    ·
                      rfl

theorem cell23_579338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_579338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579338 prefixEnd_579338 := by exact prefixLift 579338
  have htrace : WordTrace (prefixWord ++ tailWord_579338) baseStart_579338 baseEnd_579338 := by
    simpa [prefixWord, tailWord_579338, baseEnd_579338] using wordTrace_append hprefix tailTrace_579338
  have hstable : (prefixWord ++ tailWord_579338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579338).length < 2 ^ (prefixWord ++ tailWord_579338).sum := by decide
  have hdescent : baseEnd_579338 < baseStart_579338 := by decide
  rcases family_descends (prefixWord ++ tailWord_579338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579351 : List Nat := [1, 1, 3, 4, 2, 1, 1, 10]
def baseStart_579351 : Nat := 118140960795 + 579351 * 2 ^ 59
def prefixEnd_579351 : Nat := 4983230072969 + 3 ^ 40 * 579351 * 2
def baseEnd_579351 : Nat := 11017982617150667416597

theorem tailTrace_579351 : CollatzResearch.WordTrace tailWord_579351 prefixEnd_579351 11017982617150667416597 := by
  unfold tailWord_579351
  simp only [CollatzResearch.WordTrace]
  refine ⟨21130666924117747118473907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14087111282745164745649271 21130666924117747118473907)
  ·
    refine ⟨31696000386176620677710861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21130666924117747118473907 31696000386176620677710861)
    ·
      refine ⟨11886000144816232754141573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31696000386176620677710861 11886000144816232754141573)
      ·
        refine ⟨2228625027153043641401545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11886000144816232754141573 2228625027153043641401545)
        ·
          refine ⟨1671468770364782731051159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2228625027153043641401545 1671468770364782731051159)
          ·
            refine ⟨2507203155547174096576739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671468770364782731051159 2507203155547174096576739)
            ·
              refine ⟨3760804733320761144865109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507203155547174096576739 3760804733320761144865109)
              ·
                refine ⟨11017982617150667416597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3760804733320761144865109 11017982617150667416597)
                ·
                  rfl

theorem cell23_579351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 10].length) (baseStart_579351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579351 prefixEnd_579351 := by exact prefixLift 579351
  have htrace : WordTrace (prefixWord ++ tailWord_579351) baseStart_579351 baseEnd_579351 := by
    simpa [prefixWord, tailWord_579351, baseEnd_579351] using wordTrace_append hprefix tailTrace_579351
  have hstable : (prefixWord ++ tailWord_579351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579351).length < 2 ^ (prefixWord ++ tailWord_579351).sum := by decide
  have hdescent : baseEnd_579351 < baseStart_579351 := by decide
  rcases family_descends (prefixWord ++ tailWord_579351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579365 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_579365 : Nat := 118140960795 + 579365 * 2 ^ 59
def prefixEnd_579365 : Nat := 4983230072969 + 3 ^ 40 * 579365 * 2
def baseEnd_579365 : Nat := 297492719392230965473055

theorem tailTrace_579365 : CollatzResearch.WordTrace tailWord_579365 prefixEnd_579365 297492719392230965473055 := by
  unfold tailWord_579365
  simp only [CollatzResearch.WordTrace]
  refine ⟨21131177546067027509483549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14087451697378018339655699 21131177546067027509483549)
  ·
    refine ⟨7924191579775135316056331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21131177546067027509483549 7924191579775135316056331)
    ·
      refine ⟨11886287369662702974084497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7924191579775135316056331 11886287369662702974084497)
      ·
        refine ⟨8914715527247027230563373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11886287369662702974084497 8914715527247027230563373)
        ·
          refine ⟨3343018322717635211461265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8914715527247027230563373 3343018322717635211461265)
          ·
            refine ⟨2507263742038226408595949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343018322717635211461265 2507263742038226408595949)
            ·
              refine ⟨940223903264334903223481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2507263742038226408595949 940223903264334903223481)
              ·
                refine ⟨705167927448251177417611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940223903264334903223481 705167927448251177417611)
                ·
                  refine ⟨1057751891172376766126417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705167927448251177417611 1057751891172376766126417)
                  ·
                    refine ⟨793313918379282574594813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1057751891172376766126417 793313918379282574594813)
                    ·
                      refine ⟨297492719392230965473055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793313918379282574594813 297492719392230965473055)
                      ·
                        rfl

theorem cell23_579365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_579365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579365 prefixEnd_579365 := by exact prefixLift 579365
  have htrace : WordTrace (prefixWord ++ tailWord_579365) baseStart_579365 baseEnd_579365 := by
    simpa [prefixWord, tailWord_579365, baseEnd_579365] using wordTrace_append hprefix tailTrace_579365
  have hstable : (prefixWord ++ tailWord_579365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579365).length < 2 ^ (prefixWord ++ tailWord_579365).sum := by decide
  have hdescent : baseEnd_579365 < baseStart_579365 := by decide
  rcases family_descends (prefixWord ++ tailWord_579365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579378 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_579378 : Nat := 118140960795 + 579378 * 2 ^ 59
def prefixEnd_579378 : Nat := 4983230072969 + 3 ^ 40 * 579378 * 2
def baseEnd_579378 : Nat := 297499394640739414610495

theorem tailTrace_579378 : CollatzResearch.WordTrace tailWord_579378 prefixEnd_579378 297499394640739414610495 := by
  unfold tailWord_579378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282912923754982682426697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14087767796679953819804525 5282912923754982682426697)
  ·
    refine ⟨3962184692816237011820023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5282912923754982682426697 3962184692816237011820023)
    ·
      refine ⟨5943277039224355517730035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962184692816237011820023 5943277039224355517730035)
      ·
        refine ⟨8914915558836533276595053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5943277039224355517730035 8914915558836533276595053)
        ·
          refine ⟨3343093334563699978723145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8914915558836533276595053 3343093334563699978723145)
          ·
            refine ⟨2507320000922774984042359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3343093334563699978723145 2507320000922774984042359)
            ·
              refine ⟨3760980001384162476063539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507320000922774984042359 3760980001384162476063539)
              ·
                refine ⟨5641470002076243714095309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760980001384162476063539 5641470002076243714095309)
                ·
                  refine ⟨2115551250778591392785741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5641470002076243714095309 2115551250778591392785741)
                  ·
                    refine ⟨793331719041971772294653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2115551250778591392785741 793331719041971772294653)
                    ·
                      refine ⟨297499394640739414610495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793331719041971772294653 297499394640739414610495)
                      ·
                        rfl

theorem cell23_579378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_579378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579378 prefixEnd_579378 := by exact prefixLift 579378
  have htrace : WordTrace (prefixWord ++ tailWord_579378) baseStart_579378 baseEnd_579378 := by
    simpa [prefixWord, tailWord_579378, baseEnd_579378] using wordTrace_append hprefix tailTrace_579378
  have hstable : (prefixWord ++ tailWord_579378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579378).length < 2 ^ (prefixWord ++ tailWord_579378).sum := by decide
  have hdescent : baseEnd_579378 < baseStart_579378 := by decide
  rcases family_descends (prefixWord ++ tailWord_579378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579382 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_579382 : Nat := 118140960795 + 579382 * 2 ^ 59
def prefixEnd_579382 : Nat := 4983230072969 + 3 ^ 40 * 579382 * 2
def baseEnd_579382 : Nat := 297501448563357398960477

theorem tailTrace_579382 : CollatzResearch.WordTrace tailWord_579382 prefixEnd_579382 297501448563357398960477 := by
  unfold tailWord_579382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320737349187839963303275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14087865058003626275234933 1320737349187839963303275)
  ·
    refine ⟨1981106023781759944954913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320737349187839963303275 1981106023781759944954913)
    ·
      refine ⟨1485829517836319958716185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981106023781759944954913 1485829517836319958716185)
      ·
        refine ⟨1114372138377239969037139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1485829517836319958716185 1114372138377239969037139)
        ·
          refine ⟨1671558207565859953555709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114372138377239969037139 1671558207565859953555709)
          ·
            refine ⟨626834327837197482583391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1671558207565859953555709 626834327837197482583391)
            ·
              refine ⟨940251491755796223875087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626834327837197482583391 940251491755796223875087)
              ·
                refine ⟨1410377237633694335812631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940251491755796223875087 1410377237633694335812631)
                ·
                  refine ⟨2115565856450541503718947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1410377237633694335812631 2115565856450541503718947)
                  ·
                    refine ⟨3173348784675812255578421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2115565856450541503718947 3173348784675812255578421)
                    ·
                      refine ⟨297501448563357398960477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3173348784675812255578421 297501448563357398960477)
                      ·
                        rfl

theorem cell23_579382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_579382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579382 prefixEnd_579382 := by exact prefixLift 579382
  have htrace : WordTrace (prefixWord ++ tailWord_579382) baseStart_579382 baseEnd_579382 := by
    simpa [prefixWord, tailWord_579382, baseEnd_579382] using wordTrace_append hprefix tailTrace_579382
  have hstable : (prefixWord ++ tailWord_579382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579382).length < 2 ^ (prefixWord ++ tailWord_579382).sum := by decide
  have hdescent : baseEnd_579382 < baseStart_579382 := by decide
  rcases family_descends (prefixWord ++ tailWord_579382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579395 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 3]
def baseStart_579395 : Nat := 118140960795 + 579395 * 2 ^ 59
def prefixEnd_579395 : Nat := 4983230072969 + 3 ^ 40 * 579395 * 2
def baseEnd_579395 : Nat := 297508123811865848097917

theorem tailTrace_579395 : CollatzResearch.WordTrace tailWord_579395 prefixEnd_579395 297508123811865848097917 := by
  unfold tailWord_579395
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132271735958342633075639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14088181157305561755383759 21132271735958342633075639)
  ·
    refine ⟨31698407603937513949613459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21132271735958342633075639 31698407603937513949613459)
    ·
      refine ⟨47547611405906270924420189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31698407603937513949613459 47547611405906270924420189)
      ·
        refine ⟨17830354277214851596657571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47547611405906270924420189 17830354277214851596657571)
        ·
          refine ⟨26745531415822277394986357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17830354277214851596657571 26745531415822277394986357)
          ·
            refine ⟨2507393570233338505779971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26745531415822277394986357 2507393570233338505779971)
            ·
              refine ⟨3761090355350007758669957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2507393570233338505779971 3761090355350007758669957)
              ·
                refine ⟨705204441628126454750617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3761090355350007758669957 705204441628126454750617)
                ·
                  refine ⟨528903331221094841062963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705204441628126454750617 528903331221094841062963)
                  ·
                    refine ⟨793354996831642261594445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528903331221094841062963 793354996831642261594445)
                    ·
                      refine ⟨297508123811865848097917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793354996831642261594445 297508123811865848097917)
                      ·
                        rfl

theorem cell23_579395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_579395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579395 prefixEnd_579395 := by exact prefixLift 579395
  have htrace : WordTrace (prefixWord ++ tailWord_579395) baseStart_579395 baseEnd_579395 := by
    simpa [prefixWord, tailWord_579395, baseEnd_579395] using wordTrace_append hprefix tailTrace_579395
  have hstable : (prefixWord ++ tailWord_579395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579395).length < 2 ^ (prefixWord ++ tailWord_579395).sum := by decide
  have hdescent : baseEnd_579395 < baseStart_579395 := by decide
  rcases family_descends (prefixWord ++ tailWord_579395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579401 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_579401 : Nat := 118140960795 + 579401 * 2 ^ 59
def prefixEnd_579401 : Nat := 4983230072969 + 3 ^ 40 * 579401 * 2
def baseEnd_579401 : Nat := 297511204695792824622889

theorem tailTrace_579401 : CollatzResearch.WordTrace tailWord_579401 prefixEnd_579401 297511204695792824622889 := by
  unfold tailWord_579401
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132490573936605657794057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14088327049291070438529371 21132490573936605657794057)
  ·
    refine ⟨15849367930452454243345543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21132490573936605657794057 15849367930452454243345543)
    ·
      refine ⟨23774051895678681365018315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15849367930452454243345543 23774051895678681365018315)
      ·
        refine ⟨35661077843518022047527473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23774051895678681365018315 35661077843518022047527473)
        ·
          refine ⟨26745808382638516535645605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35661077843518022047527473 26745808382638516535645605)
          ·
            refine ⟨5014839071744721850433551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26745808382638516535645605 5014839071744721850433551)
            ·
              refine ⟨7522258607617082775650327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014839071744721850433551 7522258607617082775650327)
              ·
                refine ⟨11283387911425624163475491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522258607617082775650327 11283387911425624163475491)
                ·
                  refine ⟨16925081867138436245213237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11283387911425624163475491 16925081867138436245213237)
                  ·
                    refine ⟨1586726425044228397988741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16925081867138436245213237 1586726425044228397988741)
                    ·
                      refine ⟨297511204695792824622889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1586726425044228397988741 297511204695792824622889)
                      ·
                        rfl

theorem cell23_579401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_579401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579401 prefixEnd_579401 := by exact prefixLift 579401
  have htrace : WordTrace (prefixWord ++ tailWord_579401) baseStart_579401 baseEnd_579401 := by
    simpa [prefixWord, tailWord_579401, baseEnd_579401] using wordTrace_append hprefix tailTrace_579401
  have hstable : (prefixWord ++ tailWord_579401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579401).length < 2 ^ (prefixWord ++ tailWord_579401).sum := by decide
  have hdescent : baseEnd_579401 < baseStart_579401 := by decide
  rcases family_descends (prefixWord ++ tailWord_579401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579412 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_579412 : Nat := 118140960795 + 579412 * 2 ^ 59
def prefixEnd_579412 : Nat := 4983230072969 + 3 ^ 40 * 579412 * 2
def baseEnd_579412 : Nat := 297516852982992281585339

theorem tailTrace_579412 : CollatzResearch.WordTrace tailWord_579412 prefixEnd_579412 297516852982992281585339 := by
  unfold tailWord_579412
  simp only [CollatzResearch.WordTrace]
  refine ⟨10566445888448377268222245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14088594517931169690962993 10566445888448377268222245)
  ·
    refine ⟨1981208604084070737791671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10566445888448377268222245 1981208604084070737791671)
    ·
      refine ⟨2971812906126106106687507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981208604084070737791671 2971812906126106106687507)
      ·
        refine ⟨4457719359189159160031261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2971812906126106106687507 4457719359189159160031261)
        ·
          refine ⟨1671644759695934685011723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4457719359189159160031261 1671644759695934685011723)
          ·
            refine ⟨2507467139543902027517585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1671644759695934685011723 2507467139543902027517585)
            ·
              refine ⟨1880600354657926520638189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2507467139543902027517585 1880600354657926520638189)
              ·
                refine ⟨705225132996722445239321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1880600354657926520638189 705225132996722445239321)
                ·
                  refine ⟨528918849747541833929491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705225132996722445239321 528918849747541833929491)
                  ·
                    refine ⟨793378274621312750894237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528918849747541833929491 793378274621312750894237)
                    ·
                      refine ⟨297516852982992281585339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793378274621312750894237 297516852982992281585339)
                      ·
                        rfl

theorem cell23_579412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_579412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579412 prefixEnd_579412 := by exact prefixLift 579412
  have htrace : WordTrace (prefixWord ++ tailWord_579412) baseStart_579412 baseEnd_579412 := by
    simpa [prefixWord, tailWord_579412, baseEnd_579412] using wordTrace_append hprefix tailTrace_579412
  have hstable : (prefixWord ++ tailWord_579412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579412).length < 2 ^ (prefixWord ++ tailWord_579412).sum := by decide
  have hdescent : baseEnd_579412 < baseStart_579412 := by decide
  rcases family_descends (prefixWord ++ tailWord_579412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579435 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 4, 2, 2]
def baseStart_579435 : Nat := 118140960795 + 579435 * 2 ^ 59
def prefixEnd_579435 : Nat := 4983230072969 + 3 ^ 40 * 579435 * 2
def baseEnd_579435 : Nat := 297528663038045691597733

theorem tailTrace_579435 : CollatzResearch.WordTrace tailWord_579435 prefixEnd_579435 297528663038045691597733 := by
  unfold tailWord_579435
  simp only [CollatzResearch.WordTrace]
  refine ⟨21133730655813429464531759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14089153770542286309687839 21133730655813429464531759)
  ·
    refine ⟨31700595983720144196797639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21133730655813429464531759 31700595983720144196797639)
    ·
      refine ⟨47550893975580216295196459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31700595983720144196797639 47550893975580216295196459)
      ·
        refine ⟨71326340963370324442794689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47550893975580216295196459 71326340963370324442794689)
        ·
          refine ⟨53494755722527743332096017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71326340963370324442794689 53494755722527743332096017)
          ·
            refine ⟨40121066791895807499072013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53494755722527743332096017 40121066791895807499072013)
            ·
              refine ⟨15045400046960927812152005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40121066791895807499072013 15045400046960927812152005)
              ·
                refine ⟨2821012508805173964778501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15045400046960927812152005 2821012508805173964778501)
                ·
                  refine ⟨528939845400970118395969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2821012508805173964778501 528939845400970118395969)
                  ·
                    refine ⟨396704884050727588796977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 528939845400970118395969 396704884050727588796977)
                    ·
                      refine ⟨297528663038045691597733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396704884050727588796977 297528663038045691597733)
                      ·
                        rfl

theorem cell23_579435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2, 2].length) (baseStart_579435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579435 prefixEnd_579435 := by exact prefixLift 579435
  have htrace : WordTrace (prefixWord ++ tailWord_579435) baseStart_579435 baseEnd_579435 := by
    simpa [prefixWord, tailWord_579435, baseEnd_579435] using wordTrace_append hprefix tailTrace_579435
  have hstable : (prefixWord ++ tailWord_579435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579435).length < 2 ^ (prefixWord ++ tailWord_579435).sum := by decide
  have hdescent : baseEnd_579435 < baseStart_579435 := by decide
  rcases family_descends (prefixWord ++ tailWord_579435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579441 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 9]
def baseStart_579441 : Nat := 118140960795 + 579441 * 2 ^ 59
def prefixEnd_579441 : Nat := 4983230072969 + 3 ^ 40 * 579441 * 2
def baseEnd_579441 : Nat := 33059082657996963124745

theorem tailTrace_579441 : CollatzResearch.WordTrace tailWord_579441 prefixEnd_579441 33059082657996963124745 := by
  unfold tailWord_579441
  simp only [CollatzResearch.WordTrace]
  refine ⟨21133949493791692489250177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14089299662527794992833451 21133949493791692489250177)
  ·
    refine ⟨15850462120343769366937633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21133949493791692489250177 15850462120343769366937633)
    ·
      refine ⟨11887846590257827025203225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15850462120343769366937633 11887846590257827025203225)
      ·
        refine ⟨8915884942693370268902419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11887846590257827025203225 8915884942693370268902419)
        ·
          refine ⟨13373827414040055403353629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8915884942693370268902419 13373827414040055403353629)
          ·
            refine ⟨5015185280265020776257611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13373827414040055403353629 5015185280265020776257611)
            ·
              refine ⟨7522777920397531164386417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015185280265020776257611 7522777920397531164386417)
              ·
                refine ⟨5642083440298148373289813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7522777920397531164386417 5642083440298148373289813)
                ·
                  refine ⟨33059082657996963124745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5642083440298148373289813 33059082657996963124745)
                  ·
                    rfl

theorem cell23_579441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_579441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579441 prefixEnd_579441 := by exact prefixLift 579441
  have htrace : WordTrace (prefixWord ++ tailWord_579441) baseStart_579441 baseEnd_579441 := by
    simpa [prefixWord, tailWord_579441, baseEnd_579441] using wordTrace_append hprefix tailTrace_579441
  have hstable : (prefixWord ++ tailWord_579441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579441).length < 2 ^ (prefixWord ++ tailWord_579441).sum := by decide
  have hdescent : baseEnd_579441 < baseStart_579441 := by decide
  rcases family_descends (prefixWord ++ tailWord_579441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579446 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_579446 : Nat := 118140960795 + 579446 * 2 ^ 59
def prefixEnd_579446 : Nat := 4983230072969 + 3 ^ 40 * 579446 * 2
def baseEnd_579446 : Nat := 297534311325245148560183

theorem tailTrace_579446 : CollatzResearch.WordTrace tailWord_579446 prefixEnd_579446 297534311325245148560183 := by
  unfold tailWord_579446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1320883241173348646448887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14089421239182385562121461 1320883241173348646448887)
  ·
    refine ⟨1981324861760022969673331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1320883241173348646448887 1981324861760022969673331)
    ·
      refine ⟨2971987292640034454509997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1981324861760022969673331 2971987292640034454509997)
      ·
        refine ⟨1114495234740012920441249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2971987292640034454509997 1114495234740012920441249)
        ·
          refine ⟨835871426055009690330937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1114495234740012920441249 835871426055009690330937)
          ·
            refine ⟨626903569541257267748203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 835871426055009690330937 626903569541257267748203)
            ·
              refine ⟨940355354311885901622305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626903569541257267748203 940355354311885901622305)
              ·
                refine ⟨705266515733914426216729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940355354311885901622305 705266515733914426216729)
                ·
                  refine ⟨528949886800435819662547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 705266515733914426216729 528949886800435819662547)
                  ·
                    refine ⟨793424830200653729493821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 528949886800435819662547 793424830200653729493821)
                    ·
                      refine ⟨297534311325245148560183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793424830200653729493821 297534311325245148560183)
                      ·
                        rfl

theorem cell23_579446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_579446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579446 prefixEnd_579446 := by exact prefixLift 579446
  have htrace : WordTrace (prefixWord ++ tailWord_579446) baseStart_579446 baseEnd_579446 := by
    simpa [prefixWord, tailWord_579446, baseEnd_579446] using wordTrace_append hprefix tailTrace_579446
  have hstable : (prefixWord ++ tailWord_579446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579446).length < 2 ^ (prefixWord ++ tailWord_579446).sum := by decide
  have hdescent : baseEnd_579446 < baseStart_579446 := by decide
  rcases family_descends (prefixWord ++ tailWord_579446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579488 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_579488 : Nat := 118140960795 + 579488 * 2 ^ 59
def prefixEnd_579488 : Nat := 4983230072969 + 3 ^ 40 * 579488 * 2
def baseEnd_579488 : Nat := 99185292504244661411663

theorem tailTrace_579488 : CollatzResearch.WordTrace tailWord_579488 prefixEnd_579488 99185292504244661411663 := by
  unfold tailWord_579488
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567831862310709758105559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14090442483080946344140745 10567831862310709758105559)
  ·
    refine ⟨15851747793466064637158339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10567831862310709758105559 15851747793466064637158339)
    ·
      refine ⟨23777621690199096955737509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15851747793466064637158339 23777621690199096955737509)
      ·
        refine ⟨4458304066912330679200783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23777621690199096955737509 4458304066912330679200783)
        ·
          refine ⟨6687456100368496018801175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458304066912330679200783 6687456100368496018801175)
          ·
            refine ⟨10031184150552744028201763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687456100368496018801175 10031184150552744028201763)
            ·
              refine ⟨15046776225829116042302645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10031184150552744028201763 15046776225829116042302645)
              ·
                refine ⟨1410635271171479628965873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15046776225829116042302645 1410635271171479628965873)
                ·
                  refine ⟨1057976453378609721724405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410635271171479628965873 1057976453378609721724405)
                  ·
                    refine ⟨99185292504244661411663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1057976453378609721724405 99185292504244661411663)
                    ·
                      rfl

theorem cell23_579488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_579488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579488 prefixEnd_579488 := by exact prefixLift 579488
  have htrace : WordTrace (prefixWord ++ tailWord_579488) baseStart_579488 baseEnd_579488 := by
    simpa [prefixWord, tailWord_579488, baseEnd_579488] using wordTrace_append hprefix tailTrace_579488
  have hstable : (prefixWord ++ tailWord_579488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579488).length < 2 ^ (prefixWord ++ tailWord_579488).sum := by decide
  have hdescent : baseEnd_579488 < baseStart_579488 := by decide
  rcases family_descends (prefixWord ++ tailWord_579488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579492 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 5]
def baseStart_579492 : Nat := 118140960795 + 579492 * 2 ^ 59
def prefixEnd_579492 : Nat := 4983230072969 + 3 ^ 40 * 579492 * 2
def baseEnd_579492 : Nat := 33061992381705774287219

theorem tailTrace_579492 : CollatzResearch.WordTrace tailWord_579492 prefixEnd_579492 33061992381705774287219 := by
  unfold tailWord_579492
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567904808303464099678365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14090539744404618799571153 10567904808303464099678365)
  ·
    refine ⟨3962964303113799037379387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10567904808303464099678365 3962964303113799037379387)
    ·
      refine ⟨5944446454670698556069081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962964303113799037379387 5944446454670698556069081)
      ·
        refine ⟨4458334841003023917051811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5944446454670698556069081 4458334841003023917051811)
        ·
          refine ⟨6687502261504535875577717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458334841003023917051811 6687502261504535875577717)
          ·
            refine ⟨626953337016050238335411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6687502261504535875577717 626953337016050238335411)
            ·
              refine ⟨940430005524075357503117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 626953337016050238335411 940430005524075357503117)
              ·
                refine ⟨352661252071528259063669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 940430005524075357503117 352661252071528259063669)
                ·
                  refine ⟨33061992381705774287219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352661252071528259063669 33061992381705774287219)
                  ·
                    rfl

theorem cell23_579492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_579492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579492 prefixEnd_579492 := by exact prefixLift 579492
  have htrace : WordTrace (prefixWord ++ tailWord_579492) baseStart_579492 baseEnd_579492 := by
    simpa [prefixWord, tailWord_579492, baseEnd_579492] using wordTrace_append hprefix tailTrace_579492
  have hstable : (prefixWord ++ tailWord_579492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579492).length < 2 ^ (prefixWord ++ tailWord_579492).sum := by decide
  have hdescent : baseEnd_579492 < baseStart_579492 := by decide
  rcases family_descends (prefixWord ++ tailWord_579492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579505 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_579505 : Nat := 118140960795 + 579505 * 2 ^ 59
def prefixEnd_579505 : Nat := 4983230072969 + 3 ^ 40 * 579505 * 2
def baseEnd_579505 : Nat := 99188202227953472574137

theorem tailTrace_579505 : CollatzResearch.WordTrace tailWord_579505 prefixEnd_579505 99188202227953472574137 := by
  unfold tailWord_579505
  simp only [CollatzResearch.WordTrace]
  refine ⟨21136283765559831419579969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14090855843706554279719979 21136283765559831419579969)
  ·
    refine ⟨15852212824169873564684977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21136283765559831419579969 15852212824169873564684977)
    ·
      refine ⟨11889159618127405173513733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15852212824169873564684977 11889159618127405173513733)
      ·
        refine ⟨2229217428398888470033825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11889159618127405173513733 2229217428398888470033825)
        ·
          refine ⟨1671913071299166352525369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229217428398888470033825 1671913071299166352525369)
          ·
            refine ⟨1253934803474374764394027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1671913071299166352525369 1253934803474374764394027)
            ·
              refine ⟨1880902205211562146591041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1253934803474374764394027 1880902205211562146591041)
              ·
                refine ⟨1410676653908671609943281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1880902205211562146591041 1410676653908671609943281)
                ·
                  refine ⟨1058007490431503707457461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410676653908671609943281 1058007490431503707457461)
                  ·
                    refine ⟨99188202227953472574137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1058007490431503707457461 99188202227953472574137)
                    ·
                      rfl

theorem cell23_579505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_579505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579505 prefixEnd_579505 := by exact prefixLift 579505
  have htrace : WordTrace (prefixWord ++ tailWord_579505) baseStart_579505 baseEnd_579505 := by
    simpa [prefixWord, tailWord_579505, baseEnd_579505] using wordTrace_append hprefix tailTrace_579505
  have hstable : (prefixWord ++ tailWord_579505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579505).length < 2 ^ (prefixWord ++ tailWord_579505).sum := by decide
  have hdescent : baseEnd_579505 < baseStart_579505 := by decide
  rcases family_descends (prefixWord ++ tailWord_579505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579569 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 1, 4]
def baseStart_579569 : Nat := 118140960795 + 579569 * 2 ^ 59
def prefixEnd_579569 : Nat := 4983230072969 + 3 ^ 40 * 579569 * 2
def baseEnd_579569 : Nat := 99199156481916055774039

theorem tailTrace_579569 : CollatzResearch.WordTrace tailWord_579569 prefixEnd_579569 99199156481916055774039 := by
  unfold tailWord_579569
  simp only [CollatzResearch.WordTrace]
  refine ⟨21138618037327970349909761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14092412024885313566606507 21138618037327970349909761)
  ·
    refine ⟨15853963527995977762432321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21138618037327970349909761 15853963527995977762432321)
    ·
      refine ⟨11890472645996983321824241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15853963527995977762432321 11890472645996983321824241)
      ·
        refine ⟨8917854484497737491368181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11890472645996983321824241 8917854484497737491368181)
        ·
          refine ⟨836048857921662889815767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8917854484497737491368181 836048857921662889815767)
          ·
            refine ⟨1254073286882494334723651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836048857921662889815767 1254073286882494334723651)
            ·
              refine ⟨1881109930323741502085477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254073286882494334723651 1881109930323741502085477)
              ·
                refine ⟨352708111935701531641027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1881109930323741502085477 352708111935701531641027)
                ·
                  refine ⟨529062167903552297461541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352708111935701531641027 529062167903552297461541)
                  ·
                    refine ⟨99199156481916055774039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 529062167903552297461541 99199156481916055774039)
                    ·
                      rfl

theorem cell23_579569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_579569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579569 prefixEnd_579569 := by exact prefixLift 579569
  have htrace : WordTrace (prefixWord ++ tailWord_579569) baseStart_579569 baseEnd_579569 := by
    simpa [prefixWord, tailWord_579569, baseEnd_579569] using wordTrace_append hprefix tailTrace_579569
  have hstable : (prefixWord ++ tailWord_579569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579569).length < 2 ^ (prefixWord ++ tailWord_579569).sum := by decide
  have hdescent : baseEnd_579569 < baseStart_579569 := by decide
  rcases family_descends (prefixWord ++ tailWord_579569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579575 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_579575 : Nat := 118140960795 + 579575 * 2 ^ 59
def prefixEnd_579575 : Nat := 4983230072969 + 3 ^ 40 * 579575 * 2
def baseEnd_579575 : Nat := 297600550329675143847089

theorem tailTrace_579575 : CollatzResearch.WordTrace tailWord_579575 prefixEnd_579575 297600550329675143847089 := by
  unfold tailWord_579575
  simp only [CollatzResearch.WordTrace]
  refine ⟨21138836875306233374628179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14092557916870822249752119 21138836875306233374628179)
  ·
    refine ⟨31708255312959350061942269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21138836875306233374628179 31708255312959350061942269)
    ·
      refine ⟨11890595742359756273228351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31708255312959350061942269 11890595742359756273228351)
      ·
        refine ⟨17835893613539634409842527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11890595742359756273228351 17835893613539634409842527)
        ·
          refine ⟨26753840420309451614763791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17835893613539634409842527 26753840420309451614763791)
          ·
            refine ⟨40130760630464177422145687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26753840420309451614763791 40130760630464177422145687)
            ·
              refine ⟨60196140945696266133218531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40130760630464177422145687 60196140945696266133218531)
              ·
                refine ⟨90294211418544399199827797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60196140945696266133218531 90294211418544399199827797)
                ·
                  refine ⟨529067645030533589061491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 90294211418544399199827797 529067645030533589061491)
                  ·
                    refine ⟨793601467545800383592237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 529067645030533589061491 793601467545800383592237)
                    ·
                      refine ⟨297600550329675143847089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793601467545800383592237 297600550329675143847089)
                      ·
                        rfl

theorem cell23_579575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_579575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579575 prefixEnd_579575 := by exact prefixLift 579575
  have htrace : WordTrace (prefixWord ++ tailWord_579575) baseStart_579575 baseEnd_579575 := by
    simpa [prefixWord, tailWord_579575, baseEnd_579575] using wordTrace_append hprefix tailTrace_579575
  have hstable : (prefixWord ++ tailWord_579575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579575).length < 2 ^ (prefixWord ++ tailWord_579575).sum := by decide
  have hdescent : baseEnd_579575 < baseStart_579575 := by decide
  rcases family_descends (prefixWord ++ tailWord_579575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579582 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 6]
def baseStart_579582 : Nat := 118140960795 + 579582 * 2 ^ 59
def prefixEnd_579582 : Nat := 4983230072969 + 3 ^ 40 * 579582 * 2
def baseEnd_579582 : Nat := 33067127188250735162173

theorem tailTrace_579582 : CollatzResearch.WordTrace tailWord_579582 prefixEnd_579582 33067127188250735162173 := by
  unfold tailWord_579582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2642386523285109196266625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14092728124187249046755333 2642386523285109196266625)
  ·
    refine ⟨1981789892463831897199969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2642386523285109196266625 1981789892463831897199969)
    ·
      refine ⟨1486342419347873922899977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1981789892463831897199969 1486342419347873922899977)
      ·
        refine ⟨1114756814510905442174983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1486342419347873922899977 1114756814510905442174983)
        ·
          refine ⟨1672135221766358163262475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1114756814510905442174983 1672135221766358163262475)
          ·
            refine ⟨2508202832649537244893713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672135221766358163262475 2508202832649537244893713)
            ·
              refine ⟨1881152124487152933670285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508202832649537244893713 1881152124487152933670285)
              ·
                refine ⟨705432046682682350126357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881152124487152933670285 705432046682682350126357)
                ·
                  refine ⟨33067127188250735162173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 705432046682682350126357 33067127188250735162173)
                  ·
                    rfl

theorem cell23_579582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_579582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579582 prefixEnd_579582 := by exact prefixLift 579582
  have htrace : WordTrace (prefixWord ++ tailWord_579582) baseStart_579582 baseEnd_579582 := by
    simpa [prefixWord, tailWord_579582, baseEnd_579582] using wordTrace_append hprefix tailTrace_579582
  have hstable : (prefixWord ++ tailWord_579582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579582).length < 2 ^ (prefixWord ++ tailWord_579582).sum := by decide
  have hdescent : baseEnd_579582 < baseStart_579582 := by decide
  rcases family_descends (prefixWord ++ tailWord_579582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579590 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_579590 : Nat := 118140960795 + 579590 * 2 ^ 59
def prefixEnd_579590 : Nat := 4983230072969 + 3 ^ 40 * 579590 * 2
def baseEnd_579590 : Nat := 99202750846497528386507

theorem tailTrace_579590 : CollatzResearch.WordTrace tailWord_579590 prefixEnd_579590 99202750846497528386507 := by
  unfold tailWord_579590
  simp only [CollatzResearch.WordTrace]
  refine ⟨660605749070371591763257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14092922646834593957616149 660605749070371591763257)
  ·
    refine ⟨495454311802778693822443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 660605749070371591763257 495454311802778693822443)
    ·
      refine ⟨743181467704168040733665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 495454311802778693822443 743181467704168040733665)
      ·
        refine ⟨557386100778126030550249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 743181467704168040733665 557386100778126030550249)
        ·
          refine ⟨418039575583594522912687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557386100778126030550249 418039575583594522912687)
          ·
            refine ⟨627059363375391784369031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418039575583594522912687 627059363375391784369031)
            ·
              refine ⟨940589045063087676553547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627059363375391784369031 940589045063087676553547)
              ·
                refine ⟨1410883567594631514830321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 940589045063087676553547 1410883567594631514830321)
                ·
                  refine ⟨1058162675695973636122741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1410883567594631514830321 1058162675695973636122741)
                  ·
                    refine ⟨99202750846497528386507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1058162675695973636122741 99202750846497528386507)
                    ·
                      rfl

theorem cell23_579590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_579590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579590 prefixEnd_579590 := by exact prefixLift 579590
  have htrace : WordTrace (prefixWord ++ tailWord_579590) baseStart_579590 baseEnd_579590 := by
    simpa [prefixWord, tailWord_579590, baseEnd_579590] using wordTrace_append hprefix tailTrace_579590
  have hstable : (prefixWord ++ tailWord_579590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579590).length < 2 ^ (prefixWord ++ tailWord_579590).sum := by decide
  have hdescent : baseEnd_579590 < baseStart_579590 := by decide
  rcases family_descends (prefixWord ++ tailWord_579590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579592 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_579592 : Nat := 118140960795 + 579592 * 2 ^ 59
def prefixEnd_579592 : Nat := 4983230072969 + 3 ^ 40 * 579592 * 2
def baseEnd_579592 : Nat := 297609279500801577334511

theorem tailTrace_579592 : CollatzResearch.WordTrace tailWord_579592 prefixEnd_579592 297609279500801577334511 := by
  unfold tailWord_579592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10569728458122322638998515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14092971277496430185331353 10569728458122322638998515)
  ·
    refine ⟨15854592687183483958497773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10569728458122322638998515 15854592687183483958497773)
    ·
      refine ⟨5945472257693806484436665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15854592687183483958497773 5945472257693806484436665)
      ·
        refine ⟨4459104193270354863327499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5945472257693806484436665 4459104193270354863327499)
        ·
          refine ⟨6688656289905532294991249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4459104193270354863327499 6688656289905532294991249)
          ·
            refine ⟨5016492217429149221243437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688656289905532294991249 5016492217429149221243437)
            ·
              refine ⟨1881184581535930957966289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5016492217429149221243437 1881184581535930957966289)
              ·
                refine ⟨1410888436151948218474717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1881184581535930957966289 1410888436151948218474717)
                ·
                  refine ⟨529083163556980581928019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1410888436151948218474717 529083163556980581928019)
                  ·
                    refine ⟨793624745335470872892029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 529083163556980581928019 793624745335470872892029)
                    ·
                      refine ⟨297609279500801577334511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793624745335470872892029 297609279500801577334511)
                      ·
                        rfl

theorem cell23_579592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_579592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579592 prefixEnd_579592 := by exact prefixLift 579592
  have htrace : WordTrace (prefixWord ++ tailWord_579592) baseStart_579592 baseEnd_579592 := by
    simpa [prefixWord, tailWord_579592, baseEnd_579592] using wordTrace_append hprefix tailTrace_579592
  have hstable : (prefixWord ++ tailWord_579592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579592).length < 2 ^ (prefixWord ++ tailWord_579592).sum := by decide
  have hdescent : baseEnd_579592 < baseStart_579592 := by decide
  rcases family_descends (prefixWord ++ tailWord_579592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579595 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 1, 5]
def baseStart_579595 : Nat := 118140960795 + 579595 * 2 ^ 59
def prefixEnd_579595 : Nat := 4983230072969 + 3 ^ 40 * 579595 * 2
def baseEnd_579595 : Nat := 99203606647588355198999

theorem tailTrace_579595 : CollatzResearch.WordTrace tailWord_579595 prefixEnd_579595 99203606647588355198999 := by
  unfold tailWord_579595
  simp only [CollatzResearch.WordTrace]
  refine ⟨21139566335233776790356239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14093044223489184526904159 21139566335233776790356239)
  ·
    refine ⟨31709349502850665185534359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21139566335233776790356239 31709349502850665185534359)
    ·
      refine ⟨47564024254275997778301539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31709349502850665185534359 47564024254275997778301539)
      ·
        refine ⟨71346036381413996667452309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47564024254275997778301539 71346036381413996667452309)
        ·
          refine ⟨3344345455378781093786827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 71346036381413996667452309 3344345455378781093786827)
          ·
            refine ⟨5016518183068171640680241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344345455378781093786827 5016518183068171640680241)
            ·
              refine ⟨3762388637301128730510181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5016518183068171640680241 3762388637301128730510181)
              ·
                refine ⟨705447869493961636970659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3762388637301128730510181 705447869493961636970659)
                ·
                  refine ⟨1058171804240942455455989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705447869493961636970659 1058171804240942455455989)
                  ·
                    refine ⟨99203606647588355198999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1058171804240942455455989 99203606647588355198999)
                    ·
                      rfl

theorem cell23_579595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 5].length) (baseStart_579595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579595 prefixEnd_579595 := by exact prefixLift 579595
  have htrace : WordTrace (prefixWord ++ tailWord_579595) baseStart_579595 baseEnd_579595 := by
    simpa [prefixWord, tailWord_579595, baseEnd_579595] using wordTrace_append hprefix tailTrace_579595
  have hstable : (prefixWord ++ tailWord_579595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579595).length < 2 ^ (prefixWord ++ tailWord_579595).sum := by decide
  have hdescent : baseEnd_579595 < baseStart_579595 := by decide
  rcases family_descends (prefixWord ++ tailWord_579595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579612 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_579612 : Nat := 118140960795 + 579612 * 2 ^ 59
def prefixEnd_579612 : Nat := 4983230072969 + 3 ^ 40 * 579612 * 2
def baseEnd_579612 : Nat := 99206516371297166361473

theorem tailTrace_579612 : CollatzResearch.WordTrace tailWord_579612 prefixEnd_579612 99206516371297166361473 := by
  unfold tailWord_579612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10570093188086094346862545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14093457584114792462483393 10570093188086094346862545)
  ·
    refine ⟨7927569891064570760146909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10570093188086094346862545 7927569891064570760146909)
    ·
      refine ⟨2972838709149214035055091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7927569891064570760146909 2972838709149214035055091)
      ·
        refine ⟨4459258063723821052582637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972838709149214035055091 4459258063723821052582637)
        ·
          refine ⟨1672221773896432894718489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4459258063723821052582637 1672221773896432894718489)
          ·
            refine ⟨1254166330422324671038867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672221773896432894718489 1254166330422324671038867)
            ·
              refine ⟨1881249495633487006558301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254166330422324671038867 1881249495633487006558301)
              ·
                refine ⟨705468560862557627459363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1881249495633487006558301 705468560862557627459363)
                ·
                  refine ⟨1058202841293836441189045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705468560862557627459363 1058202841293836441189045)
                  ·
                    refine ⟨99206516371297166361473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1058202841293836441189045 99206516371297166361473)
                    ·
                      rfl

theorem cell23_579612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_579612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579612 prefixEnd_579612 := by exact prefixLift 579612
  have htrace : WordTrace (prefixWord ++ tailWord_579612) baseStart_579612 baseEnd_579612 := by
    simpa [prefixWord, tailWord_579612, baseEnd_579612] using wordTrace_append hprefix tailTrace_579612
  have hstable : (prefixWord ++ tailWord_579612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579612).length < 2 ^ (prefixWord ++ tailWord_579612).sum := by decide
  have hdescent : baseEnd_579612 < baseStart_579612 := by decide
  rcases family_descends (prefixWord ++ tailWord_579612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579626 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_579626 : Nat := 118140960795 + 579626 * 2 ^ 59
def prefixEnd_579626 : Nat := 4983230072969 + 3 ^ 40 * 579626 * 2
def baseEnd_579626 : Nat := 297626737843054444309355

theorem tailTrace_579626 : CollatzResearch.WordTrace tailWord_579626 prefixEnd_579626 297626737843054444309355 := by
  unfold tailWord_579626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5285174249530367271183683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14093797998747646056489821 5285174249530367271183683)
  ·
    refine ⟨7927761374295550906775525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5285174249530367271183683 7927761374295550906775525)
    ·
      refine ⟨1486455257680415795020411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7927761374295550906775525 1486455257680415795020411)
      ·
        refine ⟨2229682886520623692530617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486455257680415795020411 2229682886520623692530617)
        ·
          refine ⟨1672262164890467769397963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229682886520623692530617 1672262164890467769397963)
          ·
            refine ⟨2508393247335701654096945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1672262164890467769397963 2508393247335701654096945)
            ·
              refine ⟨1881294935501776240572709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2508393247335701654096945 1881294935501776240572709)
              ·
                refine ⟨352742800406583045107383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1881294935501776240572709 352742800406583045107383)
                ·
                  refine ⟨529114200609874567661075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 352742800406583045107383 529114200609874567661075)
                  ·
                    refine ⟨793671300914811851491613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 529114200609874567661075 793671300914811851491613)
                    ·
                      refine ⟨297626737843054444309355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793671300914811851491613 297626737843054444309355)
                      ·
                        rfl

theorem cell23_579626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_579626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579626 prefixEnd_579626 := by exact prefixLift 579626
  have htrace : WordTrace (prefixWord ++ tailWord_579626) baseStart_579626 baseEnd_579626 := by
    simpa [prefixWord, tailWord_579626, baseEnd_579626] using wordTrace_append hprefix tailTrace_579626
  have hstable : (prefixWord ++ tailWord_579626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579626).length < 2 ^ (prefixWord ++ tailWord_579626).sum := by decide
  have hdescent : baseEnd_579626 < baseStart_579626 := by decide
  rcases family_descends (prefixWord ++ tailWord_579626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579635 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3]
def baseStart_579635 : Nat := 118140960795 + 579635 * 2 ^ 59
def prefixEnd_579635 : Nat := 4983230072969 + 3 ^ 40 * 579635 * 2
def baseEnd_579635 : Nat := 297631359168944909096813

theorem tailTrace_579635 : CollatzResearch.WordTrace tailWord_579635 prefixEnd_579635 297631359168944909096813 := by
  unfold tailWord_579635
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141025255088863621812359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094016836725909081208239 21141025255088863621812359)
  ·
    refine ⟨31711537882633295432718539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21141025255088863621812359 31711537882633295432718539)
    ·
      refine ⟨47567306823949943149077809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31711537882633295432718539 47567306823949943149077809)
      ·
        refine ⟨35675480117962457361808357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47567306823949943149077809 35675480117962457361808357)
        ·
          refine ⟨6689152522117960755339067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35675480117962457361808357 6689152522117960755339067)
          ·
            refine ⟨10033728783176941133008601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689152522117960755339067 10033728783176941133008601)
            ·
              refine ⟨7525296587382705849756451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10033728783176941133008601 7525296587382705849756451)
              ·
                refine ⟨11287944881074058774634677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7525296587382705849756451 11287944881074058774634677)
                ·
                  refine ⟨1058244832600693010122001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11287944881074058774634677 1058244832600693010122001)
                  ·
                    refine ⟨793683624450519757591501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058244832600693010122001 793683624450519757591501)
                    ·
                      refine ⟨297631359168944909096813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793683624450519757591501 297631359168944909096813)
                      ·
                        rfl

theorem cell23_579635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_579635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579635 prefixEnd_579635 := by exact prefixLift 579635
  have htrace : WordTrace (prefixWord ++ tailWord_579635) baseStart_579635 baseEnd_579635 := by
    simpa [prefixWord, tailWord_579635, baseEnd_579635] using wordTrace_append hprefix tailTrace_579635
  have hstable : (prefixWord ++ tailWord_579635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579635).length < 2 ^ (prefixWord ++ tailWord_579635).sum := by decide
  have hdescent : baseEnd_579635 < baseStart_579635 := by decide
  rcases family_descends (prefixWord ++ tailWord_579635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579645 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_579645 : Nat := 118140960795 + 579645 * 2 ^ 59
def prefixEnd_579645 : Nat := 4983230072969 + 3 ^ 40 * 579645 * 2
def baseEnd_579645 : Nat := 297636493975489869971767

theorem tailTrace_579645 : CollatzResearch.WordTrace tailWord_579645 prefixEnd_579645 297636493975489869971767 := by
  unfold tailWord_579645
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141389985052635329676389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094259990035090219784259 21141389985052635329676389)
  ·
    refine ⟨3964010622197369124314323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21141389985052635329676389 3964010622197369124314323)
    ·
      refine ⟨5946015933296053686471485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964010622197369124314323 5946015933296053686471485)
      ·
        refine ⟨2229755974986020132426807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5946015933296053686471485 2229755974986020132426807)
        ·
          refine ⟨3344633962479030198640211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2229755974986020132426807 3344633962479030198640211)
          ·
            refine ⟨5016950943718545297960317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3344633962479030198640211 5016950943718545297960317)
            ·
              refine ⟨1881356603894454486735119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5016950943718545297960317 1881356603894454486735119)
              ·
                refine ⟨2822034905841681730102679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881356603894454486735119 2822034905841681730102679)
                ·
                  refine ⟨4233052358762522595154019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822034905841681730102679 4233052358762522595154019)
                  ·
                    refine ⟨6349578538143783892731029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4233052358762522595154019 6349578538143783892731029)
                    ·
                      refine ⟨297636493975489869971767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6349578538143783892731029 297636493975489869971767)
                      ·
                        rfl

theorem cell23_579645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_579645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579645 prefixEnd_579645 := by exact prefixLift 579645
  have htrace : WordTrace (prefixWord ++ tailWord_579645) baseStart_579645 baseEnd_579645 := by
    simpa [prefixWord, tailWord_579645, baseEnd_579645] using wordTrace_append hprefix tailTrace_579645
  have hstable : (prefixWord ++ tailWord_579645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579645).length < 2 ^ (prefixWord ++ tailWord_579645).sum := by decide
  have hdescent : baseEnd_579645 < baseStart_579645 := by decide
  rcases family_descends (prefixWord ++ tailWord_579645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579649 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_579649 : Nat := 118140960795 + 579649 * 2 ^ 59
def prefixEnd_579649 : Nat := 4983230072969 + 3 ^ 40 * 579649 * 2
def baseEnd_579649 : Nat := 297638547898107854321749

theorem tailTrace_579649 : CollatzResearch.WordTrace tailWord_579649 prefixEnd_579649 297638547898107854321749 := by
  unfold tailWord_579649
  simp only [CollatzResearch.WordTrace]
  refine ⟨21141535877038144012822001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094357251358762675214667 21141535877038144012822001)
  ·
    refine ⟨15856151907778608009616501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21141535877038144012822001 15856151907778608009616501)
    ·
      refine ⟨1486514241354244500901547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15856151907778608009616501 1486514241354244500901547)
      ·
        refine ⟨2229771362031366751352321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1486514241354244500901547 2229771362031366751352321)
        ·
          refine ⟨1672328521523525063514241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2229771362031366751352321 1672328521523525063514241)
          ·
            refine ⟨1254246391142643797635681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1672328521523525063514241 1254246391142643797635681)
            ·
              refine ⟨940684793356982848226761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1254246391142643797635681 940684793356982848226761)
              ·
                refine ⟨705513595017737136170071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 940684793356982848226761 705513595017737136170071)
                ·
                  refine ⟨1058270392526605704255107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705513595017737136170071 1058270392526605704255107)
                  ·
                    refine ⟨1587405588789908556382661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1058270392526605704255107 1587405588789908556382661)
                    ·
                      refine ⟨297638547898107854321749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1587405588789908556382661 297638547898107854321749)
                      ·
                        rfl

theorem cell23_579649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_579649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579649 prefixEnd_579649 := by exact prefixLift 579649
  have htrace : WordTrace (prefixWord ++ tailWord_579649) baseStart_579649 baseEnd_579649 := by
    simpa [prefixWord, tailWord_579649, baseEnd_579649] using wordTrace_append hprefix tailTrace_579649
  have hstable : (prefixWord ++ tailWord_579649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579649).length < 2 ^ (prefixWord ++ tailWord_579649).sum := by decide
  have hdescent : baseEnd_579649 < baseStart_579649 := by decide
  rcases family_descends (prefixWord ++ tailWord_579649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579665 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_579665 : Nat := 118140960795 + 579665 * 2 ^ 59
def prefixEnd_579665 : Nat := 4983230072969 + 3 ^ 40 * 579665 * 2
def baseEnd_579665 : Nat := 297646763588579791721675

theorem tailTrace_579665 : CollatzResearch.WordTrace tailWord_579665 prefixEnd_579665 297646763588579791721675 := by
  unfold tailWord_579665
  simp only [CollatzResearch.WordTrace]
  refine ⟨21142119444980178745404449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14094746296653452496936299 21142119444980178745404449)
  ·
    refine ⟨15856589583735134059053337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21142119444980178745404449 15856589583735134059053337)
    ·
      refine ⟨11892442187801350544290003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15856589583735134059053337 11892442187801350544290003)
      ·
        refine ⟨17838663281702025816435005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11892442187801350544290003 17838663281702025816435005)
        ·
          refine ⟨6689498730638259681163127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17838663281702025816435005 6689498730638259681163127)
          ·
            refine ⟨10034248095957389521744691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6689498730638259681163127 10034248095957389521744691)
            ·
              refine ⟨15051372143936084282617037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10034248095957389521744691 15051372143936084282617037)
              ·
                refine ⟨5644264553976031605981389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15051372143936084282617037 5644264553976031605981389)
                ·
                  refine ⟨2116599207741011852243021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5644264553976031605981389 2116599207741011852243021)
                  ·
                    refine ⟨793724702902879444591133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2116599207741011852243021 793724702902879444591133)
                    ·
                      refine ⟨297646763588579791721675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793724702902879444591133 297646763588579791721675)
                      ·
                        rfl

theorem cell23_579665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_579665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579665 prefixEnd_579665 := by exact prefixLift 579665
  have htrace : WordTrace (prefixWord ++ tailWord_579665) baseStart_579665 baseEnd_579665 := by
    simpa [prefixWord, tailWord_579665, baseEnd_579665] using wordTrace_append hprefix tailTrace_579665
  have hstable : (prefixWord ++ tailWord_579665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579665).length < 2 ^ (prefixWord ++ tailWord_579665).sum := by decide
  have hdescent : baseEnd_579665 < baseStart_579665 := by decide
  rcases family_descends (prefixWord ++ tailWord_579665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579709 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 3, 3, 2]
def baseStart_579709 : Nat := 118140960795 + 579709 * 2 ^ 59
def prefixEnd_579709 : Nat := 4983230072969 + 3 ^ 40 * 579709 * 2
def baseEnd_579709 : Nat := 297669356737377619571473

theorem tailTrace_579709 : CollatzResearch.WordTrace tailWord_579709 prefixEnd_579709 297669356737377619571473 := by
  unfold tailWord_579709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21143724256820774260006181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14095816171213849506670787 21143724256820774260006181)
  ·
    refine ⟨3964448298153895173751159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21143724256820774260006181 3964448298153895173751159)
    ·
      refine ⟨5946672447230842760626739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3964448298153895173751159 5946672447230842760626739)
      ·
        refine ⟨8920008670846264140940109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5946672447230842760626739 8920008670846264140940109)
        ·
          refine ⟨3345003251567349052852541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8920008670846264140940109 3345003251567349052852541)
          ·
            refine ⟨1254376219337755894819703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3345003251567349052852541 1254376219337755894819703)
            ·
              refine ⟨1881564329006633842229555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254376219337755894819703 1881564329006633842229555)
              ·
                refine ⟨2822346493509950763344333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1881564329006633842229555 2822346493509950763344333)
                ·
                  refine ⟨1058379935066231536254125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2822346493509950763344333 1058379935066231536254125)
                  ·
                    refine ⟨396892475649836826095297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058379935066231536254125 396892475649836826095297)
                    ·
                      refine ⟨297669356737377619571473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396892475649836826095297 297669356737377619571473)
                      ·
                        rfl

theorem cell23_579709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3, 2].length) (baseStart_579709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579709 prefixEnd_579709 := by exact prefixLift 579709
  have htrace : WordTrace (prefixWord ++ tailWord_579709) baseStart_579709 baseEnd_579709 := by
    simpa [prefixWord, tailWord_579709, baseEnd_579709] using wordTrace_append hprefix tailTrace_579709
  have hstable : (prefixWord ++ tailWord_579709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579709).length < 2 ^ (prefixWord ++ tailWord_579709).sum := by decide
  have hdescent : baseEnd_579709 < baseStart_579709 := by decide
  rcases family_descends (prefixWord ++ tailWord_579709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579777 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_579777 : Nat := 118140960795 + 579777 * 2 ^ 59
def prefixEnd_579777 : Nat := 4983230072969 + 3 ^ 40 * 579777 * 2
def baseEnd_579777 : Nat := 297704273421883353521161

theorem tailTrace_579777 : CollatzResearch.WordTrace tailWord_579777 prefixEnd_579777 297704273421883353521161 := by
  unfold tailWord_579777
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146204420574421873481585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097469613716281248987723 21146204420574421873481585)
  ·
    refine ⟨15859653315430816405111189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21146204420574421873481585 15859653315430816405111189)
    ·
      refine ⟨743421249160819518989587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15859653315430816405111189 743421249160819518989587)
      ·
        refine ⟨1115131873741229278484381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743421249160819518989587 1115131873741229278484381)
        ·
          refine ⟨418174452652960979431643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1115131873741229278484381 418174452652960979431643)
          ·
            refine ⟨627261678979441469147465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418174452652960979431643 627261678979441469147465)
            ·
              refine ⟨470446259234581101860599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 627261678979441469147465 470446259234581101860599)
              ·
                refine ⟨705669388851871652790899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470446259234581101860599 705669388851871652790899)
                ·
                  refine ⟨1058504083277807479186349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 705669388851871652790899 1058504083277807479186349)
                  ·
                    refine ⟨396939031229177804694881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1058504083277807479186349 396939031229177804694881)
                    ·
                      refine ⟨297704273421883353521161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 396939031229177804694881 297704273421883353521161)
                      ·
                        rfl

theorem cell23_579777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_579777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579777 prefixEnd_579777 := by exact prefixLift 579777
  have htrace : WordTrace (prefixWord ++ tailWord_579777) baseStart_579777 baseEnd_579777 := by
    simpa [prefixWord, tailWord_579777, baseEnd_579777] using wordTrace_append hprefix tailTrace_579777
  have hstable : (prefixWord ++ tailWord_579777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579777).length < 2 ^ (prefixWord ++ tailWord_579777).sum := by decide
  have hdescent : baseEnd_579777 < baseStart_579777 := by decide
  rcases family_descends (prefixWord ++ tailWord_579777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579785 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_579785 : Nat := 118140960795 + 579785 * 2 ^ 59
def prefixEnd_579785 : Nat := 4983230072969 + 3 ^ 40 * 579785 * 2
def baseEnd_579785 : Nat := 297708381267119322221123

theorem tailTrace_579785 : CollatzResearch.WordTrace tailWord_579785 prefixEnd_579785 297708381267119322221123 := by
  unfold tailWord_579785
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146496204545439239772809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097664136363626159848539 21146496204545439239772809)
  ·
    refine ⟨15859872153409079429829607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21146496204545439239772809 15859872153409079429829607)
    ·
      refine ⟨23789808230113619144744411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15859872153409079429829607 23789808230113619144744411)
      ·
        refine ⟨35684712345170428717116617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23789808230113619144744411 35684712345170428717116617)
        ·
          refine ⟨26763534258877821537837463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35684712345170428717116617 26763534258877821537837463)
          ·
            refine ⟨40145301388316732306756195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26763534258877821537837463 40145301388316732306756195)
            ·
              refine ⟨60217952082475098460134293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40145301388316732306756195 60217952082475098460134293)
              ·
                refine ⟨2822716503866020240318795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60217952082475098460134293 2822716503866020240318795)
                ·
                  refine ⟨4234074755799030360478193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2822716503866020240318795 4234074755799030360478193)
                  ·
                    refine ⟨3175556066849272770358645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4234074755799030360478193 3175556066849272770358645)
                    ·
                      refine ⟨297708381267119322221123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3175556066849272770358645 297708381267119322221123)
                      ·
                        rfl

theorem cell23_579785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_579785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579785 prefixEnd_579785 := by exact prefixLift 579785
  have htrace : WordTrace (prefixWord ++ tailWord_579785) baseStart_579785 baseEnd_579785 := by
    simpa [prefixWord, tailWord_579785, baseEnd_579785] using wordTrace_append hprefix tailTrace_579785
  have hstable : (prefixWord ++ tailWord_579785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579785).length < 2 ^ (prefixWord ++ tailWord_579785).sum := by decide
  have hdescent : baseEnd_579785 < baseStart_579785 := by decide
  rcases family_descends (prefixWord ++ tailWord_579785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579795 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_579795 : Nat := 118140960795 + 579795 * 2 ^ 59
def prefixEnd_579795 : Nat := 4983230072969 + 3 ^ 40 * 579795 * 2
def baseEnd_579795 : Nat := 297713516073664283096077

theorem tailTrace_579795 : CollatzResearch.WordTrace tailWord_579795 prefixEnd_579795 297713516073664283096077 := by
  unfold tailWord_579795
  simp only [CollatzResearch.WordTrace]
  refine ⟨21146860934509210947636839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14097907289672807298424559 21146860934509210947636839)
  ·
    refine ⟨31720291401763816421455259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21146860934509210947636839 31720291401763816421455259)
    ·
      refine ⟨47580437102645724632182889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31720291401763816421455259 47580437102645724632182889)
      ·
        refine ⟨35685327826984293474137167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47580437102645724632182889 35685327826984293474137167)
        ·
          refine ⟨53527991740476440211205751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35685327826984293474137167 53527991740476440211205751)
          ·
            refine ⟨80291987610714660316808627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53527991740476440211205751 80291987610714660316808627)
            ·
              refine ⟨120437981416071990475212941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80291987610714660316808627 120437981416071990475212941)
              ·
                refine ⟨45164243031026996428204853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120437981416071990475212941 45164243031026996428204853)
                ·
                  refine ⟨4234147784158780915144205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45164243031026996428204853 4234147784158780915144205)
                  ·
                    refine ⟨1587805419059542843179077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4234147784158780915144205 1587805419059542843179077)
                    ·
                      refine ⟨297713516073664283096077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1587805419059542843179077 297713516073664283096077)
                      ·
                        rfl

theorem cell23_579795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_579795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579795 prefixEnd_579795 := by exact prefixLift 579795
  have htrace : WordTrace (prefixWord ++ tailWord_579795) baseStart_579795 baseEnd_579795 := by
    simpa [prefixWord, tailWord_579795, baseEnd_579795] using wordTrace_append hprefix tailTrace_579795
  have hstable : (prefixWord ++ tailWord_579795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579795).length < 2 ^ (prefixWord ++ tailWord_579795).sum := by decide
  have hdescent : baseEnd_579795 < baseStart_579795 := by decide
  rcases family_descends (prefixWord ++ tailWord_579795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579832 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_579832 : Nat := 118140960795 + 579832 * 2 ^ 59
def prefixEnd_579832 : Nat := 4983230072969 + 3 ^ 40 * 579832 * 2
def baseEnd_579832 : Nat := 297732514857880638333407

theorem tailTrace_579832 : CollatzResearch.WordTrace tailWord_579832 prefixEnd_579832 297732514857880638333407 := by
  unfold tailWord_579832
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574105217687583133366875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14098806956916777511155833 10574105217687583133366875)
  ·
    refine ⟨15861157826531374700050313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10574105217687583133366875 15861157826531374700050313)
    ·
      refine ⟨11895868369898531025037735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15861157826531374700050313 11895868369898531025037735)
      ·
        refine ⟨17843802554847796537556603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11895868369898531025037735 17843802554847796537556603)
        ·
          refine ⟨26765703832271694806334905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17843802554847796537556603 26765703832271694806334905)
          ·
            refine ⟨20074277874203771104751179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26765703832271694806334905 20074277874203771104751179)
            ·
              refine ⟨30111416811305656657126769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20074277874203771104751179 30111416811305656657126769)
              ·
                refine ⟨22583562608479242492845077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30111416811305656657126769 22583562608479242492845077)
                ·
                  refine ⟨1058604497272464491852113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22583562608479242492845077 1058604497272464491852113)
                  ·
                    refine ⟨793953372954348368889085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058604497272464491852113 793953372954348368889085)
                    ·
                      refine ⟨297732514857880638333407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793953372954348368889085 297732514857880638333407)
                      ·
                        rfl

theorem cell23_579832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_579832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579832 prefixEnd_579832 := by exact prefixLift 579832
  have htrace : WordTrace (prefixWord ++ tailWord_579832) baseStart_579832 baseEnd_579832 := by
    simpa [prefixWord, tailWord_579832, baseEnd_579832] using wordTrace_append hprefix tailTrace_579832
  have hstable : (prefixWord ++ tailWord_579832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579832).length < 2 ^ (prefixWord ++ tailWord_579832).sum := by decide
  have hdescent : baseEnd_579832 < baseStart_579832 := by decide
  rcases family_descends (prefixWord ++ tailWord_579832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579849 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_579849 : Nat := 118140960795 + 579849 * 2 ^ 59
def prefixEnd_579849 : Nat := 4983230072969 + 3 ^ 40 * 579849 * 2
def baseEnd_579849 : Nat := 297741244029007071820829

theorem tailTrace_579849 : CollatzResearch.WordTrace tailWord_579849 prefixEnd_579849 297741244029007071820829 := by
  unfold tailWord_579849
  simp only [CollatzResearch.WordTrace]
  refine ⟨21148830476313578170102601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14099220317542385446735067 21148830476313578170102601)
  ·
    refine ⟨15861622857235183627576951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21148830476313578170102601 15861622857235183627576951)
    ·
      refine ⟨23792434285852775441365427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15861622857235183627576951 23792434285852775441365427)
      ·
        refine ⟨35688651428779163162048141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23792434285852775441365427 35688651428779163162048141)
        ·
          refine ⟨13383244285792186185768053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35688651428779163162048141 13383244285792186185768053)
          ·
            refine ⟨1254679151793017454915755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13383244285792186185768053 1254679151793017454915755)
            ·
              refine ⟨1882018727689526182373633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1254679151793017454915755 1882018727689526182373633)
              ·
                refine ⟨1411514045767144636780225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1882018727689526182373633 1411514045767144636780225)
                ·
                  refine ⟨1058635534325358477585169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411514045767144636780225 1058635534325358477585169)
                  ·
                    refine ⟨793976650744018858188877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058635534325358477585169 793976650744018858188877)
                    ·
                      refine ⟨297741244029007071820829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 793976650744018858188877 297741244029007071820829)
                      ·
                        rfl

theorem cell23_579849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_579849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579849 prefixEnd_579849 := by exact prefixLift 579849
  have htrace : WordTrace (prefixWord ++ tailWord_579849) baseStart_579849 baseEnd_579849 := by
    simpa [prefixWord, tailWord_579849, baseEnd_579849] using wordTrace_append hprefix tailTrace_579849
  have hstable : (prefixWord ++ tailWord_579849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579849).length < 2 ^ (prefixWord ++ tailWord_579849).sum := by decide
  have hdescent : baseEnd_579849 < baseStart_579849 := by decide
  rcases family_descends (prefixWord ++ tailWord_579849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579852 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 6]
def baseStart_579852 : Nat := 118140960795 + 579852 * 2 ^ 59
def prefixEnd_579852 : Nat := 4983230072969 + 3 ^ 40 * 579852 * 2
def baseEnd_579852 : Nat := 33082531607885617787035

theorem tailTrace_579852 : CollatzResearch.WordTrace tailWord_579852 prefixEnd_579852 33082531607885617787035 := by
  unfold tailWord_579852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10574469947651354841230905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14099293263535139788307873 10574469947651354841230905)
  ·
    refine ⟨7930852460738516130923179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10574469947651354841230905 7930852460738516130923179)
    ·
      refine ⟨11896278691107774196384769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7930852460738516130923179 11896278691107774196384769)
      ·
        refine ⟨8922209018330830647288577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11896278691107774196384769 8922209018330830647288577)
        ·
          refine ⟨6691656763748122985466433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8922209018330830647288577 6691656763748122985466433)
          ·
            refine ⟨5018742572811092239099825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6691656763748122985466433 5018742572811092239099825)
            ·
              refine ⟨3764056929608319179324869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5018742572811092239099825 3764056929608319179324869)
              ·
                refine ⟨705760674301559846123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3764056929608319179324869 705760674301559846123413)
                ·
                  refine ⟨33082531607885617787035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 705760674301559846123413 33082531607885617787035)
                  ·
                    rfl

theorem cell23_579852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_579852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579852 prefixEnd_579852 := by exact prefixLift 579852
  have htrace : WordTrace (prefixWord ++ tailWord_579852) baseStart_579852 baseEnd_579852 := by
    simpa [prefixWord, tailWord_579852, baseEnd_579852] using wordTrace_append hprefix tailTrace_579852
  have hstable : (prefixWord ++ tailWord_579852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579852).length < 2 ^ (prefixWord ++ tailWord_579852).sum := by decide
  have hdescent : baseEnd_579852 < baseStart_579852 := by decide
  rcases family_descends (prefixWord ++ tailWord_579852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579855 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_579855 : Nat := 118140960795 + 579855 * 2 ^ 59
def prefixEnd_579855 : Nat := 4983230072969 + 3 ^ 40 * 579855 * 2
def baseEnd_579855 : Nat := 297744324912934048345801

theorem tailTrace_579855 : CollatzResearch.WordTrace tailWord_579855 prefixEnd_579855 297744324912934048345801 := by
  unfold tailWord_579855
  simp only [CollatzResearch.WordTrace]
  refine ⟨21149049314291841194821019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14099366209527894129880679 21149049314291841194821019)
  ·
    refine ⟨31723573971437761792231529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21149049314291841194821019 31723573971437761792231529)
    ·
      refine ⟨23792680478578321344173647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31723573971437761792231529 23792680478578321344173647)
      ·
        refine ⟨35689020717867482016260471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23792680478578321344173647 35689020717867482016260471)
        ·
          refine ⟨53533531076801223024390707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35689020717867482016260471 53533531076801223024390707)
          ·
            refine ⟨80300296615201834536586061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53533531076801223024390707 80300296615201834536586061)
            ·
              refine ⟨30112611230700687951219773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80300296615201834536586061 30112611230700687951219773)
              ·
                refine ⟨11292229211512757981707415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30112611230700687951219773 11292229211512757981707415)
                ·
                  refine ⟨16938343817269136972561123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11292229211512757981707415 16938343817269136972561123)
                  ·
                    refine ⟨25407515725903705458841685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16938343817269136972561123 25407515725903705458841685)
                    ·
                      refine ⟨297744324912934048345801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 25407515725903705458841685 297744324912934048345801)
                      ·
                        rfl

theorem cell23_579855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_579855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579855 prefixEnd_579855 := by exact prefixLift 579855
  have htrace : WordTrace (prefixWord ++ tailWord_579855) baseStart_579855 baseEnd_579855 := by
    simpa [prefixWord, tailWord_579855, baseEnd_579855] using wordTrace_append hprefix tailTrace_579855
  have hstable : (prefixWord ++ tailWord_579855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579855).length < 2 ^ (prefixWord ++ tailWord_579855).sum := by decide
  have hdescent : baseEnd_579855 < baseStart_579855 := by decide
  rcases family_descends (prefixWord ++ tailWord_579855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579934 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_579934 : Nat := 118140960795 + 579934 * 2 ^ 59
def prefixEnd_579934 : Nat := 4983230072969 + 3 ^ 40 * 579934 * 2
def baseEnd_579934 : Nat := 297784889884639239257939

theorem tailTrace_579934 : CollatzResearch.WordTrace tailWord_579934 prefixEnd_579934 297784889884639239257939 := by
  unfold tailWord_579934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2643991335125704710868357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14101287120670425124631237 2643991335125704710868357)
  ·
    refine ⟨495748375336069633287817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2643991335125704710868357 495748375336069633287817)
    ·
      refine ⟨371811281502052224965863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 495748375336069633287817 371811281502052224965863)
      ·
        refine ⟨557716922253078337448795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371811281502052224965863 557716922253078337448795)
        ·
          refine ⟨836575383379617506173193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557716922253078337448795 836575383379617506173193)
          ·
            refine ⟨627431537534713129629895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836575383379617506173193 627431537534713129629895)
            ·
              refine ⟨941147306302069694444843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627431537534713129629895 941147306302069694444843)
              ·
                refine ⟨1411720959453104541667265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941147306302069694444843 1411720959453104541667265)
                ·
                  refine ⟨1058790719589828406250449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1411720959453104541667265 1058790719589828406250449)
                  ·
                    refine ⟨794093039692371304687837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058790719589828406250449 794093039692371304687837)
                    ·
                      refine ⟨297784889884639239257939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794093039692371304687837 297784889884639239257939)
                      ·
                        rfl

theorem cell23_579934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_579934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579934 prefixEnd_579934 := by exact prefixLift 579934
  have htrace : WordTrace (prefixWord ++ tailWord_579934) baseStart_579934 baseEnd_579934 := by
    simpa [prefixWord, tailWord_579934, baseEnd_579934] using wordTrace_append hprefix tailTrace_579934
  have hstable : (prefixWord ++ tailWord_579934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579934).length < 2 ^ (prefixWord ++ tailWord_579934).sum := by decide
  have hdescent : baseEnd_579934 < baseStart_579934 := by decide
  rcases family_descends (prefixWord ++ tailWord_579934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579939 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3]
def baseStart_579939 : Nat := 118140960795 + 579939 * 2 ^ 59
def prefixEnd_579939 : Nat := 4983230072969 + 3 ^ 40 * 579939 * 2
def baseEnd_579939 : Nat := 297787457287911719695415

theorem tailTrace_579939 : CollatzResearch.WordTrace tailWord_579939 prefixEnd_579939 297787457287911719695415 := by
  unfold tailWord_579939
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152113045987523540878871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14101408697325015693919247 21152113045987523540878871)
  ·
    refine ⟨31728169568981285311318307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21152113045987523540878871 31728169568981285311318307)
    ·
      refine ⟨47592254353471927966977461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31728169568981285311318307 47592254353471927966977461)
      ·
        refine ⟨4461773845637993246904137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47592254353471927966977461 4461773845637993246904137)
        ·
          refine ⟨3346330384228494935178103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4461773845637993246904137 3346330384228494935178103)
          ·
            refine ⟨5019495576342742402767155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3346330384228494935178103 5019495576342742402767155)
            ·
              refine ⟨7529243364514113604150733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5019495576342742402767155 7529243364514113604150733)
              ·
                refine ⟨2823466261692792601556525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7529243364514113604150733 2823466261692792601556525)
                ·
                  refine ⟨1058799848134797225583697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2823466261692792601556525 1058799848134797225583697)
                  ·
                    refine ⟨794099886101097919187773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1058799848134797225583697 794099886101097919187773)
                    ·
                      refine ⟨297787457287911719695415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794099886101097919187773 297787457287911719695415)
                      ·
                        rfl

theorem cell23_579939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_579939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579939 prefixEnd_579939 := by exact prefixLift 579939
  have htrace : WordTrace (prefixWord ++ tailWord_579939) baseStart_579939 baseEnd_579939 := by
    simpa [prefixWord, tailWord_579939, baseEnd_579939] using wordTrace_append hprefix tailTrace_579939
  have hstable : (prefixWord ++ tailWord_579939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579939).length < 2 ^ (prefixWord ++ tailWord_579939).sum := by decide
  have hdescent : baseEnd_579939 < baseStart_579939 := by decide
  rcases family_descends (prefixWord ++ tailWord_579939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_579949 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_579949 : Nat := 118140960795 + 579949 * 2 ^ 59
def prefixEnd_579949 : Nat := 4983230072969 + 3 ^ 40 * 579949 * 2
def baseEnd_579949 : Nat := 297792592094456680570369

theorem tailTrace_579949 : CollatzResearch.WordTrace tailWord_579949 prefixEnd_579949 297792592094456680570369 := by
  unfold tailWord_579949
  simp only [CollatzResearch.WordTrace]
  refine ⟨21152477775951295248742901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14101651850634196832495267 21152477775951295248742901)
  ·
    refine ⟨1983044791495433929569647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21152477775951295248742901 1983044791495433929569647)
    ·
      refine ⟨2974567187243150894354471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983044791495433929569647 2974567187243150894354471)
      ·
        refine ⟨4461850780864726341531707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974567187243150894354471 4461850780864726341531707)
        ·
          refine ⟨6692776171297089512297561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4461850780864726341531707 6692776171297089512297561)
          ·
            refine ⟨5019582128472817134223171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6692776171297089512297561 5019582128472817134223171)
            ·
              refine ⟨7529373192709225701334757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5019582128472817134223171 7529373192709225701334757)
              ·
                refine ⟨1411757473632979819000267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7529373192709225701334757 1411757473632979819000267)
                ·
                  refine ⟨2117636210449469728500401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1411757473632979819000267 2117636210449469728500401)
                  ·
                    refine ⟨1588227157837102296375301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2117636210449469728500401 1588227157837102296375301)
                    ·
                      refine ⟨297792592094456680570369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1588227157837102296375301 297792592094456680570369)
                      ·
                        rfl

theorem cell23_579949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_579949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_579949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_579949 prefixEnd_579949 := by exact prefixLift 579949
  have htrace : WordTrace (prefixWord ++ tailWord_579949) baseStart_579949 baseEnd_579949 := by
    simpa [prefixWord, tailWord_579949, baseEnd_579949] using wordTrace_append hprefix tailTrace_579949
  have hstable : (prefixWord ++ tailWord_579949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_579949).length < 2 ^ (prefixWord ++ tailWord_579949).sum := by decide
  have hdescent : baseEnd_579949 < baseStart_579949 := by decide
  rcases family_descends (prefixWord ++ tailWord_579949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580010 : List Nat := [3, 1, 6, 1, 2, 1, 9]
def baseStart_580010 : Nat := 118140960795 + 580010 * 2 ^ 59
def prefixEnd_580010 : Nat := 4983230072969 + 3 ^ 40 * 580010 * 2
def baseEnd_580010 : Nat := 3676838449560258542069

theorem tailTrace_580010 : CollatzResearch.WordTrace tailWord_580010 prefixEnd_580010 3676838449560258542069 := by
  unfold tailWord_580010
  simp only [CollatzResearch.WordTrace]
  refine ⟨5288675657182575666678371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14103135085820201777808989 5288675657182575666678371)
  ·
    refine ⟨7933013485773863500017557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5288675657182575666678371 7933013485773863500017557)
    ·
      refine ⟨371860007145649851563323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7933013485773863500017557 371860007145649851563323)
      ·
        refine ⟨557790010718474777344985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371860007145649851563323 557790010718474777344985)
        ·
          refine ⟨418342508038856083008739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557790010718474777344985 418342508038856083008739)
          ·
            refine ⟨627513762058284124513109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418342508038856083008739 627513762058284124513109)
            ·
              refine ⟨3676838449560258542069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 627513762058284124513109 3676838449560258542069)
              ·
                rfl

theorem cell23_580010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 9].length) (baseStart_580010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580010 prefixEnd_580010 := by exact prefixLift 580010
  have htrace : WordTrace (prefixWord ++ tailWord_580010) baseStart_580010 baseEnd_580010 := by
    simpa [prefixWord, tailWord_580010, baseEnd_580010] using wordTrace_append hprefix tailTrace_580010
  have hstable : (prefixWord ++ tailWord_580010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580010).length < 2 ^ (prefixWord ++ tailWord_580010).sum := by decide
  have hdescent : baseEnd_580010 < baseStart_580010 := by decide
  rcases family_descends (prefixWord ++ tailWord_580010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580077 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_580077 : Nat := 118140960795 + 580077 * 2 ^ 59
def prefixEnd_580077 : Nat := 4983230072969 + 3 ^ 40 * 580077 * 2
def baseEnd_580077 : Nat := 297858317618232179769781

theorem tailTrace_580077 : CollatzResearch.WordTrace tailWord_580077 prefixEnd_580077 297858317618232179769781 := by
  unfold tailWord_580077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21157146319487573109402485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14104764212991715406268323 21157146319487573109402485)
  ·
    refine ⟨1983482467451959979006483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21157146319487573109402485 1983482467451959979006483)
    ·
      refine ⟨2975223701177939968509725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983482467451959979006483 2975223701177939968509725)
      ·
        refine ⟨1115708887941727488191147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2975223701177939968509725 1115708887941727488191147)
        ·
          refine ⟨1673563331912591232286721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115708887941727488191147 1673563331912591232286721)
          ·
            refine ⟨1255172498934443424215041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673563331912591232286721 1255172498934443424215041)
            ·
              refine ⟨941379374200832568161281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1255172498934443424215041 941379374200832568161281)
              ·
                refine ⟨706034530650624426120961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941379374200832568161281 706034530650624426120961)
                ·
                  refine ⟨529525897987968319590721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706034530650624426120961 529525897987968319590721)
                  ·
                    refine ⟨397144423490976239693041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 529525897987968319590721 397144423490976239693041)
                    ·
                      refine ⟨297858317618232179769781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397144423490976239693041 297858317618232179769781)
                      ·
                        rfl

theorem cell23_580077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_580077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580077 prefixEnd_580077 := by exact prefixLift 580077
  have htrace : WordTrace (prefixWord ++ tailWord_580077) baseStart_580077 baseEnd_580077 := by
    simpa [prefixWord, tailWord_580077, baseEnd_580077] using wordTrace_append hprefix tailTrace_580077
  have hstable : (prefixWord ++ tailWord_580077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580077).length < 2 ^ (prefixWord ++ tailWord_580077).sum := by decide
  have hdescent : baseEnd_580077 < baseStart_580077 := by decide
  rcases family_descends (prefixWord ++ tailWord_580077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580089 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_580089 : Nat := 118140960795 + 580089 * 2 ^ 59
def prefixEnd_580089 : Nat := 4983230072969 + 3 ^ 40 * 580089 * 2
def baseEnd_580089 : Nat := 297864479386086132819725

theorem tailTrace_580089 : CollatzResearch.WordTrace tailWord_580089 prefixEnd_580089 297864479386086132819725 := by
  unfold tailWord_580089
  simp only [CollatzResearch.WordTrace]
  refine ⟨21157583995444099158839321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14105055996962732772559547 21157583995444099158839321)
  ·
    refine ⟨15868187996583074369129491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21157583995444099158839321 15868187996583074369129491)
    ·
      refine ⟨23802281994874611553694237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15868187996583074369129491 23802281994874611553694237)
      ·
        refine ⟨8925855748077979332635339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23802281994874611553694237 8925855748077979332635339)
        ·
          refine ⟨13388783622116968998953009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8925855748077979332635339 13388783622116968998953009)
          ·
            refine ⟨10041587716587726749214757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13388783622116968998953009 10041587716587726749214757)
            ·
              refine ⟨1882797696860198765477767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10041587716587726749214757 1882797696860198765477767)
              ·
                refine ⟨2824196545290298148216651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882797696860198765477767 2824196545290298148216651)
                ·
                  refine ⟨4236294817935447222324977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824196545290298148216651 4236294817935447222324977)
                  ·
                    refine ⟨3177221113451585416743733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4236294817935447222324977 3177221113451585416743733)
                    ·
                      refine ⟨297864479386086132819725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3177221113451585416743733 297864479386086132819725)
                      ·
                        rfl

theorem cell23_580089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_580089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580089 prefixEnd_580089 := by exact prefixLift 580089
  have htrace : WordTrace (prefixWord ++ tailWord_580089) baseStart_580089 baseEnd_580089 := by
    simpa [prefixWord, tailWord_580089, baseEnd_580089] using wordTrace_append hprefix tailTrace_580089
  have hstable : (prefixWord ++ tailWord_580089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580089).length < 2 ^ (prefixWord ++ tailWord_580089).sum := by decide
  have hdescent : baseEnd_580089 < baseStart_580089 := by decide
  rcases family_descends (prefixWord ++ tailWord_580089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580099 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_580099 : Nat := 118140960795 + 580099 * 2 ^ 59
def prefixEnd_580099 : Nat := 4983230072969 + 3 ^ 40 * 580099 * 2
def baseEnd_580099 : Nat := 297869614192631093694679

theorem tailTrace_580099 : CollatzResearch.WordTrace tailWord_580099 prefixEnd_580099 297869614192631093694679 := by
  unfold tailWord_580099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21157948725407870866703351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14105299150271913911135567 21157948725407870866703351)
  ·
    refine ⟨31736923088111806300055027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21157948725407870866703351 31736923088111806300055027)
    ·
      refine ⟨47605384632167709450082541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31736923088111806300055027 47605384632167709450082541)
      ·
        refine ⟨17852019237062891043780953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47605384632167709450082541 17852019237062891043780953)
        ·
          refine ⟨13389014427797168282835715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17852019237062891043780953 13389014427797168282835715)
          ·
            refine ⟨20083521641695752424253573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13389014427797168282835715 20083521641695752424253573)
            ·
              refine ⟨3765660307817953579547545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20083521641695752424253573 3765660307817953579547545)
              ·
                refine ⟨2824245230863465184660659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3765660307817953579547545 2824245230863465184660659)
                ·
                  refine ⟨4236367846295197776990989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2824245230863465184660659 4236367846295197776990989)
                  ·
                    refine ⟨1588637942360699166371621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4236367846295197776990989 1588637942360699166371621)
                    ·
                      refine ⟨297869614192631093694679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1588637942360699166371621 297869614192631093694679)
                      ·
                        rfl

theorem cell23_580099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_580099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580099 prefixEnd_580099 := by exact prefixLift 580099
  have htrace : WordTrace (prefixWord ++ tailWord_580099) baseStart_580099 baseEnd_580099 := by
    simpa [prefixWord, tailWord_580099, baseEnd_580099] using wordTrace_append hprefix tailTrace_580099
  have hstable : (prefixWord ++ tailWord_580099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580099).length < 2 ^ (prefixWord ++ tailWord_580099).sum := by decide
  have hdescent : baseEnd_580099 < baseStart_580099 := by decide
  rcases family_descends (prefixWord ++ tailWord_580099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580129 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_580129 : Nat := 118140960795 + 580129 * 2 ^ 59
def prefixEnd_580129 : Nat := 4983230072969 + 3 ^ 40 * 580129 * 2
def baseEnd_580129 : Nat := 297885018612265976319541

theorem tailTrace_580129 : CollatzResearch.WordTrace tailWord_580129 prefixEnd_580129 297885018612265976319541 := by
  unfold tailWord_580129
  simp only [CollatzResearch.WordTrace]
  refine ⟨21159042915299185990295441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14106028610199457326863627 21159042915299185990295441)
  ·
    refine ⟨15869282186474389492721581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21159042915299185990295441 15869282186474389492721581)
    ·
      refine ⟨5950980819927896059770593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15869282186474389492721581 5950980819927896059770593)
      ·
        refine ⟨4463235614945922044827945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5950980819927896059770593 4463235614945922044827945)
        ·
          refine ⟨3347426711209441533620959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4463235614945922044827945 3347426711209441533620959)
          ·
            refine ⟨5021140066814162300431439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347426711209441533620959 5021140066814162300431439)
            ·
              refine ⟨7531710100221243450647159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021140066814162300431439 7531710100221243450647159)
              ·
                refine ⟨11297565150331865175970739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7531710100221243450647159 11297565150331865175970739)
                ·
                  refine ⟨16946347725497797763956109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11297565150331865175970739 16946347725497797763956109)
                  ·
                    refine ⟨6354880397061674161483541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16946347725497797763956109 6354880397061674161483541)
                    ·
                      refine ⟨297885018612265976319541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6354880397061674161483541 297885018612265976319541)
                      ·
                        rfl

theorem cell23_580129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_580129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580129 prefixEnd_580129 := by exact prefixLift 580129
  have htrace : WordTrace (prefixWord ++ tailWord_580129) baseStart_580129 baseEnd_580129 := by
    simpa [prefixWord, tailWord_580129, baseEnd_580129] using wordTrace_append hprefix tailTrace_580129
  have hstable : (prefixWord ++ tailWord_580129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580129).length < 2 ^ (prefixWord ++ tailWord_580129).sum := by decide
  have hdescent : baseEnd_580129 < baseStart_580129 := by decide
  rcases family_descends (prefixWord ++ tailWord_580129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580150 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_580150 : Nat := 118140960795 + 580150 * 2 ^ 59
def prefixEnd_580150 : Nat := 4983230072969 + 3 ^ 40 * 580150 * 2
def baseEnd_580150 : Nat := 297895801706010394156945

theorem tailTrace_580150 : CollatzResearch.WordTrace tailWord_580150 prefixEnd_580150 297895801706010394156945 := by
  unfold tailWord_580150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322488053013944161050619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14106539232148737717873269 1322488053013944161050619)
  ·
    refine ⟨1983732079520916241575929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322488053013944161050619 1983732079520916241575929)
    ·
      refine ⟨1487799059640687181181947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983732079520916241575929 1487799059640687181181947)
      ·
        refine ⟨2231698589461030771772921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1487799059640687181181947 2231698589461030771772921)
        ·
          refine ⟨1673773942095773078829691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2231698589461030771772921 1673773942095773078829691)
          ·
            refine ⟨2510660913143659618244537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1673773942095773078829691 2510660913143659618244537)
            ·
              refine ⟨1882995684857744713683403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2510660913143659618244537 1882995684857744713683403)
              ·
                refine ⟨2824493527286617070525105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1882995684857744713683403 2824493527286617070525105)
                ·
                  refine ⟨2118370145464962802893829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2824493527286617070525105 2118370145464962802893829)
                  ·
                    refine ⟨397194402274680525542593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2118370145464962802893829 397194402274680525542593)
                    ·
                      refine ⟨297895801706010394156945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397194402274680525542593 297895801706010394156945)
                      ·
                        rfl

theorem cell23_580150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_580150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580150 prefixEnd_580150 := by exact prefixLift 580150
  have htrace : WordTrace (prefixWord ++ tailWord_580150) baseStart_580150 baseEnd_580150 := by
    simpa [prefixWord, tailWord_580150, baseEnd_580150] using wordTrace_append hprefix tailTrace_580150
  have hstable : (prefixWord ++ tailWord_580150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580150).length < 2 ^ (prefixWord ++ tailWord_580150).sum := by decide
  have hdescent : baseEnd_580150 < baseStart_580150 := by decide
  rcases family_descends (prefixWord ++ tailWord_580150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580159 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_580159 : Nat := 118140960795 + 580159 * 2 ^ 59
def prefixEnd_580159 : Nat := 4983230072969 + 3 ^ 40 * 580159 * 2
def baseEnd_580159 : Nat := 297900423031900858944403

theorem tailTrace_580159 : CollatzResearch.WordTrace tailWord_580159 prefixEnd_580159 297900423031900858944403 := by
  unfold tailWord_580159
  simp only [CollatzResearch.WordTrace]
  refine ⟨21160137105190501113887531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14106758070127000742591687 21160137105190501113887531)
  ·
    refine ⟨31740205657785751670831297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21160137105190501113887531 31740205657785751670831297)
    ·
      refine ⟨23805154243339313753123473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31740205657785751670831297 23805154243339313753123473)
      ·
        refine ⟨17853865682504485314842605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23805154243339313753123473 17853865682504485314842605)
        ·
          refine ⟨6695199630939181993065977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17853865682504485314842605 6695199630939181993065977)
          ·
            refine ⟨5021399723204386494799483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6695199630939181993065977 5021399723204386494799483)
            ·
              refine ⟨7532099584806579742199225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5021399723204386494799483 7532099584806579742199225)
              ·
                refine ⟨5649074688604934806649419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7532099584806579742199225 5649074688604934806649419)
                ·
                  refine ⟨8473612032907402209974129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5649074688604934806649419 8473612032907402209974129)
                  ·
                    refine ⟨6355209024680551657480597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8473612032907402209974129 6355209024680551657480597)
                    ·
                      refine ⟨297900423031900858944403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6355209024680551657480597 297900423031900858944403)
                      ·
                        rfl

theorem cell23_580159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_580159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580159 prefixEnd_580159 := by exact prefixLift 580159
  have htrace : WordTrace (prefixWord ++ tailWord_580159) baseStart_580159 baseEnd_580159 := by
    simpa [prefixWord, tailWord_580159, baseEnd_580159] using wordTrace_append hprefix tailTrace_580159
  have hstable : (prefixWord ++ tailWord_580159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580159).length < 2 ^ (prefixWord ++ tailWord_580159).sum := by decide
  have hdescent : baseEnd_580159 < baseStart_580159 := by decide
  rcases family_descends (prefixWord ++ tailWord_580159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580193 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 4, 3, 2]
def baseStart_580193 : Nat := 118140960795 + 580193 * 2 ^ 59
def prefixEnd_580193 : Nat := 4983230072969 + 3 ^ 40 * 580193 * 2
def baseEnd_580193 : Nat := 297917881374153725919247

theorem tailTrace_580193 : CollatzResearch.WordTrace tailWord_580193 prefixEnd_580193 297917881374153725919247 := by
  unfold tailWord_580193
  simp only [CollatzResearch.WordTrace]
  refine ⟨21161377187067324920625233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14107584791378216613750155 21161377187067324920625233)
  ·
    refine ⟨15871032890300493690468925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21161377187067324920625233 15871032890300493690468925)
    ·
      refine ⟨5951637333862685133925847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15871032890300493690468925 5951637333862685133925847)
      ·
        refine ⟨8927456000794027700888771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5951637333862685133925847 8927456000794027700888771)
        ·
          refine ⟨13391184001191041551333157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8927456000794027700888771 13391184001191041551333157)
          ·
            refine ⟨2510847000223320290874967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13391184001191041551333157 2510847000223320290874967)
            ·
              refine ⟨3766270500334980436312451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2510847000223320290874967 3766270500334980436312451)
              ·
                refine ⟨5649405750502470654468677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3766270500334980436312451 5649405750502470654468677)
                ·
                  refine ⟨1059263578219213247712877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5649405750502470654468677 1059263578219213247712877)
                  ·
                    refine ⟨397223841832204967892329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1059263578219213247712877 397223841832204967892329)
                    ·
                      refine ⟨297917881374153725919247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397223841832204967892329 297917881374153725919247)
                      ·
                        rfl

theorem cell23_580193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3, 2].length) (baseStart_580193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580193 prefixEnd_580193 := by exact prefixLift 580193
  have htrace : WordTrace (prefixWord ++ tailWord_580193) baseStart_580193 baseEnd_580193 := by
    simpa [prefixWord, tailWord_580193, baseEnd_580193] using wordTrace_append hprefix tailTrace_580193
  have hstable : (prefixWord ++ tailWord_580193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580193).length < 2 ^ (prefixWord ++ tailWord_580193).sum := by decide
  have hdescent : baseEnd_580193 < baseStart_580193 := by decide
  rcases family_descends (prefixWord ++ tailWord_580193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580194 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_580194 : Nat := 118140960795 + 580194 * 2 ^ 59
def prefixEnd_580194 : Nat := 4983230072969 + 3 ^ 40 * 580194 * 2
def baseEnd_580194 : Nat := 99306131618269407335581

theorem tailTrace_580194 : CollatzResearch.WordTrace tailWord_580194 prefixEnd_580194 99306131618269407335581 := by
  unfold tailWord_580194
  simp only [CollatzResearch.WordTrace]
  refine ⟨5290353415015925522852909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14107609106709134727607757 5290353415015925522852909)
  ·
    refine ⟨1983882530630972071069841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5290353415015925522852909 1983882530630972071069841)
    ·
      refine ⟨1487911897973229053302381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1983882530630972071069841 1487911897973229053302381)
      ·
        refine ⟨557966961739960894988393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1487911897973229053302381 557966961739960894988393)
        ·
          refine ⟨418475221304970671241295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 557966961739960894988393 418475221304970671241295)
          ·
            refine ⟨627712831957456006861943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418475221304970671241295 627712831957456006861943)
            ·
              refine ⟨941569247936184010292915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627712831957456006861943 941569247936184010292915)
              ·
                refine ⟨1412353871904276015439373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 941569247936184010292915 1412353871904276015439373)
                ·
                  refine ⟨529632701964103505789765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1412353871904276015439373 529632701964103505789765)
                  ·
                    refine ⟨99306131618269407335581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 529632701964103505789765 99306131618269407335581)
                    ·
                      rfl

theorem cell23_580194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_580194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580194 prefixEnd_580194 := by exact prefixLift 580194
  have htrace : WordTrace (prefixWord ++ tailWord_580194) baseStart_580194 baseEnd_580194 := by
    simpa [prefixWord, tailWord_580194, baseEnd_580194] using wordTrace_append hprefix tailTrace_580194
  have hstable : (prefixWord ++ tailWord_580194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580194).length < 2 ^ (prefixWord ++ tailWord_580194).sum := by decide
  have hdescent : baseEnd_580194 < baseStart_580194 := by decide
  rcases family_descends (prefixWord ++ tailWord_580194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580270 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_580270 : Nat := 118140960795 + 580270 * 2 ^ 59
def prefixEnd_580270 : Nat := 4983230072969 + 3 ^ 40 * 580270 * 2
def baseEnd_580270 : Nat := 297957419384549924656393

theorem tailTrace_580270 : CollatzResearch.WordTrace tailWord_580270 prefixEnd_580270 297957419384549924656393 := by
  unfold tailWord_580270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645523200973545883897283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14109457071858911380785509 2645523200973545883897283)
  ·
    refine ⟨3968284801460318825845925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2645523200973545883897283 3968284801460318825845925)
    ·
      refine ⟨744053400273809779846111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3968284801460318825845925 744053400273809779846111)
      ·
        refine ⟨1116080100410714669769167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744053400273809779846111 1116080100410714669769167)
        ·
          refine ⟨1674120150616072004653751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116080100410714669769167 1674120150616072004653751)
          ·
            refine ⟨2511180225924108006980627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674120150616072004653751 2511180225924108006980627)
            ·
              refine ⟨3766770338886162010470941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2511180225924108006980627 3766770338886162010470941)
              ·
                refine ⟨1412538877082310753926603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3766770338886162010470941 1412538877082310753926603)
                ·
                  refine ⟨2118808315623466130889905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1412538877082310753926603 2118808315623466130889905)
                  ·
                    refine ⟨1589106236717599598167429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2118808315623466130889905 1589106236717599598167429)
                    ·
                      refine ⟨297957419384549924656393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1589106236717599598167429 297957419384549924656393)
                      ·
                        rfl

theorem cell23_580270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_580270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580270 prefixEnd_580270 := by exact prefixLift 580270
  have htrace : WordTrace (prefixWord ++ tailWord_580270) baseStart_580270 baseEnd_580270 := by
    simpa [prefixWord, tailWord_580270, baseEnd_580270] using wordTrace_append hprefix tailTrace_580270
  have hstable : (prefixWord ++ tailWord_580270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580270).length < 2 ^ (prefixWord ++ tailWord_580270).sum := by decide
  have hdescent : baseEnd_580270 < baseStart_580270 := by decide
  rcases family_descends (prefixWord ++ tailWord_580270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580301 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 2, 4]
def baseStart_580301 : Nat := 118140960795 + 580301 * 2 ^ 59
def prefixEnd_580301 : Nat := 4983230072969 + 3 ^ 40 * 580301 * 2
def baseEnd_580301 : Nat := 99324445761613101122917

theorem tailTrace_580301 : CollatzResearch.WordTrace tailWord_580301 prefixEnd_580301 99324445761613101122917 := by
  unfold tailWord_580301
  simp only [CollatzResearch.WordTrace]
  refine ⟨21165316270676059365556757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14110210847117372910371171 21165316270676059365556757)
  ·
    refine ⟨992124200187940282760473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21165316270676059365556757 992124200187940282760473)
    ·
      refine ⟨744093150140955212070355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 992124200187940282760473 744093150140955212070355)
      ·
        refine ⟨1116139725211432818105533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744093150140955212070355 1116139725211432818105533)
        ·
          refine ⟨418552396954287306789575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1116139725211432818105533 418552396954287306789575)
          ·
            refine ⟨627828595431430960184363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418552396954287306789575 627828595431430960184363)
            ·
              refine ⟨941742893147146440276545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627828595431430960184363 941742893147146440276545)
              ·
                refine ⟨706307169860359830207409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941742893147146440276545 706307169860359830207409)
                ·
                  refine ⟨529730377395269872655557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706307169860359830207409 529730377395269872655557)
                  ·
                    refine ⟨99324445761613101122917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 529730377395269872655557 99324445761613101122917)
                    ·
                      rfl

theorem cell23_580301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_580301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580301 prefixEnd_580301 := by exact prefixLift 580301
  have htrace : WordTrace (prefixWord ++ tailWord_580301) baseStart_580301 baseEnd_580301 := by
    simpa [prefixWord, tailWord_580301, baseEnd_580301] using wordTrace_append hprefix tailTrace_580301
  have hstable : (prefixWord ++ tailWord_580301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580301).length < 2 ^ (prefixWord ++ tailWord_580301).sum := by decide
  have hdescent : baseEnd_580301 < baseStart_580301 := by decide
  rcases family_descends (prefixWord ++ tailWord_580301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580323 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 2, 6]
def baseStart_580323 : Nat := 118140960795 + 580323 * 2 ^ 59
def prefixEnd_580323 : Nat := 4983230072969 + 3 ^ 40 * 580323 * 2
def baseEnd_580323 : Nat := 99328211286412739097883

theorem tailTrace_580323 : CollatzResearch.WordTrace tailWord_580323 prefixEnd_580323 99328211286412739097883 := by
  unfold tailWord_580323
  simp only [CollatzResearch.WordTrace]
  refine ⟨21166118676596357122857623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14110745784397571415238415 21166118676596357122857623)
  ·
    refine ⟨31749178014894535684286435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21166118676596357122857623 31749178014894535684286435)
    ·
      refine ⟨47623767022341803526429653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31749178014894535684286435 47623767022341803526429653)
      ·
        refine ⟨1116182039586136020150695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 47623767022341803526429653 1116182039586136020150695)
        ·
          refine ⟨1674273059379204030226043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1116182039586136020150695 1674273059379204030226043)
          ·
            refine ⟨2511409589068806045339065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674273059379204030226043 2511409589068806045339065)
            ·
              refine ⟨1883557191801604534004299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2511409589068806045339065 1883557191801604534004299)
              ·
                refine ⟨2825335787702406801006449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883557191801604534004299 2825335787702406801006449)
                ·
                  refine ⟨2119001840776805100754837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825335787702406801006449 2119001840776805100754837)
                  ·
                    refine ⟨99328211286412739097883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2119001840776805100754837 99328211286412739097883)
                    ·
                      rfl

theorem cell23_580323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 6].length) (baseStart_580323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580323 prefixEnd_580323 := by exact prefixLift 580323
  have htrace : WordTrace (prefixWord ++ tailWord_580323) baseStart_580323 baseEnd_580323 := by
    simpa [prefixWord, tailWord_580323, baseEnd_580323] using wordTrace_append hprefix tailTrace_580323
  have hstable : (prefixWord ++ tailWord_580323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580323).length < 2 ^ (prefixWord ++ tailWord_580323).sum := by decide
  have hdescent : baseEnd_580323 < baseStart_580323 := by decide
  rcases family_descends (prefixWord ++ tailWord_580323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580333 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_580333 : Nat := 118140960795 + 580333 * 2 ^ 59
def prefixEnd_580333 : Nat := 4983230072969 + 3 ^ 40 * 580333 * 2
def baseEnd_580333 : Nat := 297989768665783178168603

theorem tailTrace_580333 : CollatzResearch.WordTrace tailWord_580333 prefixEnd_580333 297989768665783178168603 := by
  unfold tailWord_580333
  simp only [CollatzResearch.WordTrace]
  refine ⟨21166483406560128830721653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14110988937706752553814435 21166483406560128830721653)
  ·
    refine ⟨1984357819365012077880155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21166483406560128830721653 1984357819365012077880155)
    ·
      refine ⟨2976536729047518116820233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1984357819365012077880155 2976536729047518116820233)
      ·
        refine ⟨2232402546785638587615175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2976536729047518116820233 2232402546785638587615175)
        ·
          refine ⟨3348603820178457881422763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2232402546785638587615175 3348603820178457881422763)
          ·
            refine ⟨5022905730267686822134145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3348603820178457881422763 5022905730267686822134145)
            ·
              refine ⟨3767179297700765116600609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5022905730267686822134145 3767179297700765116600609)
              ·
                refine ⟨2825384473275573837450457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3767179297700765116600609 2825384473275573837450457)
                ·
                  refine ⟨2119038354956680378087843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825384473275573837450457 2119038354956680378087843)
                  ·
                    refine ⟨3178557532435020567131765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119038354956680378087843 3178557532435020567131765)
                    ·
                      refine ⟨297989768665783178168603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3178557532435020567131765 297989768665783178168603)
                      ·
                        rfl

theorem cell23_580333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_580333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580333 prefixEnd_580333 := by exact prefixLift 580333
  have htrace : WordTrace (prefixWord ++ tailWord_580333) baseStart_580333 baseEnd_580333 := by
    simpa [prefixWord, tailWord_580333, baseEnd_580333] using wordTrace_append hprefix tailTrace_580333
  have hstable : (prefixWord ++ tailWord_580333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580333).length < 2 ^ (prefixWord ++ tailWord_580333).sum := by decide
  have hdescent : baseEnd_580333 < baseStart_580333 := by decide
  rcases family_descends (prefixWord ++ tailWord_580333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580336 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 7]
def baseStart_580336 : Nat := 118140960795 + 580336 * 2 ^ 59
def prefixEnd_580336 : Nat := 4983230072969 + 3 ^ 40 * 580336 * 2
def baseEnd_580336 : Nat := 33110145456416296270121

theorem tailTrace_580336 : CollatzResearch.WordTrace tailWord_580336 prefixEnd_580336 33110145456416296270121 := by
  unfold tailWord_580336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10583296412774630171540431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14111061883699506895387241 10583296412774630171540431)
  ·
    refine ⟨15874944619161945257310647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10583296412774630171540431 15874944619161945257310647)
    ·
      refine ⟨23812416928742917885965971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15874944619161945257310647 23812416928742917885965971)
      ·
        refine ⟨35718625393114376828948957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23812416928742917885965971 35718625393114376828948957)
        ·
          refine ⟨13394484522417891310855859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35718625393114376828948957 13394484522417891310855859)
          ·
            refine ⟨20091726783626836966283789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13394484522417891310855859 20091726783626836966283789)
            ·
              refine ⟨7534397543860063862356421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20091726783626836966283789 7534397543860063862356421)
              ·
                refine ⟨1412699539473761974191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7534397543860063862356421 1412699539473761974191829)
                ·
                  refine ⟨33110145456416296270121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1412699539473761974191829 33110145456416296270121)
                  ·
                    rfl

theorem cell23_580336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_580336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580336 prefixEnd_580336 := by exact prefixLift 580336
  have htrace : WordTrace (prefixWord ++ tailWord_580336) baseStart_580336 baseEnd_580336 := by
    simpa [prefixWord, tailWord_580336, baseEnd_580336] using wordTrace_append hprefix tailTrace_580336
  have hstable : (prefixWord ++ tailWord_580336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580336).length < 2 ^ (prefixWord ++ tailWord_580336).sum := by decide
  have hdescent : baseEnd_580336 < baseStart_580336 := by decide
  rcases family_descends (prefixWord ++ tailWord_580336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580350 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_580350 : Nat := 118140960795 + 580350 * 2 ^ 59
def prefixEnd_580350 : Nat := 4983230072969 + 3 ^ 40 * 580350 * 2
def baseEnd_580350 : Nat := 297998497836909611656025

theorem tailTrace_580350 : CollatzResearch.WordTrace tailWord_580350 prefixEnd_580350 297998497836909611656025 := by
  unfold tailWord_580350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2645887930937317591761313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14111402298332360489393669 2645887930937317591761313)
  ·
    refine ⟨1984415948202988193820985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2645887930937317591761313 1984415948202988193820985)
    ·
      refine ⟨1488311961152241145365739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1984415948202988193820985 1488311961152241145365739)
      ·
        refine ⟨2232467941728361718048609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1488311961152241145365739 2232467941728361718048609)
        ·
          refine ⟨1674350956296271288536457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2232467941728361718048609 1674350956296271288536457)
          ·
            refine ⟨1255763217222203466402343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1674350956296271288536457 1255763217222203466402343)
            ·
              refine ⟨1883644825833305199603515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255763217222203466402343 1883644825833305199603515)
              ·
                refine ⟨2825467238749957799405273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1883644825833305199603515 2825467238749957799405273)
                ·
                  refine ⟨2119100429062468349553955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2825467238749957799405273 2119100429062468349553955)
                  ·
                    refine ⟨3178650643593702524330933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119100429062468349553955 3178650643593702524330933)
                    ·
                      refine ⟨297998497836909611656025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3178650643593702524330933 297998497836909611656025)
                      ·
                        rfl

theorem cell23_580350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_580350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580350 prefixEnd_580350 := by exact prefixLift 580350
  have htrace : WordTrace (prefixWord ++ tailWord_580350) baseStart_580350 baseEnd_580350 := by
    simpa [prefixWord, tailWord_580350, baseEnd_580350] using wordTrace_append hprefix tailTrace_580350
  have hstable : (prefixWord ++ tailWord_580350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580350).length < 2 ^ (prefixWord ++ tailWord_580350).sum := by decide
  have hdescent : baseEnd_580350 < baseStart_580350 := by decide
  rcases family_descends (prefixWord ++ tailWord_580350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580381 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_580381 : Nat := 118140960795 + 580381 * 2 ^ 59
def prefixEnd_580381 : Nat := 4983230072969 + 3 ^ 40 * 580381 * 2
def baseEnd_580381 : Nat := 298014415737198990368383

theorem tailTrace_580381 : CollatzResearch.WordTrace tailWord_580381 prefixEnd_580381 298014415737198990368383 := by
  unfold tailWord_580381
  simp only [CollatzResearch.WordTrace]
  refine ⟨21168234110386233028468997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14112156073590822018979331 21168234110386233028468997)
  ·
    refine ⟨3969043895697418692837937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21168234110386233028468997 3969043895697418692837937)
    ·
      refine ⟨2976782921773064019628453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3969043895697418692837937 2976782921773064019628453)
      ·
        refine ⟨558146797832449503680335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2976782921773064019628453 558146797832449503680335)
        ·
          refine ⟨837220196748674255520503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558146797832449503680335 837220196748674255520503)
          ·
            refine ⟨1255830295123011383280755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837220196748674255520503 1255830295123011383280755)
            ·
              refine ⟨1883745442684517074921133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1255830295123011383280755 1883745442684517074921133)
              ·
                refine ⟨706404541006693903095425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1883745442684517074921133 706404541006693903095425)
                ·
                  refine ⟨529803405755020427321569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706404541006693903095425 529803405755020427321569)
                  ·
                    refine ⟨397352554316265320491177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 529803405755020427321569 397352554316265320491177)
                    ·
                      refine ⟨298014415737198990368383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397352554316265320491177 298014415737198990368383)
                      ·
                        rfl

theorem cell23_580381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_580381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580381 prefixEnd_580381 := by exact prefixLift 580381
  have htrace : WordTrace (prefixWord ++ tailWord_580381) baseStart_580381 baseEnd_580381 := by
    simpa [prefixWord, tailWord_580381, baseEnd_580381] using wordTrace_append hprefix tailTrace_580381
  have hstable : (prefixWord ++ tailWord_580381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580381).length < 2 ^ (prefixWord ++ tailWord_580381).sum := by decide
  have hdescent : baseEnd_580381 < baseStart_580381 := by decide
  rcases family_descends (prefixWord ++ tailWord_580381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580423 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_580423 : Nat := 118140960795 + 580423 * 2 ^ 59
def prefixEnd_580423 : Nat := 4983230072969 + 3 ^ 40 * 580423 * 2
def baseEnd_580423 : Nat := 298035981924687826043189

theorem tailTrace_580423 : CollatzResearch.WordTrace tailWord_580423 prefixEnd_580423 298035981924687826043189 := by
  unfold tailWord_580423
  simp only [CollatzResearch.WordTrace]
  refine ⟨21169765976234074201497923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14113177317489382800998615 21169765976234074201497923)
  ·
    refine ⟨31754648964351111302246885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21169765976234074201497923 31754648964351111302246885)
    ·
      refine ⟨5953996680815833369171291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31754648964351111302246885 5953996680815833369171291)
      ·
        refine ⟨8930995021223750053756937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5953996680815833369171291 8930995021223750053756937)
        ·
          refine ⟨6698246265917812540317703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8930995021223750053756937 6698246265917812540317703)
          ·
            refine ⟨10047369398876718810476555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6698246265917812540317703 10047369398876718810476555)
            ·
              refine ⟨15071054098315078215714833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10047369398876718810476555 15071054098315078215714833)
              ·
                refine ⟨11303290573736308661786125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15071054098315078215714833 11303290573736308661786125)
                ·
                  refine ⟨4238733965151115748169797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11303290573736308661786125 4238733965151115748169797)
                  ·
                    refine ⟨794762618465834202781837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4238733965151115748169797 794762618465834202781837)
                    ·
                      refine ⟨298035981924687826043189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794762618465834202781837 298035981924687826043189)
                      ·
                        rfl

theorem cell23_580423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_580423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580423 prefixEnd_580423 := by exact prefixLift 580423
  have htrace : WordTrace (prefixWord ++ tailWord_580423) baseStart_580423 baseEnd_580423 := by
    simpa [prefixWord, tailWord_580423, baseEnd_580423] using wordTrace_append hprefix tailTrace_580423
  have hstable : (prefixWord ++ tailWord_580423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580423).length < 2 ^ (prefixWord ++ tailWord_580423).sum := by decide
  have hdescent : baseEnd_580423 < baseStart_580423 := by decide
  rcases family_descends (prefixWord ++ tailWord_580423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580487 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_580487 : Nat := 118140960795 + 580487 * 2 ^ 59
def prefixEnd_580487 : Nat := 4983230072969 + 3 ^ 40 * 580487 * 2
def baseEnd_580487 : Nat := 298068844686575575642895

theorem tailTrace_580487 : CollatzResearch.WordTrace tailWord_580487 prefixEnd_580487 298068844686575575642895 := by
  unfold tailWord_580487
  simp only [CollatzResearch.WordTrace]
  refine ⟨21172100248002213131827715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14114733498668142087885143 21172100248002213131827715)
  ·
    refine ⟨31758150372003319697741573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21172100248002213131827715 31758150372003319697741573)
    ·
      refine ⟨5954653194750622443326545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31758150372003319697741573 5954653194750622443326545)
      ·
        refine ⟨4465989896062966832494909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5954653194750622443326545 4465989896062966832494909)
        ·
          refine ⟨1674746211023612562185591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4465989896062966832494909 1674746211023612562185591)
          ·
            refine ⟨2512119316535418843278387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1674746211023612562185591 2512119316535418843278387)
            ·
              refine ⟨3768178974803128264917581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2512119316535418843278387 3768178974803128264917581)
              ·
                refine ⟨1413067115551173099344093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3768178974803128264917581 1413067115551173099344093)
                ·
                  refine ⟨529900168331689912254035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1413067115551173099344093 529900168331689912254035)
                  ·
                    refine ⟨794850252497534868381053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 529900168331689912254035 794850252497534868381053)
                    ·
                      refine ⟨298068844686575575642895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794850252497534868381053 298068844686575575642895)
                      ·
                        rfl

theorem cell23_580487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_580487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580487 prefixEnd_580487 := by exact prefixLift 580487
  have htrace : WordTrace (prefixWord ++ tailWord_580487) baseStart_580487 baseEnd_580487 := by
    simpa [prefixWord, tailWord_580487, baseEnd_580487] using wordTrace_append hprefix tailTrace_580487
  have hstable : (prefixWord ++ tailWord_580487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580487).length < 2 ^ (prefixWord ++ tailWord_580487).sum := by decide
  have hdescent : baseEnd_580487 < baseStart_580487 := by decide
  rcases family_descends (prefixWord ++ tailWord_580487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580530 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_580530 : Nat := 118140960795 + 580530 * 2 ^ 59
def prefixEnd_580530 : Nat := 4983230072969 + 3 ^ 40 * 580530 * 2
def baseEnd_580530 : Nat := 298090924354718907405197

theorem tailTrace_580530 : CollatzResearch.WordTrace tailWord_580530 prefixEnd_580530 298090924354718907405197 := by
  unfold tailWord_580530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5293417146711607868910761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14115779057897620983762029 5293417146711607868910761)
  ·
    refine ⟨3970062860033705901683071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5293417146711607868910761 3970062860033705901683071)
    ·
      refine ⟨5955094290050558852524607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3970062860033705901683071 5955094290050558852524607)
      ·
        refine ⟨8932641435075838278786911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5955094290050558852524607 8932641435075838278786911)
        ·
          refine ⟨13398962152613757418180367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8932641435075838278786911 13398962152613757418180367)
          ·
            refine ⟨20098443228920636127270551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13398962152613757418180367 20098443228920636127270551)
            ·
              refine ⟨30147664843380954190905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20098443228920636127270551 30147664843380954190905827)
              ·
                refine ⟨45221497265071431286358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30147664843380954190905827 45221497265071431286358741)
                ·
                  refine ⟨1059878842150111670774033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 45221497265071431286358741 1059878842150111670774033)
                  ·
                    refine ⟨794909131612583753080525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1059878842150111670774033 794909131612583753080525)
                    ·
                      refine ⟨298090924354718907405197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794909131612583753080525 298090924354718907405197)
                      ·
                        rfl

theorem cell23_580530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_580530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580530 prefixEnd_580530 := by exact prefixLift 580530
  have htrace : WordTrace (prefixWord ++ tailWord_580530) baseStart_580530 baseEnd_580530 := by
    simpa [prefixWord, tailWord_580530, baseEnd_580530] using wordTrace_append hprefix tailTrace_580530
  have hstable : (prefixWord ++ tailWord_580530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580530).length < 2 ^ (prefixWord ++ tailWord_580530).sum := by decide
  have hdescent : baseEnd_580530 < baseStart_580530 := by decide
  rcases family_descends (prefixWord ++ tailWord_580530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580544 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2]
def baseStart_580544 : Nat := 118140960795 + 580544 * 2 ^ 59
def prefixEnd_580544 : Nat := 4983230072969 + 3 ^ 40 * 580544 * 2
def baseEnd_580544 : Nat := 298098113083881852630133

theorem tailTrace_580544 : CollatzResearch.WordTrace tailWord_580544 prefixEnd_580544 298098113083881852630133 := by
  unfold tailWord_580544
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587089604397855933326343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14116119472530474577768457 10587089604397855933326343)
  ·
    refine ⟨15880634406596783899989515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10587089604397855933326343 15880634406596783899989515)
    ·
      refine ⟨23820951609895175849984273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15880634406596783899989515 23820951609895175849984273)
      ·
        refine ⟨17865713707421381887488205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23820951609895175849984273 17865713707421381887488205)
        ·
          refine ⟨6699642640283018207808077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17865713707421381887488205 6699642640283018207808077)
          ·
            refine ⟨2512365990106131827928029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6699642640283018207808077 2512365990106131827928029)
            ·
              refine ⟨942137246289799435473011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2512365990106131827928029 942137246289799435473011)
              ·
                refine ⟨1413205869434699153209517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942137246289799435473011 1413205869434699153209517)
                ·
                  refine ⟨529952201038012182453569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1413205869434699153209517 529952201038012182453569)
                  ·
                    refine ⟨397464150778509136840177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 529952201038012182453569 397464150778509136840177)
                    ·
                      refine ⟨298098113083881852630133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397464150778509136840177 298098113083881852630133)
                      ·
                        rfl

theorem cell23_580544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 2, 2].length) (baseStart_580544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580544 prefixEnd_580544 := by exact prefixLift 580544
  have htrace : WordTrace (prefixWord ++ tailWord_580544) baseStart_580544 baseEnd_580544 := by
    simpa [prefixWord, tailWord_580544, baseEnd_580544] using wordTrace_append hprefix tailTrace_580544
  have hstable : (prefixWord ++ tailWord_580544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580544).length < 2 ^ (prefixWord ++ tailWord_580544).sum := by decide
  have hdescent : baseEnd_580544 < baseStart_580544 := by decide
  rcases family_descends (prefixWord ++ tailWord_580544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580560 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_580560 : Nat := 118140960795 + 580560 * 2 ^ 59
def prefixEnd_580560 : Nat := 4983230072969 + 3 ^ 40 * 580560 * 2
def baseEnd_580560 : Nat := 298106328774353790030059

theorem tailTrace_580560 : CollatzResearch.WordTrace tailWord_580560 prefixEnd_580560 298106328774353790030059 := by
  unfold tailWord_580560
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587381388368873299617567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14116508517825164399490089 10587381388368873299617567)
  ·
    refine ⟨15881072082553309949426351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10587381388368873299617567 15881072082553309949426351)
    ·
      refine ⟨23821608123829964924139527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15881072082553309949426351 23821608123829964924139527)
      ·
        refine ⟨35732412185744947386209291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23821608123829964924139527 35732412185744947386209291)
        ·
          refine ⟨53598618278617421079313937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35732412185744947386209291 53598618278617421079313937)
          ·
            refine ⟨40198963708963065809485453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53598618278617421079313937 40198963708963065809485453)
            ·
              refine ⟨15074611390861149678557045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40198963708963065809485453 15074611390861149678557045)
              ·
                refine ⟨1413244817893232782364723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15074611390861149678557045 1413244817893232782364723)
                ·
                  refine ⟨2119867226839849173547085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413244817893232782364723 2119867226839849173547085)
                  ·
                    refine ⟨794950210064943440080157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2119867226839849173547085 794950210064943440080157)
                    ·
                      refine ⟨298106328774353790030059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794950210064943440080157 298106328774353790030059)
                      ·
                        rfl

theorem cell23_580560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_580560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580560 prefixEnd_580560 := by exact prefixLift 580560
  have htrace : WordTrace (prefixWord ++ tailWord_580560) baseStart_580560 baseEnd_580560 := by
    simpa [prefixWord, tailWord_580560, baseEnd_580560] using wordTrace_append hprefix tailTrace_580560
  have hstable : (prefixWord ++ tailWord_580560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580560).length < 2 ^ (prefixWord ++ tailWord_580560).sum := by decide
  have hdescent : baseEnd_580560 < baseStart_580560 := by decide
  rcases family_descends (prefixWord ++ tailWord_580560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580564 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_580564 : Nat := 118140960795 + 580564 * 2 ^ 59
def prefixEnd_580564 : Nat := 4983230072969 + 3 ^ 40 * 580564 * 2
def baseEnd_580564 : Nat := 298108382696971774380041

theorem tailTrace_580564 : CollatzResearch.WordTrace tailWord_580564 prefixEnd_580564 298108382696971774380041 := by
  unfold tailWord_580564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10587454334361627641190373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14116605779148836854920497 10587454334361627641190373)
  ·
    refine ⟨1985147687692805182723195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10587454334361627641190373 1985147687692805182723195)
    ·
      refine ⟨2977721531539207774084793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1985147687692805182723195 2977721531539207774084793)
      ·
        refine ⟨2233291148654405830563595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2977721531539207774084793 2233291148654405830563595)
        ·
          refine ⟨3349936722981608745845393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2233291148654405830563595 3349936722981608745845393)
          ·
            refine ⟨2512452542236206559384045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3349936722981608745845393 2512452542236206559384045)
            ·
              refine ⟨942169703338577459769017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2512452542236206559384045 942169703338577459769017)
              ·
                refine ⟨706627277503933094826763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942169703338577459769017 706627277503933094826763)
                ·
                  refine ⟨1059940916255899642240145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706627277503933094826763 1059940916255899642240145)
                  ·
                    refine ⟨794955687191924731680109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1059940916255899642240145 794955687191924731680109)
                    ·
                      refine ⟨298108382696971774380041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 794955687191924731680109 298108382696971774380041)
                      ·
                        rfl

theorem cell23_580564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_580564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580564 prefixEnd_580564 := by exact prefixLift 580564
  have htrace : WordTrace (prefixWord ++ tailWord_580564) baseStart_580564 baseEnd_580564 := by
    simpa [prefixWord, tailWord_580564, baseEnd_580564] using wordTrace_append hprefix tailTrace_580564
  have hstable : (prefixWord ++ tailWord_580564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580564).length < 2 ^ (prefixWord ++ tailWord_580564).sum := by decide
  have hdescent : baseEnd_580564 < baseStart_580564 := by decide
  rcases family_descends (prefixWord ++ tailWord_580564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580581 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 1, 1, 5]
def baseStart_580581 : Nat := 118140960795 + 580581 * 2 ^ 59
def prefixEnd_580581 : Nat := 4983230072969 + 3 ^ 40 * 580581 * 2
def baseEnd_580581 : Nat := 298117111868098207867463

theorem tailTrace_580581 : CollatzResearch.WordTrace tailWord_580581 prefixEnd_580581 298117111868098207867463 := by
  unfold tailWord_580581
  simp only [CollatzResearch.WordTrace]
  refine ⟨21175528709661667185749597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14117019139774444790499731 21175528709661667185749597)
  ·
    refine ⟨7940823266123125194656099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21175528709661667185749597 7940823266123125194656099)
    ·
      refine ⟨11911234899184687791984149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7940823266123125194656099 11911234899184687791984149)
      ·
        refine ⟨558339135899282240249257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11911234899184687791984149 558339135899282240249257)
        ·
          refine ⟨418754351924461680186943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558339135899282240249257 418754351924461680186943)
          ·
            refine ⟨628131527886692520280415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418754351924461680186943 628131527886692520280415)
            ·
              refine ⟨942197291830038780420623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628131527886692520280415 942197291830038780420623)
              ·
                refine ⟨1413295937745058170630935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942197291830038780420623 1413295937745058170630935)
                ·
                  refine ⟨2119943906617587255946403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413295937745058170630935 2119943906617587255946403)
                  ·
                    refine ⟨3179915859926380883919605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2119943906617587255946403 3179915859926380883919605)
                    ·
                      refine ⟨298117111868098207867463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3179915859926380883919605 298117111868098207867463)
                      ·
                        rfl

theorem cell23_580581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_580581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580581 prefixEnd_580581 := by exact prefixLift 580581
  have htrace : WordTrace (prefixWord ++ tailWord_580581) baseStart_580581 baseEnd_580581 := by
    simpa [prefixWord, tailWord_580581, baseEnd_580581] using wordTrace_append hprefix tailTrace_580581
  have hstable : (prefixWord ++ tailWord_580581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580581).length < 2 ^ (prefixWord ++ tailWord_580581).sum := by decide
  have hdescent : baseEnd_580581 < baseStart_580581 := by decide
  rcases family_descends (prefixWord ++ tailWord_580581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580634 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_580634 : Nat := 118140960795 + 580634 * 2 ^ 59
def prefixEnd_580634 : Nat := 4983230072969 + 3 ^ 40 * 580634 * 2
def baseEnd_580634 : Nat := 298144326342786500504719

theorem tailTrace_580634 : CollatzResearch.WordTrace tailWord_580634 prefixEnd_580634 298144326342786500504719 := by
  unfold tailWord_580634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5294365444617414309357239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14118307852313104824952637 5294365444617414309357239)
  ·
    refine ⟨7941548166926121464035859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5294365444617414309357239 7941548166926121464035859)
    ·
      refine ⟨11912322250389182196053789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7941548166926121464035859 11912322250389182196053789)
      ·
        refine ⟨4467120843895943323520171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11912322250389182196053789 4467120843895943323520171)
        ·
          refine ⟨6700681265843914985280257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467120843895943323520171 6700681265843914985280257)
          ·
            refine ⟨5025510949382936238960193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6700681265843914985280257 5025510949382936238960193)
            ·
              refine ⟨3769133212037202179220145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5025510949382936238960193 3769133212037202179220145)
              ·
                refine ⟨2826849909027901634415109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3769133212037202179220145 2826849909027901634415109)
                ·
                  refine ⟨530034357942731556452833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2826849909027901634415109 530034357942731556452833)
                  ·
                    refine ⟨397525768457048667339625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530034357942731556452833 397525768457048667339625)
                    ·
                      refine ⟨298144326342786500504719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397525768457048667339625 298144326342786500504719)
                      ·
                        rfl

theorem cell23_580634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_580634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580634 prefixEnd_580634 := by exact prefixLift 580634
  have htrace : WordTrace (prefixWord ++ tailWord_580634) baseStart_580634 baseEnd_580634 := by
    simpa [prefixWord, tailWord_580634, baseEnd_580634] using wordTrace_append hprefix tailTrace_580634
  have hstable : (prefixWord ++ tailWord_580634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580634).length < 2 ^ (prefixWord ++ tailWord_580634).sum := by decide
  have hdescent : baseEnd_580634 < baseStart_580634 := by decide
  rcases family_descends (prefixWord ++ tailWord_580634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580657 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 5]
def baseStart_580657 : Nat := 118140960795 + 580657 * 2 ^ 59
def prefixEnd_580657 : Nat := 4983230072969 + 3 ^ 40 * 580657 * 2
def baseEnd_580657 : Nat := 33128459599759990057457

theorem tailTrace_580657 : CollatzResearch.WordTrace tailWord_580657 prefixEnd_580657 33128459599759990057457 := by
  unfold tailWord_580657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21178300657386332165516225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14118867104924221443677483 21178300657386332165516225)
  ·
    refine ⟨15883725493039749124137169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21178300657386332165516225 15883725493039749124137169)
    ·
      refine ⟨11912794119779811843102877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15883725493039749124137169 11912794119779811843102877)
      ·
        refine ⟨4467297794917429441163579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11912794119779811843102877 4467297794917429441163579)
        ·
          refine ⟨6700946692376144161745369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4467297794917429441163579 6700946692376144161745369)
          ·
            refine ⟨5025710019282108121309027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6700946692376144161745369 5025710019282108121309027)
            ·
              refine ⟨7538565028923162181963541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5025710019282108121309027 7538565028923162181963541)
              ·
                refine ⟨353370235730773227279541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7538565028923162181963541 353370235730773227279541)
                ·
                  refine ⟨33128459599759990057457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 353370235730773227279541 33128459599759990057457)
                  ·
                    rfl

theorem cell23_580657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 5].length) (baseStart_580657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580657 prefixEnd_580657 := by exact prefixLift 580657
  have htrace : WordTrace (prefixWord ++ tailWord_580657) baseStart_580657 baseEnd_580657 := by
    simpa [prefixWord, tailWord_580657, baseEnd_580657] using wordTrace_append hprefix tailTrace_580657
  have hstable : (prefixWord ++ tailWord_580657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580657).length < 2 ^ (prefixWord ++ tailWord_580657).sum := by decide
  have hdescent : baseEnd_580657 < baseStart_580657 := by decide
  rcases family_descends (prefixWord ++ tailWord_580657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580668 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_580668 : Nat := 118140960795 + 580668 * 2 ^ 59
def prefixEnd_580668 : Nat := 4983230072969 + 3 ^ 40 * 580668 * 2
def baseEnd_580668 : Nat := 298161784685039367479563

theorem tailTrace_580668 : CollatzResearch.WordTrace tailWord_580668 prefixEnd_580668 298161784685039367479563 := by
  unfold tailWord_580668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10589350930173240522083329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14119134573564320696111105 10589350930173240522083329)
  ·
    refine ⟨7942013197629930391562497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10589350930173240522083329 7942013197629930391562497)
    ·
      refine ⟨5956509898222447793671873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7942013197629930391562497 5956509898222447793671873)
      ·
        refine ⟨4467382423666835845253905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5956509898222447793671873 4467382423666835845253905)
        ·
          refine ⟨3350536817750126883940429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4467382423666835845253905 3350536817750126883940429)
          ·
            refine ⟨1256451306656297581477661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3350536817750126883940429 1256451306656297581477661)
            ·
              refine ⟨471169239996111593054123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1256451306656297581477661 471169239996111593054123)
              ·
                refine ⟨706753859994167389581185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 471169239996111593054123 706753859994167389581185)
                ·
                  refine ⟨530065394995625542185889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 706753859994167389581185 530065394995625542185889)
                  ·
                    refine ⟨397549046246719156639417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530065394995625542185889 397549046246719156639417)
                    ·
                      refine ⟨298161784685039367479563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397549046246719156639417 298161784685039367479563)
                      ·
                        rfl

theorem cell23_580668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_580668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580668 prefixEnd_580668 := by exact prefixLift 580668
  have htrace : WordTrace (prefixWord ++ tailWord_580668) baseStart_580668 baseEnd_580668 := by
    simpa [prefixWord, tailWord_580668, baseEnd_580668] using wordTrace_append hprefix tailTrace_580668
  have hstable : (prefixWord ++ tailWord_580668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580668).length < 2 ^ (prefixWord ++ tailWord_580668).sum := by decide
  have hdescent : baseEnd_580668 < baseStart_580668 := by decide
  rcases family_descends (prefixWord ++ tailWord_580668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580677 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 5, 2]
def baseStart_580677 : Nat := 118140960795 + 580677 * 2 ^ 59
def prefixEnd_580677 : Nat := 4983230072969 + 3 ^ 40 * 580677 * 2
def baseEnd_580677 : Nat := 298166406010929832267021

theorem tailTrace_580677 : CollatzResearch.WordTrace tailWord_580677 prefixEnd_580677 298166406010929832267021 := by
  unfold tailWord_580677
  simp only [CollatzResearch.WordTrace]
  refine ⟨21179030117313875581244285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14119353411542583720829523 21179030117313875581244285)
  ·
    refine ⟨7942136293992703342966607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21179030117313875581244285 7942136293992703342966607)
    ·
      refine ⟨11913204440989055014449911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7942136293992703342966607 11913204440989055014449911)
      ·
        refine ⟨17869806661483582521674867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11913204440989055014449911 17869806661483582521674867)
        ·
          refine ⟨26804709992225373782512301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17869806661483582521674867 26804709992225373782512301)
          ·
            refine ⟨10051766247084515168442113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26804709992225373782512301 10051766247084515168442113)
            ·
              refine ⟨7538824685313386376331585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10051766247084515168442113 7538824685313386376331585)
              ·
                refine ⟨5654118513985039782248689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7538824685313386376331585 5654118513985039782248689)
                ·
                  refine ⟨4240588885488779836686517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5654118513985039782248689 4240588885488779836686517)
                  ·
                    refine ⟨397555208014573109689361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4240588885488779836686517 397555208014573109689361)
                    ·
                      refine ⟨298166406010929832267021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397555208014573109689361 298166406010929832267021)
                      ·
                        rfl

theorem cell23_580677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5, 2].length) (baseStart_580677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580677 prefixEnd_580677 := by exact prefixLift 580677
  have htrace : WordTrace (prefixWord ++ tailWord_580677) baseStart_580677 baseEnd_580677 := by
    simpa [prefixWord, tailWord_580677, baseEnd_580677] using wordTrace_append hprefix tailTrace_580677
  have hstable : (prefixWord ++ tailWord_580677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580677).length < 2 ^ (prefixWord ++ tailWord_580677).sum := by decide
  have hdescent : baseEnd_580677 < baseStart_580677 := by decide
  rcases family_descends (prefixWord ++ tailWord_580677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580727 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_580727 : Nat := 118140960795 + 580727 * 2 ^ 59
def prefixEnd_580727 : Nat := 4983230072969 + 3 ^ 40 * 580727 * 2
def baseEnd_580727 : Nat := 298192080043654636641791

theorem tailTrace_580727 : CollatzResearch.WordTrace tailWord_580727 prefixEnd_580727 298192080043654636641791 := by
  unfold tailWord_580727
  simp only [CollatzResearch.WordTrace]
  refine ⟨21180853767132734120564435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14120569178088489413709623 21180853767132734120564435)
  ·
    refine ⟨31771280650699101180846653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21180853767132734120564435 31771280650699101180846653)
    ·
      refine ⟨11914230244012162942817495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31771280650699101180846653 11914230244012162942817495)
      ·
        refine ⟨17871345366018244414226243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11914230244012162942817495 17871345366018244414226243)
        ·
          refine ⟨26807018049027366621339365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17871345366018244414226243 26807018049027366621339365)
          ·
            refine ⟨5026315884192631241501131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26807018049027366621339365 5026315884192631241501131)
            ·
              refine ⟨7539473826288946862251697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5026315884192631241501131 7539473826288946862251697)
              ·
                refine ⟨5654605369716710146688773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7539473826288946862251697 5654605369716710146688773)
                ·
                  refine ⟨1060238506821883152504145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5654605369716710146688773 1060238506821883152504145)
                  ·
                    refine ⟨795178880116412364378109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060238506821883152504145 795178880116412364378109)
                    ·
                      refine ⟨298192080043654636641791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795178880116412364378109 298192080043654636641791)
                      ·
                        rfl

theorem cell23_580727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_580727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580727 prefixEnd_580727 := by exact prefixLift 580727
  have htrace : WordTrace (prefixWord ++ tailWord_580727) baseStart_580727 baseEnd_580727 := by
    simpa [prefixWord, tailWord_580727, baseEnd_580727] using wordTrace_append hprefix tailTrace_580727
  have hstable : (prefixWord ++ tailWord_580727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580727).length < 2 ^ (prefixWord ++ tailWord_580727).sum := by decide
  have hdescent : baseEnd_580727 < baseStart_580727 := by decide
  rcases family_descends (prefixWord ++ tailWord_580727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580764 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 6]
def baseStart_580764 : Nat := 118140960795 + 580764 * 2 ^ 59
def prefixEnd_580764 : Nat := 4983230072969 + 3 ^ 40 * 580764 * 2
def baseEnd_580764 : Nat := 33134564314207887986569

theorem tailTrace_580764 : CollatzResearch.WordTrace tailWord_580764 prefixEnd_580764 33134564314207887986569 := by
  unfold tailWord_580764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10591101633999344719830673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14121468845332459626440897 10591101633999344719830673)
  ·
    refine ⟨7943326225499508539873005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10591101633999344719830673 7943326225499508539873005)
    ·
      refine ⟨2978747334562315702452377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7943326225499508539873005 2978747334562315702452377)
      ·
        refine ⟨2234060500921736776839283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2978747334562315702452377 2234060500921736776839283)
        ·
          refine ⟨3351090751382605165258925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2234060500921736776839283 3351090751382605165258925)
          ·
            refine ⟨1256659031768476936972097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3351090751382605165258925 1256659031768476936972097)
            ·
              refine ⟨942494273826357702729073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256659031768476936972097 942494273826357702729073)
              ·
                refine ⟨706870705369768277046805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942494273826357702729073 706870705369768277046805)
                ·
                  refine ⟨33134564314207887986569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 706870705369768277046805 33134564314207887986569)
                  ·
                    rfl

theorem cell23_580764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_580764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580764 prefixEnd_580764 := by exact prefixLift 580764
  have htrace : WordTrace (prefixWord ++ tailWord_580764) baseStart_580764 baseEnd_580764 := by
    simpa [prefixWord, tailWord_580764, baseEnd_580764] using wordTrace_append hprefix tailTrace_580764
  have hstable : (prefixWord ++ tailWord_580764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580764).length < 2 ^ (prefixWord ++ tailWord_580764).sum := by decide
  have hdescent : baseEnd_580764 < baseStart_580764 := by decide
  rcases family_descends (prefixWord ++ tailWord_580764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580802 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_580802 : Nat := 118140960795 + 580802 * 2 ^ 59
def prefixEnd_580802 : Nat := 4983230072969 + 3 ^ 40 * 580802 * 2
def baseEnd_580802 : Nat := 99410197030913947734649

theorem tailTrace_580802 : CollatzResearch.WordTrace tailWord_580802 prefixEnd_580802 99410197030913947734649 := by
  unfold tailWord_580802
  simp only [CollatzResearch.WordTrace]
  refine ⟨5295897310465255482386165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14122392827907347953029773 5295897310465255482386165)
  ·
    refine ⟨496490372856117701473703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5295897310465255482386165 496490372856117701473703)
    ·
      refine ⟨744735559284176552210555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496490372856117701473703 744735559284176552210555)
      ·
        refine ⟨1117103338926264828315833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744735559284176552210555 1117103338926264828315833)
        ·
          refine ⟨837827504194698621236875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117103338926264828315833 837827504194698621236875)
          ·
            refine ⟨1256741256292047931855313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837827504194698621236875 1256741256292047931855313)
            ·
              refine ⟨942555942219035948891485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256741256292047931855313 942555942219035948891485)
              ·
                refine ⟨353458478332138480834307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942555942219035948891485 353458478332138480834307)
                ·
                  refine ⟨530187717498207721251461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353458478332138480834307 530187717498207721251461)
                  ·
                    refine ⟨99410197030913947734649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 530187717498207721251461 99410197030913947734649)
                    ·
                      rfl

theorem cell23_580802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_580802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580802 prefixEnd_580802 := by exact prefixLift 580802
  have htrace : WordTrace (prefixWord ++ tailWord_580802) baseStart_580802 baseEnd_580802 := by
    simpa [prefixWord, tailWord_580802, baseEnd_580802] using wordTrace_append hprefix tailTrace_580802
  have hstable : (prefixWord ++ tailWord_580802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580802).length < 2 ^ (prefixWord ++ tailWord_580802).sum := by decide
  have hdescent : baseEnd_580802 < baseStart_580802 := by decide
  rcases family_descends (prefixWord ++ tailWord_580802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580817 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_580817 : Nat := 118140960795 + 580817 * 2 ^ 59
def prefixEnd_580817 : Nat := 4983230072969 + 3 ^ 40 * 580817 * 2
def baseEnd_580817 : Nat := 298238293302559284516377

theorem tailTrace_580817 : CollatzResearch.WordTrace tailWord_580817 prefixEnd_580817 298238293302559284516377 := by
  unfold tailWord_580817
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184136336806679491340705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14122757557871119660893803 21184136336806679491340705)
  ·
    refine ⟨15888102252605009618505529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21184136336806679491340705 15888102252605009618505529)
    ·
      refine ⟨11916076689453757213879147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15888102252605009618505529 11916076689453757213879147)
      ·
        refine ⟨17874115034180635820818721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916076689453757213879147 17874115034180635820818721)
        ·
          refine ⟨13405586275635476865614041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17874115034180635820818721 13405586275635476865614041)
          ·
            refine ⟨10054189706726607649210531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13405586275635476865614041 10054189706726607649210531)
            ·
              refine ⟨15081284560089911473815797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10054189706726607649210531 15081284560089911473815797)
              ·
                refine ⟨1413870427508429200670231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15081284560089911473815797 1413870427508429200670231)
                ·
                  refine ⟨2120805641262643801005347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413870427508429200670231 2120805641262643801005347)
                  ·
                    refine ⟨3181208461893965701508021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2120805641262643801005347 3181208461893965701508021)
                    ·
                      refine ⟨298238293302559284516377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3181208461893965701508021 298238293302559284516377)
                      ·
                        rfl

theorem cell23_580817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_580817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580817 prefixEnd_580817 := by exact prefixLift 580817
  have htrace : WordTrace (prefixWord ++ tailWord_580817) baseStart_580817 baseEnd_580817 := by
    simpa [prefixWord, tailWord_580817, baseEnd_580817] using wordTrace_append hprefix tailTrace_580817
  have hstable : (prefixWord ++ tailWord_580817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580817).length < 2 ^ (prefixWord ++ tailWord_580817).sum := by decide
  have hdescent : baseEnd_580817 < baseStart_580817 := by decide
  rcases family_descends (prefixWord ++ tailWord_580817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580831 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 3, 2, 2]
def baseStart_580831 : Nat := 118140960795 + 580831 * 2 ^ 59
def prefixEnd_580831 : Nat := 4983230072969 + 3 ^ 40 * 580831 * 2
def baseEnd_580831 : Nat := 298245482031722229741313

theorem tailTrace_580831 : CollatzResearch.WordTrace tailWord_580831 prefixEnd_580831 298245482031722229741313 := by
  unfold tailWord_580831
  simp only [CollatzResearch.WordTrace]
  refine ⟨21184646958755959882350347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14123097972503973254900231 21184646958755959882350347)
  ·
    refine ⟨31776970438133939823525521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21184646958755959882350347 31776970438133939823525521)
    ·
      refine ⟨23832727828600454867644141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31776970438133939823525521 23832727828600454867644141)
      ·
        refine ⟨8937272935725170575366553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23832727828600454867644141 8937272935725170575366553)
        ·
          refine ⟨6702954701793877931524915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8937272935725170575366553 6702954701793877931524915)
          ·
            refine ⟨10054432052690816897287373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6702954701793877931524915 10054432052690816897287373)
            ·
              refine ⟨3770412019759056336482765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10054432052690816897287373 3770412019759056336482765)
              ·
                refine ⟨1413904507409646126181037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3770412019759056336482765 1413904507409646126181037)
                ·
                  refine ⟨530214190278617297317889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1413904507409646126181037 530214190278617297317889)
                  ·
                    refine ⟨397660642708962972988417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530214190278617297317889 397660642708962972988417)
                    ·
                      refine ⟨298245482031722229741313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397660642708962972988417 298245482031722229741313)
                      ·
                        rfl

theorem cell23_580831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_580831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580831 prefixEnd_580831 := by exact prefixLift 580831
  have htrace : WordTrace (prefixWord ++ tailWord_580831) baseStart_580831 baseEnd_580831 := by
    simpa [prefixWord, tailWord_580831, baseEnd_580831] using wordTrace_append hprefix tailTrace_580831
  have hstable : (prefixWord ++ tailWord_580831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580831).length < 2 ^ (prefixWord ++ tailWord_580831).sum := by decide
  have hdescent : baseEnd_580831 < baseStart_580831 := by decide
  rcases family_descends (prefixWord ++ tailWord_580831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580844 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_580844 : Nat := 118140960795 + 580844 * 2 ^ 59
def prefixEnd_580844 : Nat := 4983230072969 + 3 ^ 40 * 580844 * 2
def baseEnd_580844 : Nat := 298252157280230678878753

theorem tailTrace_580844 : CollatzResearch.WordTrace tailWord_580844 prefixEnd_580844 298252157280230678878753 := by
  unfold tailWord_580844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10592560553854431551286793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14123414071805908735049057 10592560553854431551286793)
  ·
    refine ⟨7944420415390823663465095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10592560553854431551286793 7944420415390823663465095)
    ·
      refine ⟨11916630623086235495197643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7944420415390823663465095 11916630623086235495197643)
      ·
        refine ⟨17874945934629353242796465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11916630623086235495197643 17874945934629353242796465)
        ·
          refine ⟨13406209450972014932097349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17874945934629353242796465 13406209450972014932097349)
          ·
            refine ⟨2513664272057252799768253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13406209450972014932097349 2513664272057252799768253)
            ·
              refine ⟨942624102021469799913095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513664272057252799768253 942624102021469799913095)
              ·
                refine ⟨1413936153032204699869643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 942624102021469799913095 1413936153032204699869643)
                ·
                  refine ⟨2120904229548307049804465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1413936153032204699869643 2120904229548307049804465)
                  ·
                    refine ⟨1590678172161230287353349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2120904229548307049804465 1590678172161230287353349)
                    ·
                      refine ⟨298252157280230678878753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1590678172161230287353349 298252157280230678878753)
                      ·
                        rfl

theorem cell23_580844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_580844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580844 prefixEnd_580844 := by exact prefixLift 580844
  have htrace : WordTrace (prefixWord ++ tailWord_580844) baseStart_580844 baseEnd_580844 := by
    simpa [prefixWord, tailWord_580844, baseEnd_580844] using wordTrace_append hprefix tailTrace_580844
  have hstable : (prefixWord ++ tailWord_580844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580844).length < 2 ^ (prefixWord ++ tailWord_580844).sum := by decide
  have hdescent : baseEnd_580844 < baseStart_580844 := by decide
  rcases family_descends (prefixWord ++ tailWord_580844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580851 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 3]
def baseStart_580851 : Nat := 118140960795 + 580851 * 2 ^ 59
def prefixEnd_580851 : Nat := 4983230072969 + 3 ^ 40 * 580851 * 2
def baseEnd_580851 : Nat := 298255751644812151491221

theorem tailTrace_580851 : CollatzResearch.WordTrace tailWord_580851 prefixEnd_580851 298255751644812151491221 := by
  unfold tailWord_580851
  simp only [CollatzResearch.WordTrace]
  refine ⟨21185376418683503298078407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14123584279122335532052271 21185376418683503298078407)
  ·
    refine ⟨31778064628025254947117611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21185376418683503298078407 31778064628025254947117611)
    ·
      refine ⟨47667096942037882420676417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31778064628025254947117611 47667096942037882420676417)
      ·
        refine ⟨35750322706528411815507313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47667096942037882420676417 35750322706528411815507313)
        ·
          refine ⟨26812742029896308861630485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35750322706528411815507313 26812742029896308861630485)
          ·
            refine ⟨1256847282651389477888929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26812742029896308861630485 1256847282651389477888929)
            ·
              refine ⟨942635461988542108416697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1256847282651389477888929 942635461988542108416697)
              ·
                refine ⟨706976596491406581312523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942635461988542108416697 706976596491406581312523)
                ·
                  refine ⟨1060464894737109871968785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706976596491406581312523 1060464894737109871968785)
                  ·
                    refine ⟨795348671052832403976589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1060464894737109871968785 795348671052832403976589)
                    ·
                      refine ⟨298255751644812151491221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795348671052832403976589 298255751644812151491221)
                      ·
                        rfl

theorem cell23_580851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_580851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580851 prefixEnd_580851 := by exact prefixLift 580851
  have htrace : WordTrace (prefixWord ++ tailWord_580851) baseStart_580851 baseEnd_580851 := by
    simpa [prefixWord, tailWord_580851, baseEnd_580851] using wordTrace_append hprefix tailTrace_580851
  have hstable : (prefixWord ++ tailWord_580851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580851).length < 2 ^ (prefixWord ++ tailWord_580851).sum := by decide
  have hdescent : baseEnd_580851 < baseStart_580851 := by decide
  rcases family_descends (prefixWord ++ tailWord_580851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580865 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_580865 : Nat := 118140960795 + 580865 * 2 ^ 59
def prefixEnd_580865 : Nat := 4983230072969 + 3 ^ 40 * 580865 * 2
def baseEnd_580865 : Nat := 298262940373975096716157

theorem tailTrace_580865 : CollatzResearch.WordTrace tailWord_580865 prefixEnd_580865 298262940373975096716157 := by
  unfold tailWord_580865
  simp only [CollatzResearch.WordTrace]
  refine ⟨21185887040632783689088049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14123924693755189126058699 21185887040632783689088049)
  ·
    refine ⟨15889415280474587766816037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21185887040632783689088049 15889415280474587766816037)
    ·
      refine ⟨2979265365088985206278007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15889415280474587766816037 2979265365088985206278007)
      ·
        refine ⟨4468898047633477809417011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2979265365088985206278007 4468898047633477809417011)
        ·
          refine ⟨6703347071450216714125517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4468898047633477809417011 6703347071450216714125517)
          ·
            refine ⟨2513755151793831267797069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6703347071450216714125517 2513755151793831267797069)
            ·
              refine ⟨942658181922686725423901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2513755151793831267797069 942658181922686725423901)
              ·
                refine ⟨353496818221007522033963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 942658181922686725423901 353496818221007522033963)
                ·
                  refine ⟨530245227331511283050945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353496818221007522033963 530245227331511283050945)
                  ·
                    refine ⟨397683920498633462288209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 530245227331511283050945 397683920498633462288209)
                    ·
                      refine ⟨298262940373975096716157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 397683920498633462288209 298262940373975096716157)
                      ·
                        rfl

theorem cell23_580865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_580865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580865 prefixEnd_580865 := by exact prefixLift 580865
  have htrace : WordTrace (prefixWord ++ tailWord_580865) baseStart_580865 baseEnd_580865 := by
    simpa [prefixWord, tailWord_580865, baseEnd_580865] using wordTrace_append hprefix tailTrace_580865
  have hstable : (prefixWord ++ tailWord_580865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580865).length < 2 ^ (prefixWord ++ tailWord_580865).sum := by decide
  have hdescent : baseEnd_580865 < baseStart_580865 := by decide
  rcases family_descends (prefixWord ++ tailWord_580865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580881 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_580881 : Nat := 118140960795 + 580881 * 2 ^ 59
def prefixEnd_580881 : Nat := 4983230072969 + 3 ^ 40 * 580881 * 2
def baseEnd_580881 : Nat := 298271156064447034116083

theorem tailTrace_580881 : CollatzResearch.WordTrace tailWord_580881 prefixEnd_580881 298271156064447034116083 := by
  unfold tailWord_580881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21186470608574818421670497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14124313739049878947780331 21186470608574818421670497)
  ·
    refine ⟨15889852956431113816252873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21186470608574818421670497 15889852956431113816252873)
    ·
      refine ⟨11917389717323335362189655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15889852956431113816252873 11917389717323335362189655)
      ·
        refine ⟨17876084575985003043284483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11917389717323335362189655 17876084575985003043284483)
        ·
          refine ⟨26814126863977504564926725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17876084575985003043284483 26814126863977504564926725)
          ·
            refine ⟨5027648786995782105923761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26814126863977504564926725 5027648786995782105923761)
            ·
              refine ⟨3770736590246836579442821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5027648786995782105923761 3770736590246836579442821)
              ·
                refine ⟨707013110671281858645529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3770736590246836579442821 707013110671281858645529)
                ·
                  refine ⟨530259833003461393984147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 707013110671281858645529 530259833003461393984147)
                  ·
                    refine ⟨795389749505192090976221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 530259833003461393984147 795389749505192090976221)
                    ·
                      refine ⟨298271156064447034116083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 795389749505192090976221 298271156064447034116083)
                      ·
                        rfl

theorem cell23_580881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_580881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580881 prefixEnd_580881 := by exact prefixLift 580881
  have htrace : WordTrace (prefixWord ++ tailWord_580881) baseStart_580881 baseEnd_580881 := by
    simpa [prefixWord, tailWord_580881, baseEnd_580881] using wordTrace_append hprefix tailTrace_580881
  have hstable : (prefixWord ++ tailWord_580881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580881).length < 2 ^ (prefixWord ++ tailWord_580881).sum := by decide
  have hdescent : baseEnd_580881 < baseStart_580881 := by decide
  rcases family_descends (prefixWord ++ tailWord_580881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_580897 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_580897 : Nat := 118140960795 + 580897 * 2 ^ 59
def prefixEnd_580897 : Nat := 4983230072969 + 3 ^ 40 * 580897 * 2
def baseEnd_580897 : Nat := 99426457251639657172003

theorem tailTrace_580897 : CollatzResearch.WordTrace tailWord_580897 prefixEnd_580897 99426457251639657172003 := by
  unfold tailWord_580897
  simp only [CollatzResearch.WordTrace]
  refine ⟨21187054176516853154252945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14124702784344568769501963 21187054176516853154252945)
  ·
    refine ⟨15890290632387639865689709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21187054176516853154252945 15890290632387639865689709)
    ·
      refine ⟨5958858987145364949633641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15890290632387639865689709 5958858987145364949633641)
      ·
        refine ⟨4469144240359023712225231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5958858987145364949633641 4469144240359023712225231)
        ·
          refine ⟨6703716360538535568337847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4469144240359023712225231 6703716360538535568337847)
          ·
            refine ⟨10055574540807803352506771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6703716360538535568337847 10055574540807803352506771)
            ·
              refine ⟨15083361811211705028760157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10055574540807803352506771 15083361811211705028760157)
              ·
                refine ⟨5656260679204389385785059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15083361811211705028760157 5656260679204389385785059)
                ·
                  refine ⟨8484391018806584078677589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5656260679204389385785059 8484391018806584078677589)
                  ·
                    refine ⟨99426457251639657172003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8484391018806584078677589 99426457251639657172003)
                    ·
                      rfl

theorem cell23_580897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_580897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_580897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_580897 prefixEnd_580897 := by exact prefixLift 580897
  have htrace : WordTrace (prefixWord ++ tailWord_580897) baseStart_580897 baseEnd_580897 := by
    simpa [prefixWord, tailWord_580897, baseEnd_580897] using wordTrace_append hprefix tailTrace_580897
  have hstable : (prefixWord ++ tailWord_580897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_580897).length < 2 ^ (prefixWord ++ tailWord_580897).sum := by decide
  have hdescent : baseEnd_580897 < baseStart_580897 := by decide
  rcases family_descends (prefixWord ++ tailWord_580897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
