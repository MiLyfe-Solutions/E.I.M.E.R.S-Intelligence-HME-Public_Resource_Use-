import V185TrunkScan22Chunk435

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3886981 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3886981 : Nat := 118140960795 + 3886981 * 2 ^ 59
def prefixEnd_3886981 : Nat := 4983230072969 + 3 ^ 40 * 3886981 * 2
def baseEnd_3886981 : Nat := 1330593031929307935107737

theorem tailTrace_3886981 : CollatzResearch.WordTrace tailWord_3886981 prefixEnd_3886981 1330593031929307935107737 := by
  unfold tailWord_3886981
  simp only [CollatzResearch.WordTrace]
  refine ⟨141769843931139155348628797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94513229287426103565752531 141769843931139155348628797)
  ·
    refine ⟨53163691474177183255735799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141769843931139155348628797 53163691474177183255735799)
    ·
      refine ⟨79745537211265774883603699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53163691474177183255735799 79745537211265774883603699)
      ·
        refine ⟨119618305816898662325405549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79745537211265774883603699 119618305816898662325405549)
        ·
          refine ⟨44856864681336998372027081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119618305816898662325405549 44856864681336998372027081)
          ·
            refine ⟨33642648511002748779020311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44856864681336998372027081 33642648511002748779020311)
            ·
              refine ⟨50463972766504123168530467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33642648511002748779020311 50463972766504123168530467)
              ·
                refine ⟨75695959149756184752795701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50463972766504123168530467 75695959149756184752795701)
                ·
                  refine ⟨7096496170289642320574597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75695959149756184752795701 7096496170289642320574597)
                  ·
                    refine ⟨1330593031929307935107737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096496170289642320574597 1330593031929307935107737)
                    ·
                      rfl

theorem cell22_3886981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3886981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886981 prefixEnd_3886981 := by exact prefixLift 3886981
  have htrace : WordTrace (prefixWord ++ tailWord_3886981) baseStart_3886981 baseEnd_3886981 := by
    simpa [prefixWord, tailWord_3886981, baseEnd_3886981] using wordTrace_append hprefix tailTrace_3886981
  have hstable : (prefixWord ++ tailWord_3886981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886981).length < 2 ^ (prefixWord ++ tailWord_3886981).sum := by decide
  have hdescent : baseEnd_3886981 < baseStart_3886981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3886983 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 2, 5]
def baseStart_3886983 : Nat := 118140960795 + 3886983 * 2 ^ 59
def prefixEnd_3886983 : Nat := 4983230072969 + 3 ^ 40 * 3886983 * 2
def baseEnd_3886983 : Nat := 1330593716570180596557731

theorem tailTrace_3886983 : CollatzResearch.WordTrace tailWord_3886983 prefixEnd_3886983 1330593716570180596557731 := by
  unfold tailWord_3886983
  simp only [CollatzResearch.WordTrace]
  refine ⟨141769916877131909690201603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94513277918087939793467735 141769916877131909690201603)
  ·
    refine ⟨212654875315697864535302405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141769916877131909690201603 212654875315697864535302405)
    ·
      refine ⟨39872789121693349600369201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212654875315697864535302405 39872789121693349600369201)
      ·
        refine ⟨29904591841270012200276901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39872789121693349600369201 29904591841270012200276901)
        ·
          refine ⟨5607110970238127287551919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29904591841270012200276901 5607110970238127287551919)
          ·
            refine ⟨8410666455357190931327879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607110970238127287551919 8410666455357190931327879)
            ·
              refine ⟨12615999683035786396991819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8410666455357190931327879 12615999683035786396991819)
              ·
                refine ⟨18923999524553679595487729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12615999683035786396991819 18923999524553679595487729)
                ·
                  refine ⟨14192999643415259696615797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18923999524553679595487729 14192999643415259696615797)
                  ·
                    refine ⟨1330593716570180596557731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14192999643415259696615797 1330593716570180596557731)
                    ·
                      rfl

theorem cell22_3886983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_3886983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3886983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3886983 prefixEnd_3886983 := by exact prefixLift 3886983
  have htrace : WordTrace (prefixWord ++ tailWord_3886983) baseStart_3886983 baseEnd_3886983 := by
    simpa [prefixWord, tailWord_3886983, baseEnd_3886983] using wordTrace_append hprefix tailTrace_3886983
  have hstable : (prefixWord ++ tailWord_3886983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3886983).length < 2 ^ (prefixWord ++ tailWord_3886983).sum := by decide
  have hdescent : baseEnd_3886983 < baseStart_3886983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3886983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887006 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3887006 : Nat := 118140960795 + 3887006 * 2 ^ 59
def prefixEnd_3887006 : Nat := 4983230072969 + 3 ^ 40 * 3887006 * 2
def baseEnd_3887006 : Nat := 1330601589940216203232661

theorem tailTrace_3887006 : CollatzResearch.WordTrace tailWord_3887006 prefixEnd_3887006 1330601589940216203232661 := by
  unfold tailWord_3887006
  simp only [CollatzResearch.WordTrace]
  refine ⟨17721344469506073077286109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94513837170699056412192581 17721344469506073077286109)
  ·
    refine ⟨6645504176064777403982291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17721344469506073077286109 6645504176064777403982291)
    ·
      refine ⟨9968256264097166105973437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6645504176064777403982291 9968256264097166105973437)
      ·
        refine ⟨3738096099036437289740039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9968256264097166105973437 3738096099036437289740039)
        ·
          refine ⟨5607144148554655934610059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738096099036437289740039 5607144148554655934610059)
          ·
            refine ⟨8410716222831983901915089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5607144148554655934610059 8410716222831983901915089)
            ·
              refine ⟨6308037167123987926436317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8410716222831983901915089 6308037167123987926436317)
              ·
                refine ⟨2365513937671495472413619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6308037167123987926436317 2365513937671495472413619)
                ·
                  refine ⟨3548270906507243208620429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2365513937671495472413619 3548270906507243208620429)
                  ·
                    refine ⟨1330601589940216203232661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548270906507243208620429 1330601589940216203232661)
                    ·
                      rfl

theorem cell22_3887006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3887006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887006 prefixEnd_3887006 := by exact prefixLift 3887006
  have htrace : WordTrace (prefixWord ++ tailWord_3887006) baseStart_3887006 baseEnd_3887006 := by
    simpa [prefixWord, tailWord_3887006, baseEnd_3887006] using wordTrace_append hprefix tailTrace_3887006
  have hstable : (prefixWord ++ tailWord_3887006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887006).length < 2 ^ (prefixWord ++ tailWord_3887006).sum := by decide
  have hdescent : baseEnd_3887006 < baseStart_3887006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887015 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3887015 : Nat := 118140960795 + 3887015 * 2 ^ 59
def prefixEnd_3887015 : Nat := 4983230072969 + 3 ^ 40 * 3887015 * 2
def baseEnd_3887015 : Nat := 1330604670824143179757633

theorem tailTrace_3887015 : CollatzResearch.WordTrace tailWord_3887015 prefixEnd_3887015 1330604670824143179757633 := by
  unfold tailWord_3887015
  simp only [CollatzResearch.WordTrace]
  refine ⟨141771084013015979155366499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94514056008677319436910999 141771084013015979155366499)
  ·
    refine ⟨212656626019523968733049749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141771084013015979155366499 212656626019523968733049749)
    ·
      refine ⟨9968279344665186034361707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212656626019523968733049749 9968279344665186034361707)
      ·
        refine ⟨14952419016997779051542561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968279344665186034361707 14952419016997779051542561)
        ·
          refine ⟨11214314262748334288656921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14952419016997779051542561 11214314262748334288656921)
          ·
            refine ⟨8410735697061250716492691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11214314262748334288656921 8410735697061250716492691)
            ·
              refine ⟨12616103545591876074739037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8410735697061250716492691 12616103545591876074739037)
              ·
                refine ⟨4731038829596953528027139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12616103545591876074739037 4731038829596953528027139)
                ·
                  refine ⟨7096558244395430292040709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731038829596953528027139 7096558244395430292040709)
                  ·
                    refine ⟨1330604670824143179757633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096558244395430292040709 1330604670824143179757633)
                    ·
                      rfl

theorem cell22_3887015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3887015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887015 prefixEnd_3887015 := by exact prefixLift 3887015
  have htrace : WordTrace (prefixWord ++ tailWord_3887015) baseStart_3887015 baseEnd_3887015 := by
    simpa [prefixWord, tailWord_3887015, baseEnd_3887015] using wordTrace_append hprefix tailTrace_3887015
  have hstable : (prefixWord ++ tailWord_3887015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887015).length < 2 ^ (prefixWord ++ tailWord_3887015).sum := by decide
  have hdescent : baseEnd_3887015 < baseStart_3887015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887073 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3887073 : Nat := 118140960795 + 3887073 * 2 ^ 59
def prefixEnd_3887073 : Nat := 4983230072969 + 3 ^ 40 * 3887073 * 2
def baseEnd_3887073 : Nat := 1330624525409450361807455

theorem tailTrace_3887073 : CollatzResearch.WordTrace tailWord_3887073 prefixEnd_3887073 1330624525409450361807455 := by
  unfold tailWord_3887073
  simp only [CollatzResearch.WordTrace]
  refine ⟨141773199446805855060977873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94515466297870570040651915 141773199446805855060977873)
  ·
    refine ⟨106329899585104391295733405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141773199446805855060977873 106329899585104391295733405)
    ·
      refine ⟨39873712344414146735900027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106329899585104391295733405 39873712344414146735900027)
      ·
        refine ⟨59810568516621220103850041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39873712344414146735900027 59810568516621220103850041)
        ·
          refine ⟨44857926387465915077887531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59810568516621220103850041 44857926387465915077887531)
          ·
            refine ⟨67286889581198872616831297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44857926387465915077887531 67286889581198872616831297)
            ·
              refine ⟨50465167185899154462623473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67286889581198872616831297 50465167185899154462623473)
              ·
                refine ⟨37848875389424365846967605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50465167185899154462623473 37848875389424365846967605)
                ·
                  refine ⟨3548332067758534298153213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37848875389424365846967605 3548332067758534298153213)
                  ·
                    refine ⟨1330624525409450361807455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548332067758534298153213 1330624525409450361807455)
                    ·
                      rfl

theorem cell22_3887073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3887073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887073 prefixEnd_3887073 := by exact prefixLift 3887073
  have htrace : WordTrace (prefixWord ++ tailWord_3887073) baseStart_3887073 baseEnd_3887073 := by
    simpa [prefixWord, tailWord_3887073, baseEnd_3887073] using wordTrace_append hprefix tailTrace_3887073
  have hstable : (prefixWord ++ tailWord_3887073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887073).length < 2 ^ (prefixWord ++ tailWord_3887073).sum := by decide
  have hdescent : baseEnd_3887073 < baseStart_3887073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887131 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 10]
def baseStart_3887131 : Nat := 118140960795 + 3887131 * 2 ^ 59
def prefixEnd_3887131 : Nat := 4983230072969 + 3 ^ 40 * 3887131 * 2
def baseEnd_3887131 : Nat := 443548126664919181285759

theorem tailTrace_3887131 : CollatzResearch.WordTrace tailWord_3887131 prefixEnd_3887131 443548126664919181285759 := by
  unfold tailWord_3887131
  simp only [CollatzResearch.WordTrace]
  refine ⟨141775314880595730966589247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94516876587063820644392831 141775314880595730966589247)
  ·
    refine ⟨212662972320893596449883871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141775314880595730966589247 212662972320893596449883871)
    ·
      refine ⟨318994458481340394674825807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212662972320893596449883871 318994458481340394674825807)
      ·
        refine ⟨478491687722010592012238711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318994458481340394674825807 478491687722010592012238711)
        ·
          refine ⟨717737531583015888018358067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478491687722010592012238711 717737531583015888018358067)
          ·
            refine ⟨1076606297374523832027537101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717737531583015888018358067 1076606297374523832027537101)
            ·
              refine ⟨403727361515446437010326413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076606297374523832027537101 403727361515446437010326413)
              ·
                refine ⟨151397760568292413878872405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 403727361515446437010326413 151397760568292413878872405)
                ·
                  refine ⟨443548126664919181285759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 151397760568292413878872405 443548126664919181285759)
                  ·
                    rfl

theorem cell22_3887131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_3887131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887131 prefixEnd_3887131 := by exact prefixLift 3887131
  have htrace : WordTrace (prefixWord ++ tailWord_3887131) baseStart_3887131 baseEnd_3887131 := by
    simpa [prefixWord, tailWord_3887131, baseEnd_3887131] using wordTrace_append hprefix tailTrace_3887131
  have hstable : (prefixWord ++ tailWord_3887131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887131).length < 2 ^ (prefixWord ++ tailWord_3887131).sum := by decide
  have hdescent : baseEnd_3887131 < baseStart_3887131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887150 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3887150 : Nat := 118140960795 + 3887150 * 2 ^ 59
def prefixEnd_3887150 : Nat := 4983230072969 + 3 ^ 40 * 3887150 * 2
def baseEnd_3887150 : Nat := 1330650884083047827632219

theorem tailTrace_3887150 : CollatzResearch.WordTrace tailWord_3887150 prefixEnd_3887150 1330650884083047827632219 := by
  unfold tailWord_3887150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722000983440862151441363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94517338578351264807687269 17722000983440862151441363)
  ·
    refine ⟨26583001475161293227162045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17722000983440862151441363 26583001475161293227162045)
    ·
      refine ⟨9968625553185484960185767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26583001475161293227162045 9968625553185484960185767)
      ·
        refine ⟨14952938329778227440278651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9968625553185484960185767 14952938329778227440278651)
        ·
          refine ⟨22429407494667341160417977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14952938329778227440278651 22429407494667341160417977)
          ·
            refine ⟨16822055621000505870313483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22429407494667341160417977 16822055621000505870313483)
            ·
              refine ⟨25233083431500758805470225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16822055621000505870313483 25233083431500758805470225)
              ·
                refine ⟨18924812573625569104102669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25233083431500758805470225 18924812573625569104102669)
                ·
                  refine ⟨7096804715109588414038501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18924812573625569104102669 7096804715109588414038501)
                  ·
                    refine ⟨1330650884083047827632219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7096804715109588414038501 1330650884083047827632219)
                    ·
                      rfl

theorem cell22_3887150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3887150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887150 prefixEnd_3887150 := by exact prefixLift 3887150
  have htrace : WordTrace (prefixWord ++ tailWord_3887150) baseStart_3887150 baseEnd_3887150 := by
    simpa [prefixWord, tailWord_3887150, baseEnd_3887150] using wordTrace_append hprefix tailTrace_3887150
  have hstable : (prefixWord ++ tailWord_3887150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887150).length < 2 ^ (prefixWord ++ tailWord_3887150).sum := by decide
  have hdescent : baseEnd_3887150 < baseStart_3887150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887182 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3887182 : Nat := 118140960795 + 3887182 * 2 ^ 59
def prefixEnd_3887182 : Nat := 4983230072969 + 3 ^ 40 * 3887182 * 2
def baseEnd_3887182 : Nat := 443553946112336803610707

theorem tailTrace_3887182 : CollatzResearch.WordTrace tailWord_3887182 prefixEnd_3887182 443553946112336803610707 := by
  unfold tailWord_3887182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722146875426370834586975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94518116668940644451130533 17722146875426370834586975)
  ·
    refine ⟨26583220313139556251880463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17722146875426370834586975 26583220313139556251880463)
    ·
      refine ⟨39874830469709334377820695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26583220313139556251880463 39874830469709334377820695)
      ·
        refine ⟨59812245704564001566731043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39874830469709334377820695 59812245704564001566731043)
        ·
          refine ⟨89718368556846002350096565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59812245704564001566731043 89718368556846002350096565)
          ·
            refine ⟨8411097052204312720321553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89718368556846002350096565 8411097052204312720321553)
            ·
              refine ⟨6308322789153234540241165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8411097052204312720321553 6308322789153234540241165)
              ·
                refine ⟨2365621045932462952590437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6308322789153234540241165 2365621045932462952590437)
                ·
                  refine ⟨443553946112336803610707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365621045932462952590437 443553946112336803610707)
                  ·
                    rfl

theorem cell22_3887182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3887182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887182 prefixEnd_3887182 := by exact prefixLift 3887182
  have htrace : WordTrace (prefixWord ++ tailWord_3887182) baseStart_3887182 baseEnd_3887182 := by
    simpa [prefixWord, tailWord_3887182, baseEnd_3887182] using wordTrace_append hprefix tailTrace_3887182
  have hstable : (prefixWord ++ tailWord_3887182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887182).length < 2 ^ (prefixWord ++ tailWord_3887182).sum := by decide
  have hdescent : baseEnd_3887182 < baseStart_3887182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887214 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_3887214 : Nat := 118140960795 + 3887214 * 2 ^ 59
def prefixEnd_3887214 : Nat := 4983230072969 + 3 ^ 40 * 3887214 * 2
def baseEnd_3887214 : Nat := 1330672792590972994032023

theorem tailTrace_3887214 : CollatzResearch.WordTrace tailWord_3887214 prefixEnd_3887214 1330672792590972994032023 := by
  unfold tailWord_3887214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17722292767411879517732587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94518894759530024094573797 17722292767411879517732587)
  ·
    refine ⟨26583439151117819276598881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17722292767411879517732587 26583439151117819276598881)
    ·
      refine ⟨19937579363338364457449161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26583439151117819276598881 19937579363338364457449161)
      ·
        refine ⟨14953184522503773343086871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19937579363338364457449161 14953184522503773343086871)
        ·
          refine ⟨22429776783755660014630307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14953184522503773343086871 22429776783755660014630307)
          ·
            refine ⟨33644665175633490021945461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22429776783755660014630307 33644665175633490021945461)
            ·
              refine ⟨3154187360215639689557387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33644665175633490021945461 3154187360215639689557387)
              ·
                refine ⟨4731281040323459534336081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154187360215639689557387 4731281040323459534336081)
                ·
                  refine ⟨3548460780242594650752061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4731281040323459534336081 3548460780242594650752061)
                  ·
                    refine ⟨1330672792590972994032023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548460780242594650752061 1330672792590972994032023)
                    ·
                      rfl

theorem cell22_3887214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_3887214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887214 prefixEnd_3887214 := by exact prefixLift 3887214
  have htrace : WordTrace (prefixWord ++ tailWord_3887214) baseStart_3887214 baseEnd_3887214 := by
    simpa [prefixWord, tailWord_3887214, baseEnd_3887214] using wordTrace_append hprefix tailTrace_3887214
  have hstable : (prefixWord ++ tailWord_3887214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887214).length < 2 ^ (prefixWord ++ tailWord_3887214).sum := by decide
  have hdescent : baseEnd_3887214 < baseStart_3887214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887283 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 8]
def baseStart_3887283 : Nat := 118140960795 + 3887283 * 2 ^ 59
def prefixEnd_3887283 : Nat := 4983230072969 + 3 ^ 40 * 3887283 * 2
def baseEnd_3887283 : Nat := 443565470900359938018937

theorem tailTrace_3887283 : CollatzResearch.WordTrace tailWord_3887283 prefixEnd_3887283 443565470900359938018937 := by
  unfold tailWord_3887283
  simp only [CollatzResearch.WordTrace]
  refine ⟨141780858776045060926122503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94520572517363373950748335 141780858776045060926122503)
  ·
    refine ⟨212671288164067591389183755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141780858776045060926122503 212671288164067591389183755)
    ·
      refine ⟨319006932246101387083775633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212671288164067591389183755 319006932246101387083775633)
      ·
        refine ⟨239255199184576040312831725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319006932246101387083775633 239255199184576040312831725)
        ·
          refine ⟨89720699694216015117311897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239255199184576040312831725 89720699694216015117311897)
          ·
            refine ⟨67290524770662011337983923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89720699694216015117311897 67290524770662011337983923)
            ·
              refine ⟨100935787155993017006975885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67290524770662011337983923 100935787155993017006975885)
              ·
                refine ⟨37850920183497381377615957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100935787155993017006975885 37850920183497381377615957)
                ·
                  refine ⟨443565470900359938018937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37850920183497381377615957 443565470900359938018937)
                  ·
                    rfl

theorem cell22_3887283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_3887283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887283 prefixEnd_3887283 := by exact prefixLift 3887283
  have htrace : WordTrace (prefixWord ++ tailWord_3887283) baseStart_3887283 baseEnd_3887283 := by
    simpa [prefixWord, tailWord_3887283, baseEnd_3887283] using wordTrace_append hprefix tailTrace_3887283
  have hstable : (prefixWord ++ tailWord_3887283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887283).length < 2 ^ (prefixWord ++ tailWord_3887283).sum := by decide
  have hdescent : baseEnd_3887283 < baseStart_3887283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887362 : List Nat := [3, 4, 1, 1, 2, 2, 9]
def baseStart_3887362 : Nat := 118140960795 + 3887362 * 2 ^ 59
def prefixEnd_3887362 : Nat := 4983230072969 + 3 ^ 40 * 3887362 * 2
def baseEnd_3887362 : Nat := 49286053926501849678947

theorem tailTrace_3887362 : CollatzResearch.WordTrace tailWord_3887362 prefixEnd_3887362 49286053926501849678947 := by
  unfold tailWord_3887362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35445935035689714354562085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94522493428505904945498893 35445935035689714354562085)
  ·
    refine ⟨6646112819191821441480391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35445935035689714354562085 6646112819191821441480391)
    ·
      refine ⟨9969169228787732162220587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6646112819191821441480391 9969169228787732162220587)
      ·
        refine ⟨14953753843181598243330881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969169228787732162220587 14953753843181598243330881)
        ·
          refine ⟨11215315382386198682498161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14953753843181598243330881 11215315382386198682498161)
          ·
            refine ⟨8411486536789649011873621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11215315382386198682498161 8411486536789649011873621)
            ·
              refine ⟨49286053926501849678947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8411486536789649011873621 49286053926501849678947)
              ·
                rfl

theorem cell22_3887362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 9].length) (baseStart_3887362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887362 prefixEnd_3887362 := by exact prefixLift 3887362
  have htrace : WordTrace (prefixWord ++ tailWord_3887362) baseStart_3887362 baseEnd_3887362 := by
    simpa [prefixWord, tailWord_3887362, baseEnd_3887362] using wordTrace_append hprefix tailTrace_3887362
  have hstable : (prefixWord ++ tailWord_3887362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887362).length < 2 ^ (prefixWord ++ tailWord_3887362).sum := by decide
  have hdescent : baseEnd_3887362 < baseStart_3887362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887377 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_3887377 : Nat := 118140960795 + 3887377 * 2 ^ 59
def prefixEnd_3887377 : Nat := 4983230072969 + 3 ^ 40 * 3887377 * 2
def baseEnd_3887377 : Nat := 1330728590822094902206523

theorem tailTrace_3887377 : CollatzResearch.WordTrace tailWord_3887377 prefixEnd_3887377 1330728590822094902206523 := by
  unfold tailWord_3887377
  simp only [CollatzResearch.WordTrace]
  refine ⟨141784287237704514980044385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94522858158469676653362923 141784287237704514980044385)
  ·
    refine ⟨106338215428278386235033289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141784287237704514980044385 106338215428278386235033289)
    ·
      refine ⟨79753661571208789676274967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106338215428278386235033289 79753661571208789676274967)
      ·
        refine ⟨119630492356813184514412451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79753661571208789676274967 119630492356813184514412451)
        ·
          refine ⟨179445738535219776771618677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119630492356813184514412451 179445738535219776771618677)
          ·
            refine ⟨16823037987676854072339251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179445738535219776771618677 16823037987676854072339251)
            ·
              refine ⟨25234556981515281108508877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16823037987676854072339251 25234556981515281108508877)
              ·
                refine ⟨9462958868068230415690829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25234556981515281108508877 9462958868068230415690829)
                ·
                  refine ⟨3548609575525586405884061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9462958868068230415690829 3548609575525586405884061)
                  ·
                    refine ⟨1330728590822094902206523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548609575525586405884061 1330728590822094902206523)
                    ·
                      rfl

theorem cell22_3887377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_3887377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887377 prefixEnd_3887377 := by exact prefixLift 3887377
  have htrace : WordTrace (prefixWord ++ tailWord_3887377) baseStart_3887377 baseEnd_3887377 := by
    simpa [prefixWord, tailWord_3887377, baseEnd_3887377] using wordTrace_append hprefix tailTrace_3887377
  have hstable : (prefixWord ++ tailWord_3887377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887377).length < 2 ^ (prefixWord ++ tailWord_3887377).sum := by decide
  have hdescent : baseEnd_3887377 < baseStart_3887377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887394 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3887394 : Nat := 118140960795 + 3887394 * 2 ^ 59
def prefixEnd_3887394 : Nat := 4983230072969 + 3 ^ 40 * 3887394 * 2
def baseEnd_3887394 : Nat := 1330734410269512524531471

theorem tailTrace_3887394 : CollatzResearch.WordTrace tailWord_3887394 prefixEnd_3887394 1330734410269512524531471 := by
  unfold tailWord_3887394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35446226819660731720853309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94523271519095284588942157 35446226819660731720853309)
  ·
    refine ⟨13292335057372774395319991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35446226819660731720853309 13292335057372774395319991)
    ·
      refine ⟨19938502586059161592979987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13292335057372774395319991 19938502586059161592979987)
      ·
        refine ⟨29907753879088742389469981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19938502586059161592979987 29907753879088742389469981)
        ·
          refine ⟨11215407704658278396051243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29907753879088742389469981 11215407704658278396051243)
          ·
            refine ⟨16823111556987417594076865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215407704658278396051243 16823111556987417594076865)
            ·
              refine ⟨12617333667740563195557649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16823111556987417594076865 12617333667740563195557649)
              ·
                refine ⟨9463000250805422396668237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12617333667740563195557649 9463000250805422396668237)
                ·
                  refine ⟨3548625094052033398750589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9463000250805422396668237 3548625094052033398750589)
                  ·
                    refine ⟨1330734410269512524531471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548625094052033398750589 1330734410269512524531471)
                    ·
                      rfl

theorem cell22_3887394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3887394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887394 prefixEnd_3887394 := by exact prefixLift 3887394
  have htrace : WordTrace (prefixWord ++ tailWord_3887394) baseStart_3887394 baseEnd_3887394 := by
    simpa [prefixWord, tailWord_3887394, baseEnd_3887394] using wordTrace_append hprefix tailTrace_3887394
  have hstable : (prefixWord ++ tailWord_3887394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887394).length < 2 ^ (prefixWord ++ tailWord_3887394).sum := by decide
  have hdescent : baseEnd_3887394 < baseStart_3887394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887428 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3887428 : Nat := 118140960795 + 3887428 * 2 ^ 59
def prefixEnd_3887428 : Nat := 4983230072969 + 3 ^ 40 * 3887428 * 2
def baseEnd_3887428 : Nat := 1330746049164347769181367

theorem tailTrace_3887428 : CollatzResearch.WordTrace tailWord_3887428 prefixEnd_3887428 1330746049164347769181367 := by
  unfold tailWord_3887428
  simp only [CollatzResearch.WordTrace]
  refine ⟨70893073680259875345075469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94524098240346500460100625 70893073680259875345075469)
  ·
    refine ⟨26584902630097453254403301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70893073680259875345075469 26584902630097453254403301)
    ·
      refine ⟨4984669243143272485200619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26584902630097453254403301 4984669243143272485200619)
      ·
        refine ⟨7477003864714908727800929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984669243143272485200619 7477003864714908727800929)
        ·
          refine ⟨5607752898536181545850697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7477003864714908727800929 5607752898536181545850697)
          ·
            refine ⟨4205814673902136159388023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5607752898536181545850697 4205814673902136159388023)
            ·
              refine ⟨6308722010853204239082035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4205814673902136159388023 6308722010853204239082035)
              ·
                refine ⟨9463083016279806358623053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6308722010853204239082035 9463083016279806358623053)
                ·
                  refine ⟨3548656131104927384483645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9463083016279806358623053 3548656131104927384483645)
                  ·
                    refine ⟨1330746049164347769181367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548656131104927384483645 1330746049164347769181367)
                    ·
                      rfl

theorem cell22_3887428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3887428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887428 prefixEnd_3887428 := by exact prefixLift 3887428
  have htrace : WordTrace (prefixWord ++ tailWord_3887428) baseStart_3887428 baseEnd_3887428 := by
    simpa [prefixWord, tailWord_3887428, baseEnd_3887428] using wordTrace_append hprefix tailTrace_3887428
  have hstable : (prefixWord ++ tailWord_3887428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887428).length < 2 ^ (prefixWord ++ tailWord_3887428).sum := by decide
  have hdescent : baseEnd_3887428 < baseStart_3887428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887435 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 6]
def baseStart_3887435 : Nat := 118140960795 + 3887435 * 2 ^ 59
def prefixEnd_3887435 : Nat := 4983230072969 + 3 ^ 40 * 3887435 * 2
def baseEnd_3887435 : Nat := 443582815135800694752115

theorem tailTrace_3887435 : CollatzResearch.WordTrace tailWord_3887435 prefixEnd_3887435 443582815135800694752115 := by
  unfold tailWord_3887435
  simp only [CollatzResearch.WordTrace]
  refine ⟨141786402671494390885655759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94524268447662927257103839 141786402671494390885655759)
  ·
    refine ⟨212679604007241586328483639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141786402671494390885655759 212679604007241586328483639)
    ·
      refine ⟨319019406010862379492725459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212679604007241586328483639 319019406010862379492725459)
      ·
        refine ⟨478529109016293569239088189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319019406010862379492725459 478529109016293569239088189)
        ·
          refine ⟨179448415881110088464658071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478529109016293569239088189 179448415881110088464658071)
          ·
            refine ⟨269172623821665132696987107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179448415881110088464658071 269172623821665132696987107)
            ·
              refine ⟨403758935732497699045480661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269172623821665132696987107 403758935732497699045480661)
              ·
                refine ⟨9463100056230414821378453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 403758935732497699045480661 9463100056230414821378453)
                ·
                  refine ⟨443582815135800694752115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9463100056230414821378453 443582815135800694752115)
                  ·
                    rfl

theorem cell22_3887435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_3887435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887435 prefixEnd_3887435 := by exact prefixLift 3887435
  have htrace : WordTrace (prefixWord ++ tailWord_3887435) baseStart_3887435 baseEnd_3887435 := by
    simpa [prefixWord, tailWord_3887435, baseEnd_3887435] using wordTrace_append hprefix tailTrace_3887435
  have hstable : (prefixWord ++ tailWord_3887435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887435).length < 2 ^ (prefixWord ++ tailWord_3887435).sum := by decide
  have hdescent : baseEnd_3887435 < baseStart_3887435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887469 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3887469 : Nat := 118140960795 + 3887469 * 2 ^ 59
def prefixEnd_3887469 : Nat := 4983230072969 + 3 ^ 40 * 3887469 * 2
def baseEnd_3887469 : Nat := 443586694767412442968747

theorem tailTrace_3887469 : CollatzResearch.WordTrace tailWord_3887469 prefixEnd_3887469 443586694767412442968747 := by
  unfold tailWord_3887469
  simp only [CollatzResearch.WordTrace]
  refine ⟨141787642753371214692393461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94525095168914143128262307 141787642753371214692393461)
  ·
    refine ⟨13292591508128551377411887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141787642753371214692393461 13292591508128551377411887)
    ·
      refine ⟨19938887262192827066117831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13292591508128551377411887 19938887262192827066117831)
      ·
        refine ⟨29908330893289240599176747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19938887262192827066117831 29908330893289240599176747)
        ·
          refine ⟨44862496339933860898765121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29908330893289240599176747 44862496339933860898765121)
          ·
            refine ⟨33646872254950395674073841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44862496339933860898765121 33646872254950395674073841)
            ·
              refine ⟨25235154191212796755555381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33646872254950395674073841 25235154191212796755555381)
              ·
                refine ⟨2365795705426199695833317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25235154191212796755555381 2365795705426199695833317)
                ·
                  refine ⟨443586694767412442968747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365795705426199695833317 443586694767412442968747)
                  ·
                    rfl

theorem cell22_3887469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3887469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887469 prefixEnd_3887469 := by exact prefixLift 3887469
  have htrace : WordTrace (prefixWord ++ tailWord_3887469) baseStart_3887469 baseEnd_3887469 := by
    simpa [prefixWord, tailWord_3887469, baseEnd_3887469] using wordTrace_append hprefix tailTrace_3887469
  have hstable : (prefixWord ++ tailWord_3887469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887469).length < 2 ^ (prefixWord ++ tailWord_3887469).sum := by decide
  have hdescent : baseEnd_3887469 < baseStart_3887469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887497 : List Nat := [1, 2, 1, 1, 6, 1, 3, 7]
def baseStart_3887497 : Nat := 118140960795 + 3887497 * 2 ^ 59
def prefixEnd_3887497 : Nat := 4983230072969 + 3 ^ 40 * 3887497 * 2
def baseEnd_3887497 : Nat := 147863296586050509911795

theorem tailTrace_3887497 : CollatzResearch.WordTrace tailWord_3887497 prefixEnd_3887497 147863296586050509911795 := by
  unfold tailWord_3887497
  simp only [CollatzResearch.WordTrace]
  refine ⟨141788663997269775474412745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94525775998179850316275163 141788663997269775474412745)
  ·
    refine ⟨106341497997952331605809559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141788663997269775474412745 106341497997952331605809559)
    ·
      refine ⟨159512246996928497408714339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106341497997952331605809559 159512246996928497408714339)
      ·
        refine ⟨239268370495392746113071509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159512246996928497408714339 239268370495392746113071509)
        ·
          refine ⟨11215704866971534974050227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239268370495392746113071509 11215704866971534974050227)
          ·
            refine ⟨16823557300457302461075341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11215704866971534974050227 16823557300457302461075341)
            ·
              refine ⟨6308833987671488422903253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16823557300457302461075341 6308833987671488422903253)
              ·
                refine ⟨147863296586050509911795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6308833987671488422903253 147863296586050509911795)
                ·
                  rfl

theorem cell22_3887497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 7].length) (baseStart_3887497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887497 prefixEnd_3887497 := by exact prefixLift 3887497
  have htrace : WordTrace (prefixWord ++ tailWord_3887497) baseStart_3887497 baseEnd_3887497 := by
    simpa [prefixWord, tailWord_3887497, baseEnd_3887497] using wordTrace_append hprefix tailTrace_3887497
  have hstable : (prefixWord ++ tailWord_3887497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887497).length < 2 ^ (prefixWord ++ tailWord_3887497).sum := by decide
  have hdescent : baseEnd_3887497 < baseStart_3887497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887514 : List Nat := [3, 1, 1, 4, 1, 3, 3, 6]
def baseStart_3887514 : Nat := 118140960795 + 3887514 * 2 ^ 59
def prefixEnd_3887514 : Nat := 4983230072969 + 3 ^ 40 * 3887514 * 2
def baseEnd_3887514 : Nat := 147863943191319134614567

theorem tailTrace_3887514 : CollatzResearch.WordTrace tailWord_3887514 prefixEnd_3887514 147863943191319134614567 := by
  unfold tailWord_3887514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35447321009552046844445399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94526189358805458251854397 35447321009552046844445399)
  ·
    refine ⟨53170981514328070266668099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35447321009552046844445399 53170981514328070266668099)
    ·
      refine ⟨79756472271492105400002149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53170981514328070266668099 79756472271492105400002149)
      ·
        refine ⟨14954338550904769762500403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79756472271492105400002149 14954338550904769762500403)
        ·
          refine ⟨22431507826357154643750605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954338550904769762500403 22431507826357154643750605)
          ·
            refine ⟨8411815434883932991406477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22431507826357154643750605 8411815434883932991406477)
            ·
              refine ⟨3154430788081474871777429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8411815434883932991406477 3154430788081474871777429)
              ·
                refine ⟨147863943191319134614567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3154430788081474871777429 147863943191319134614567)
                ·
                  rfl

theorem cell22_3887514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_3887514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887514 prefixEnd_3887514 := by exact prefixLift 3887514
  have htrace : WordTrace (prefixWord ++ tailWord_3887514) baseStart_3887514 baseEnd_3887514 := by
    simpa [prefixWord, tailWord_3887514, baseEnd_3887514] using wordTrace_append hprefix tailTrace_3887514
  have hstable : (prefixWord ++ tailWord_3887514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887514).length < 2 ^ (prefixWord ++ tailWord_3887514).sum := by decide
  have hdescent : baseEnd_3887514 < baseStart_3887514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887623 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3887623 : Nat := 118140960795 + 3887623 * 2 ^ 59
def prefixEnd_3887623 : Nat := 4983230072969 + 3 ^ 40 * 3887623 * 2
def baseEnd_3887623 : Nat := 1330812801649432260555769

theorem tailTrace_3887623 : CollatzResearch.WordTrace tailWord_3887623 prefixEnd_3887623 1330812801649432260555769 := by
  unfold tailWord_3887623
  simp only [CollatzResearch.WordTrace]
  refine ⟨141793259594813298993499523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94528839729875532662333015 141793259594813298993499523)
  ·
    refine ⟨212689889392219948490249285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141793259594813298993499523 212689889392219948490249285)
    ·
      refine ⟨39879354261041240341921741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212689889392219948490249285 39879354261041240341921741)
      ·
        refine ⟨14954757847890465128220653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39879354261041240341921741 14954757847890465128220653)
        ·
          refine ⟨5608034192958924423082745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14954757847890465128220653 5608034192958924423082745)
          ·
            refine ⟨4206025644719193317312059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5608034192958924423082745 4206025644719193317312059)
            ·
              refine ⟨6309038467078789975968089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206025644719193317312059 6309038467078789975968089)
              ·
                refine ⟨4731778850309092481976067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6309038467078789975968089 4731778850309092481976067)
                ·
                  refine ⟨7097668275463638722964101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4731778850309092481976067 7097668275463638722964101)
                  ·
                    refine ⟨1330812801649432260555769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7097668275463638722964101 1330812801649432260555769)
                    ·
                      rfl

theorem cell22_3887623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3887623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887623 prefixEnd_3887623 := by exact prefixLift 3887623
  have htrace : WordTrace (prefixWord ++ tailWord_3887623) baseStart_3887623 baseEnd_3887623 := by
    simpa [prefixWord, tailWord_3887623, baseEnd_3887623] using wordTrace_append hprefix tailTrace_3887623
  have hstable : (prefixWord ++ tailWord_3887623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887623).length < 2 ^ (prefixWord ++ tailWord_3887623).sum := by decide
  have hdescent : baseEnd_3887623 < baseStart_3887623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887636 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_3887636 : Nat := 118140960795 + 3887636 * 2 ^ 59
def prefixEnd_3887636 : Nat := 4983230072969 + 3 ^ 40 * 3887636 * 2
def baseEnd_3887636 : Nat := 1330817251815104559980729

theorem tailTrace_3887636 : CollatzResearch.WordTrace tailWord_3887636 prefixEnd_3887636 1330817251815104559980729 := by
  unfold tailWord_3887636
  simp only [CollatzResearch.WordTrace]
  refine ⟨70896866871883101106861381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94529155829177468142481841 70896866871883101106861381)
  ·
    refine ⟨13293162538478081457536509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70896866871883101106861381 13293162538478081457536509)
    ·
      refine ⟨4984935951929280546576191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13293162538478081457536509 4984935951929280546576191)
      ·
        refine ⟨7477403927893920819864287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4984935951929280546576191 7477403927893920819864287)
        ·
          refine ⟨11216105891840881229796431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7477403927893920819864287 11216105891840881229796431)
          ·
            refine ⟨16824158837761321844694647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216105891840881229796431 16824158837761321844694647)
            ·
              refine ⟨25236238256641982767041971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824158837761321844694647 25236238256641982767041971)
              ·
                refine ⟨37854357384962974150562957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25236238256641982767041971 37854357384962974150562957)
                ·
                  refine ⟨14195384019361115306461109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37854357384962974150562957 14195384019361115306461109)
                  ·
                    refine ⟨1330817251815104559980729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14195384019361115306461109 1330817251815104559980729)
                    ·
                      rfl

theorem cell22_3887636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_3887636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887636 prefixEnd_3887636 := by exact prefixLift 3887636
  have htrace : WordTrace (prefixWord ++ tailWord_3887636) baseStart_3887636 baseEnd_3887636 := by
    simpa [prefixWord, tailWord_3887636, baseEnd_3887636] using wordTrace_append hprefix tailTrace_3887636
  have hstable : (prefixWord ++ tailWord_3887636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887636).length < 2 ^ (prefixWord ++ tailWord_3887636).sum := by decide
  have hdescent : baseEnd_3887636 < baseStart_3887636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887655 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 4]
def baseStart_3887655 : Nat := 118140960795 + 3887655 * 2 ^ 59
def prefixEnd_3887655 : Nat := 4983230072969 + 3 ^ 40 * 3887655 * 2
def baseEnd_3887655 : Nat := 443607918634464947918557

theorem tailTrace_3887655 : CollatzResearch.WordTrace tailWord_3887655 prefixEnd_3887655 443607918634464947918557 := by
  unfold tailWord_3887655
  simp only [CollatzResearch.WordTrace]
  refine ⟨141794426730697368458664419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94529617820464912305776279 141794426730697368458664419)
  ·
    refine ⟨212691640096046052687996629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141794426730697368458664419 212691640096046052687996629)
    ·
      refine ⟨4984960314751079359874921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 212691640096046052687996629 4984960314751079359874921)
      ·
        refine ⟨3738720236063309519906191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4984960314751079359874921 3738720236063309519906191)
        ·
          refine ⟨5608080354094964279859287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3738720236063309519906191 5608080354094964279859287)
          ·
            refine ⟨8412120531142446419788931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608080354094964279859287 8412120531142446419788931)
            ·
              refine ⟨12618180796713669629683397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8412120531142446419788931 12618180796713669629683397)
              ·
                refine ⟨2365908899383813055565637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12618180796713669629683397 2365908899383813055565637)
                ·
                  refine ⟨443607918634464947918557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365908899383813055565637 443607918634464947918557)
                  ·
                    rfl

theorem cell22_3887655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 4].length) (baseStart_3887655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887655 prefixEnd_3887655 := by exact prefixLift 3887655
  have htrace : WordTrace (prefixWord ++ tailWord_3887655) baseStart_3887655 baseEnd_3887655 := by
    simpa [prefixWord, tailWord_3887655, baseEnd_3887655] using wordTrace_append hprefix tailTrace_3887655
  have hstable : (prefixWord ++ tailWord_3887655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887655).length < 2 ^ (prefixWord ++ tailWord_3887655).sum := by decide
  have hdescent : baseEnd_3887655 < baseStart_3887655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887681 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3887681 : Nat := 118140960795 + 3887681 * 2 ^ 59
def prefixEnd_3887681 : Nat := 4983230072969 + 3 ^ 40 * 3887681 * 2
def baseEnd_3887681 : Nat := 1330832656234739442605591

theorem tailTrace_3887681 : CollatzResearch.WordTrace tailWord_3887681 prefixEnd_3887681 1330832656234739442605591 := by
  unfold tailWord_3887681
  simp only [CollatzResearch.WordTrace]
  refine ⟨141795375028603174899110897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94530250019068783266073931 141795375028603174899110897)
  ·
    refine ⟨106346531271452381174333173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141795375028603174899110897 106346531271452381174333173)
    ·
      refine ⟨9969987306698660735093735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106346531271452381174333173 9969987306698660735093735)
      ·
        refine ⟨14954980960047991102640603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9969987306698660735093735 14954980960047991102640603)
        ·
          refine ⟨22432471440071986653960905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14954980960047991102640603 22432471440071986653960905)
          ·
            refine ⟨16824353580053989990470679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22432471440071986653960905 16824353580053989990470679)
            ·
              refine ⟨25236530370080984985706019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16824353580053989990470679 25236530370080984985706019)
              ·
                refine ⟨37854795555121477478559029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25236530370080984985706019 37854795555121477478559029)
                ·
                  refine ⟨3548887083292638513614909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37854795555121477478559029 3548887083292638513614909)
                  ·
                    refine ⟨1330832656234739442605591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3548887083292638513614909 1330832656234739442605591)
                    ·
                      rfl

theorem cell22_3887681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3887681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887681 prefixEnd_3887681 := by exact prefixLift 3887681
  have htrace : WordTrace (prefixWord ++ tailWord_3887681) baseStart_3887681 baseEnd_3887681 := by
    simpa [prefixWord, tailWord_3887681, baseEnd_3887681] using wordTrace_append hprefix tailTrace_3887681
  have hstable : (prefixWord ++ tailWord_3887681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887681).length < 2 ^ (prefixWord ++ tailWord_3887681).sum := by decide
  have hdescent : baseEnd_3887681 < baseStart_3887681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887724 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_3887724 : Nat := 118140960795 + 3887724 * 2 ^ 59
def prefixEnd_3887724 : Nat := 4983230072969 + 3 ^ 40 * 3887724 * 2
def baseEnd_3887724 : Nat := 1330847376013501663780459

theorem tailTrace_3887724 : CollatzResearch.WordTrace tailWord_3887724 prefixEnd_3887724 1330847376013501663780459 := by
  unfold tailWord_3887724
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898471683723696621463113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94531295578298262161950817 70898471683723696621463113)
  ·
    refine ⟨53173853762792772466097335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70898471683723696621463113 53173853762792772466097335)
    ·
      refine ⟨79760780644189158699146003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53173853762792772466097335 79760780644189158699146003)
      ·
        refine ⟨119641170966283738048719005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79760780644189158699146003 119641170966283738048719005)
        ·
          refine ⟨44865439112356401768269627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119641170966283738048719005 44865439112356401768269627)
          ·
            refine ⟨67298158668534602652404441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44865439112356401768269627 67298158668534602652404441)
            ·
              refine ⟨50473619001400951989303331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67298158668534602652404441 50473619001400951989303331)
              ·
                refine ⟨75710428502101427983954997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50473619001400951989303331 75710428502101427983954997)
                ·
                  refine ⟨7097852672072008873495781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75710428502101427983954997 7097852672072008873495781)
                  ·
                    refine ⟨1330847376013501663780459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7097852672072008873495781 1330847376013501663780459)
                    ·
                      rfl

theorem cell22_3887724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_3887724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887724 prefixEnd_3887724 := by exact prefixLift 3887724
  have htrace : WordTrace (prefixWord ++ tailWord_3887724) baseStart_3887724 baseEnd_3887724 := by
    simpa [prefixWord, tailWord_3887724, baseEnd_3887724] using wordTrace_append hprefix tailTrace_3887724
  have hstable : (prefixWord ++ tailWord_3887724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887724).length < 2 ^ (prefixWord ++ tailWord_3887724).sum := by decide
  have hdescent : baseEnd_3887724 < baseStart_3887724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887726 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3887726 : Nat := 118140960795 + 3887726 * 2 ^ 59
def prefixEnd_3887726 : Nat := 4983230072969 + 3 ^ 40 * 3887726 * 2
def baseEnd_3887726 : Nat := 1330848060654374325230453

theorem tailTrace_3887726 : CollatzResearch.WordTrace tailWord_3887726 prefixEnd_3887726 1330848060654374325230453 := by
  unfold tailWord_3887726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17724627039180018448062379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94531344208960098389666021 17724627039180018448062379)
  ·
    refine ⟨26586940558770027672093569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17724627039180018448062379 26586940558770027672093569)
    ·
      refine ⟨19940205419077520754070177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26586940558770027672093569 19940205419077520754070177)
      ·
        refine ⟨14955154064308140565552633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19940205419077520754070177 14955154064308140565552633)
        ·
          refine ⟨11216365548231105424164475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14955154064308140565552633 11216365548231105424164475)
          ·
            refine ⟨16824548322346658136246713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216365548231105424164475 16824548322346658136246713)
            ·
              refine ⟨12618411241759993602185035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16824548322346658136246713 12618411241759993602185035)
              ·
                refine ⟨18927616862639990403277553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12618411241759993602185035 18927616862639990403277553)
                ·
                  refine ⟨14195712646979992802458165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18927616862639990403277553 14195712646979992802458165)
                  ·
                    refine ⟨1330848060654374325230453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14195712646979992802458165 1330848060654374325230453)
                    ·
                      rfl

theorem cell22_3887726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3887726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887726 prefixEnd_3887726 := by exact prefixLift 3887726
  have htrace : WordTrace (prefixWord ++ tailWord_3887726) baseStart_3887726 baseEnd_3887726 := by
    simpa [prefixWord, tailWord_3887726, baseEnd_3887726] using wordTrace_append hprefix tailTrace_3887726
  have hstable : (prefixWord ++ tailWord_3887726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887726).length < 2 ^ (prefixWord ++ tailWord_3887726).sum := by decide
  have hdescent : baseEnd_3887726 < baseStart_3887726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887728 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_3887728 : Nat := 118140960795 + 3887728 * 2 ^ 59
def prefixEnd_3887728 : Nat := 4983230072969 + 3 ^ 40 * 3887728 * 2
def baseEnd_3887728 : Nat := 443616248431748995560149

theorem tailTrace_3887728 : CollatzResearch.WordTrace tailWord_3887728 prefixEnd_3887728 443616248431748995560149 := by
  unfold tailWord_3887728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70898544629716450963035919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94531392839621934617381225 70898544629716450963035919)
  ·
    refine ⟨106347816944574676444553879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70898544629716450963035919 106347816944574676444553879)
    ·
      refine ⟨159521725416862014666830819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106347816944574676444553879 159521725416862014666830819)
      ·
        refine ⟨239282588125293022000246229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159521725416862014666830819 239282588125293022000246229)
        ·
          refine ⟨5608185659186555203130771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 239282588125293022000246229 5608185659186555203130771)
          ·
            refine ⟨8412278488779832804696157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608185659186555203130771 8412278488779832804696157)
            ·
              refine ⟨3154604433292437301761059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8412278488779832804696157 3154604433292437301761059)
              ·
                refine ⟨4731906649938655952641589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3154604433292437301761059 4731906649938655952641589)
                ·
                  refine ⟨443616248431748995560149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4731906649938655952641589 443616248431748995560149)
                  ·
                    rfl

theorem cell22_3887728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_3887728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887728 prefixEnd_3887728 := by exact prefixLift 3887728
  have htrace : WordTrace (prefixWord ++ tailWord_3887728) baseStart_3887728 baseEnd_3887728 := by
    simpa [prefixWord, tailWord_3887728, baseEnd_3887728] using wordTrace_append hprefix tailTrace_3887728
  have hstable : (prefixWord ++ tailWord_3887728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887728).length < 2 ^ (prefixWord ++ tailWord_3887728).sum := by decide
  have hdescent : baseEnd_3887728 < baseStart_3887728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887756 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 4]
def baseStart_3887756 : Nat := 118140960795 + 3887756 * 2 ^ 59
def prefixEnd_3887756 : Nat := 4983230072969 + 3 ^ 40 * 3887756 * 2
def baseEnd_3887756 : Nat := 443619443422488082326787

theorem tailTrace_3887756 : CollatzResearch.WordTrace tailWord_3887756 prefixEnd_3887756 443619443422488082326787 := by
  unfold tailWord_3887756
  simp only [CollatzResearch.WordTrace]
  refine ⟨70899055251665731354045561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94532073668887641805394081 70899055251665731354045561)
  ·
    refine ⟨53174291438749298515534171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70899055251665731354045561 53174291438749298515534171)
    ·
      refine ⟨79761437158123947773301257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53174291438749298515534171 79761437158123947773301257)
      ·
        refine ⟨59821077868592960829975943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79761437158123947773301257 59821077868592960829975943)
        ·
          refine ⟨89731616802889441244963915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59821077868592960829975943 89731616802889441244963915)
          ·
            refine ⟨134597425204334161867445873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89731616802889441244963915 134597425204334161867445873)
            ·
              refine ⟨100948068903250621400584405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134597425204334161867445873 100948068903250621400584405)
              ·
                refine ⟨2365970364919936439076197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100948068903250621400584405 2365970364919936439076197)
                ·
                  refine ⟨443619443422488082326787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2365970364919936439076197 443619443422488082326787)
                  ·
                    rfl

theorem cell22_3887756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_3887756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887756 prefixEnd_3887756 := by exact prefixLift 3887756
  have htrace : WordTrace (prefixWord ++ tailWord_3887756) baseStart_3887756 baseEnd_3887756 := by
    simpa [prefixWord, tailWord_3887756, baseEnd_3887756] using wordTrace_append hprefix tailTrace_3887756
  have hstable : (prefixWord ++ tailWord_3887756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887756).length < 2 ^ (prefixWord ++ tailWord_3887756).sum := by decide
  have hdescent : baseEnd_3887756 < baseStart_3887756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887891 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 6]
def baseStart_3887891 : Nat := 118140960795 + 3887891 * 2 ^ 59
def prefixEnd_3887891 : Nat := 4983230072969 + 3 ^ 40 * 3887891 * 2
def baseEnd_3887891 : Nat := 443634847842122964951649

theorem tailTrace_3887891 : CollatzResearch.WordTrace tailWord_3887891 prefixEnd_3887891 443634847842122964951649 := by
  unfold tailWord_3887891
  simp only [CollatzResearch.WordTrace]
  refine ⟨141803034357842380764255527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94535356238561587176170351 141803034357842380764255527)
  ·
    refine ⟨212704551536763571146383291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141803034357842380764255527 212704551536763571146383291)
    ·
      refine ⟨319056827305145356719574937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212704551536763571146383291 319056827305145356719574937)
      ·
        refine ⟨239292620478859017539681203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319056827305145356719574937 239292620478859017539681203)
        ·
          refine ⟨358938930718288526309521805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239292620478859017539681203 358938930718288526309521805)
          ·
            refine ⟨134602099019358197366070677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 358938930718288526309521805 134602099019358197366070677)
            ·
              refine ⟨6309473391532415501534563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134602099019358197366070677 6309473391532415501534563)
              ·
                refine ⟨9464210087298623252301845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309473391532415501534563 9464210087298623252301845)
                ·
                  refine ⟨443634847842122964951649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9464210087298623252301845 443634847842122964951649)
                  ·
                    rfl

theorem cell22_3887891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 6].length) (baseStart_3887891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887891 prefixEnd_3887891 := by exact prefixLift 3887891
  have htrace : WordTrace (prefixWord ++ tailWord_3887891) baseStart_3887891 baseEnd_3887891 := by
    simpa [prefixWord, tailWord_3887891, baseEnd_3887891] using wordTrace_append hprefix tailTrace_3887891
  have hstable : (prefixWord ++ tailWord_3887891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887891).length < 2 ^ (prefixWord ++ tailWord_3887891).sum := by decide
  have hdescent : baseEnd_3887891 < baseStart_3887891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887921 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_3887921 : Nat := 118140960795 + 3887921 * 2 ^ 59
def prefixEnd_3887921 : Nat := 4983230072969 + 3 ^ 40 * 3887921 * 2
def baseEnd_3887921 : Nat := 1330914813139458816604855

theorem tailTrace_3887921 : CollatzResearch.WordTrace tailWord_3887921 prefixEnd_3887921 1330914813139458816604855 := by
  unfold tailWord_3887921
  simp only [CollatzResearch.WordTrace]
  refine ⟨141804128547733695887847617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94536085698489130591898411 141804128547733695887847617)
  ·
    refine ⟨106353096410800271915885713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141804128547733695887847617 106353096410800271915885713)
    ·
      refine ⟨79764822308100203936914285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106353096410800271915885713 79764822308100203936914285)
      ·
        refine ⟨29911808365537576476342857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79764822308100203936914285 29911808365537576476342857)
        ·
          refine ⟨22433856274153182357257143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29911808365537576476342857 22433856274153182357257143)
          ·
            refine ⟨33650784411229773535885715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22433856274153182357257143 33650784411229773535885715)
            ·
              refine ⟨50476176616844660303828573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33650784411229773535885715 50476176616844660303828573)
              ·
                refine ⟨18928566231316747613935715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50476176616844660303828573 18928566231316747613935715)
                ·
                  refine ⟨28392849346975121420903573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18928566231316747613935715 28392849346975121420903573)
                  ·
                    refine ⟨1330914813139458816604855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28392849346975121420903573 1330914813139458816604855)
                    ·
                      rfl

theorem cell22_3887921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_3887921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887921 prefixEnd_3887921 := by exact prefixLift 3887921
  have htrace : WordTrace (prefixWord ++ tailWord_3887921) baseStart_3887921 baseEnd_3887921 := by
    simpa [prefixWord, tailWord_3887921, baseEnd_3887921] using wordTrace_append hprefix tailTrace_3887921
  have hstable : (prefixWord ++ tailWord_3887921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887921).length < 2 ^ (prefixWord ++ tailWord_3887921).sum := by decide
  have hdescent : baseEnd_3887921 < baseStart_3887921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887923 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 4, 3]
def baseStart_3887923 : Nat := 118140960795 + 3887923 * 2 ^ 59
def prefixEnd_3887923 : Nat := 4983230072969 + 3 ^ 40 * 3887923 * 2
def baseEnd_3887923 : Nat := 1330915497780331478054849

theorem tailTrace_3887923 : CollatzResearch.WordTrace tailWord_3887923 prefixEnd_3887923 1330915497780331478054849 := by
  unfold tailWord_3887923
  simp only [CollatzResearch.WordTrace]
  refine ⟨141804201493726450229420423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94536134329150966819613615 141804201493726450229420423)
  ·
    refine ⟨212706302240589675344130635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141804201493726450229420423 212706302240589675344130635)
    ·
      refine ⟨319059453360884513016195953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212706302240589675344130635 319059453360884513016195953)
      ·
        refine ⟨239294590020663384762146965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319059453360884513016195953 239294590020663384762146965)
        ·
          refine ⟨11216933907218596160725639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 239294590020663384762146965 11216933907218596160725639)
          ·
            refine ⟨16825400860827894241088459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216933907218596160725639 16825400860827894241088459)
            ·
              refine ⟨25238101291241841361632689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16825400860827894241088459 25238101291241841361632689)
              ·
                refine ⟨18928575968431381021224517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25238101291241841361632689 18928575968431381021224517)
                ·
                  refine ⟨3549107994080883941479597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18928575968431381021224517 3549107994080883941479597)
                  ·
                    refine ⟨1330915497780331478054849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549107994080883941479597 1330915497780331478054849)
                    ·
                      rfl

theorem cell22_3887923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3].length) (baseStart_3887923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887923 prefixEnd_3887923 := by exact prefixLift 3887923
  have htrace : WordTrace (prefixWord ++ tailWord_3887923) baseStart_3887923 baseEnd_3887923 := by
    simpa [prefixWord, tailWord_3887923, baseEnd_3887923] using wordTrace_append hprefix tailTrace_3887923
  have hstable : (prefixWord ++ tailWord_3887923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887923).length < 2 ^ (prefixWord ++ tailWord_3887923).sum := by decide
  have hdescent : baseEnd_3887923 < baseStart_3887923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887925 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 4]
def baseStart_3887925 : Nat := 118140960795 + 3887925 * 2 ^ 59
def prefixEnd_3887925 : Nat := 4983230072969 + 3 ^ 40 * 3887925 * 2
def baseEnd_3887925 : Nat := 443638727473734713168281

theorem tailTrace_3887925 : CollatzResearch.WordTrace tailWord_3887925 prefixEnd_3887925 443638727473734713168281 := by
  unfold tailWord_3887925
  simp only [CollatzResearch.WordTrace]
  refine ⟨141804274439719204570993229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94536182959812803047328819 141804274439719204570993229)
  ·
    refine ⟨53176602914894701714122461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141804274439719204570993229 53176602914894701714122461)
    ·
      refine ⟨19941226093085513142795923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53176602914894701714122461 19941226093085513142795923)
      ·
        refine ⟨29911839139628269714193885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19941226093085513142795923 29911839139628269714193885)
        ·
          refine ⟨11216939677360601142822707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29911839139628269714193885 11216939677360601142822707)
          ·
            refine ⟨16825409516040901714234061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11216939677360601142822707 16825409516040901714234061)
            ·
              refine ⟨6309528568515338142837773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16825409516040901714234061 6309528568515338142837773)
              ·
                refine ⟨2366073213193251803564165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6309528568515338142837773 2366073213193251803564165)
                ·
                  refine ⟨443638727473734713168281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366073213193251803564165 443638727473734713168281)
                  ·
                    rfl

theorem cell22_3887925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_3887925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887925 prefixEnd_3887925 := by exact prefixLift 3887925
  have htrace : WordTrace (prefixWord ++ tailWord_3887925) baseStart_3887925 baseEnd_3887925 := by
    simpa [prefixWord, tailWord_3887925, baseEnd_3887925] using wordTrace_append hprefix tailTrace_3887925
  have hstable : (prefixWord ++ tailWord_3887925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887925).length < 2 ^ (prefixWord ++ tailWord_3887925).sum := by decide
  have hdescent : baseEnd_3887925 < baseStart_3887925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887953 : List Nat := [1, 2, 2, 1, 6, 1, 2, 7]
def baseStart_3887953 : Nat := 118140960795 + 3887953 * 2 ^ 59
def prefixEnd_3887953 : Nat := 4983230072969 + 3 ^ 40 * 3887953 * 2
def baseEnd_3887953 : Nat := 147880640821491266644973

theorem tailTrace_3887953 : CollatzResearch.WordTrace tailWord_3887953 prefixEnd_3887953 147880640821491266644973 := by
  unfold tailWord_3887953
  simp only [CollatzResearch.WordTrace]
  refine ⟨141805295683617765353012513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94536863789078510235341675 141805295683617765353012513)
  ·
    refine ⟨106353971762713324014759385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141805295683617765353012513 106353971762713324014759385)
    ·
      refine ⟨79765478822034993011069539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106353971762713324014759385 79765478822034993011069539)
      ·
        refine ⟨119648218233052489516604309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79765478822034993011069539 119648218233052489516604309)
        ·
          refine ⟨5608510229674335446090827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119648218233052489516604309 5608510229674335446090827)
          ·
            refine ⟨8412765344511503169136241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5608510229674335446090827 8412765344511503169136241)
            ·
              refine ⟨6309574008383627376852181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8412765344511503169136241 6309574008383627376852181)
              ·
                refine ⟨147880640821491266644973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6309574008383627376852181 147880640821491266644973)
                ·
                  rfl

theorem cell22_3887953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 7].length) (baseStart_3887953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887953 prefixEnd_3887953 := by exact prefixLift 3887953
  have htrace : WordTrace (prefixWord ++ tailWord_3887953) baseStart_3887953 baseEnd_3887953 := by
    simpa [prefixWord, tailWord_3887953, baseEnd_3887953] using wordTrace_append hprefix tailTrace_3887953
  have hstable : (prefixWord ++ tailWord_3887953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887953).length < 2 ^ (prefixWord ++ tailWord_3887953).sum := by decide
  have hdescent : baseEnd_3887953 < baseStart_3887953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887968 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_3887968 : Nat := 118140960795 + 3887968 * 2 ^ 59
def prefixEnd_3887968 : Nat := 4983230072969 + 3 ^ 40 * 3887968 * 2
def baseEnd_3887968 : Nat := 1330930902199966360679711

theorem tailTrace_3887968 : CollatzResearch.WordTrace tailWord_3887968 prefixEnd_3887968 1330930902199966360679711 := by
  unfold tailWord_3887968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70902921389281711457404279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94537228519042281943205705 70902921389281711457404279)
  ·
    refine ⟨106354382083922567186106419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70902921389281711457404279 106354382083922567186106419)
    ·
      refine ⟨159531573125883850779159629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106354382083922567186106419 159531573125883850779159629)
      ·
        refine ⟨59824339922206444042184861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159531573125883850779159629 59824339922206444042184861)
        ·
          refine ⟨22434127470827416515819323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59824339922206444042184861 22434127470827416515819323)
          ·
            refine ⟨33651191206241124773728985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22434127470827416515819323 33651191206241124773728985)
            ·
              refine ⟨25238393404680843580296739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33651191206241124773728985 25238393404680843580296739)
              ·
                refine ⟨37857590107021265370445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25238393404680843580296739 37857590107021265370445109)
                ·
                  refine ⟨3549149072533243628479229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37857590107021265370445109 3549149072533243628479229)
                  ·
                    refine ⟨1330930902199966360679711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549149072533243628479229 1330930902199966360679711)
                    ·
                      rfl

theorem cell22_3887968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_3887968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887968 prefixEnd_3887968 := by exact prefixLift 3887968
  have htrace : WordTrace (prefixWord ++ tailWord_3887968) baseStart_3887968 baseEnd_3887968 := by
    simpa [prefixWord, tailWord_3887968, baseEnd_3887968] using wordTrace_append hprefix tailTrace_3887968
  have hstable : (prefixWord ++ tailWord_3887968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887968).length < 2 ^ (prefixWord ++ tailWord_3887968).sum := by decide
  have hdescent : baseEnd_3887968 < baseStart_3887968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3887996 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_3887996 : Nat := 118140960795 + 3887996 * 2 ^ 59
def prefixEnd_3887996 : Nat := 4983230072969 + 3 ^ 40 * 3887996 * 2
def baseEnd_3887996 : Nat := 1330940487172183620979625

theorem tailTrace_3887996 : CollatzResearch.WordTrace tailWord_3887996 prefixEnd_3887996 1330940487172183620979625 := by
  unfold tailWord_3887996
  simp only [CollatzResearch.WordTrace]
  refine ⟨70903432011230991848413921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94537909348307989131218561 70903432011230991848413921)
  ·
    refine ⟨53177574008423243886310441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70903432011230991848413921 53177574008423243886310441)
    ·
      refine ⟨39883180506317432914732831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53177574008423243886310441 39883180506317432914732831)
      ·
        refine ⟨59824770759476149372099247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39883180506317432914732831 59824770759476149372099247)
        ·
          refine ⟨89737156139214224058148871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59824770759476149372099247 89737156139214224058148871)
          ·
            refine ⟨134605734208821336087223307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89737156139214224058148871 134605734208821336087223307)
            ·
              refine ⟨201908601313232004130834961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134605734208821336087223307 201908601313232004130834961)
              ·
                refine ⟨151431450984924003098126221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201908601313232004130834961 151431450984924003098126221)
                ·
                  refine ⟨56786794119346501161797333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151431450984924003098126221 56786794119346501161797333)
                  ·
                    refine ⟨1330940487172183620979625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56786794119346501161797333 1330940487172183620979625)
                    ·
                      rfl

theorem cell22_3887996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_3887996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3887996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3887996 prefixEnd_3887996 := by exact prefixLift 3887996
  have htrace : WordTrace (prefixWord ++ tailWord_3887996) baseStart_3887996 baseEnd_3887996 := by
    simpa [prefixWord, tailWord_3887996, baseEnd_3887996] using wordTrace_append hprefix tailTrace_3887996
  have hstable : (prefixWord ++ tailWord_3887996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3887996).length < 2 ^ (prefixWord ++ tailWord_3887996).sum := by decide
  have hdescent : baseEnd_3887996 < baseStart_3887996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3887996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888075 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 1, 5]
def baseStart_3888075 : Nat := 118140960795 + 3888075 * 2 ^ 59
def prefixEnd_3888075 : Nat := 4983230072969 + 3 ^ 40 * 3888075 * 2
def baseEnd_3888075 : Nat := 1330967530486653748254383

theorem tailTrace_3888075 : CollatzResearch.WordTrace tailWord_3888075 prefixEnd_3888075 1330967530486653748254383 := by
  unfold tailWord_3888075
  simp only [CollatzResearch.WordTrace]
  refine ⟨141809745389175780188953679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94539830259450520125969119 141809745389175780188953679)
  ·
    refine ⟨212714618083763670283430519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141809745389175780188953679 212714618083763670283430519)
    ·
      refine ⟨319071927125645505425145779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212714618083763670283430519 319071927125645505425145779)
      ·
        refine ⟨478607890688468258137718669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319071927125645505425145779 478607890688468258137718669)
        ·
          refine ⟨179477959008175596801644501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 478607890688468258137718669 179477959008175596801644501)
          ·
            refine ⟨4206514664254115550038543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 179477959008175596801644501 4206514664254115550038543)
            ·
              refine ⟨6309771996381173325057815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206514664254115550038543 6309771996381173325057815)
              ·
                refine ⟨9464657994571759987586723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6309771996381173325057815 9464657994571759987586723)
                ·
                  refine ⟨14196986991857639981380085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9464657994571759987586723 14196986991857639981380085)
                  ·
                    refine ⟨1330967530486653748254383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14196986991857639981380085 1330967530486653748254383)
                    ·
                      rfl

theorem cell22_3888075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5].length) (baseStart_3888075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888075 prefixEnd_3888075 := by exact prefixLift 3888075
  have htrace : WordTrace (prefixWord ++ tailWord_3888075) baseStart_3888075 baseEnd_3888075 := by
    simpa [prefixWord, tailWord_3888075, baseEnd_3888075] using wordTrace_append hprefix tailTrace_3888075
  have hstable : (prefixWord ++ tailWord_3888075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888075).length < 2 ^ (prefixWord ++ tailWord_3888075).sum := by decide
  have hdescent : baseEnd_3888075 < baseStart_3888075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888088 : List Nat := [2, 1, 2, 2, 2, 4, 1, 8]
def baseStart_3888088 : Nat := 118140960795 + 3888088 * 2 ^ 59
def prefixEnd_3888088 : Nat := 4983230072969 + 3 ^ 40 * 3888088 * 2
def baseEnd_3888088 : Nat := 147885775628036227519927

theorem tailTrace_3888088 : CollatzResearch.WordTrace tailWord_3888088 prefixEnd_3888088 147885775628036227519927 := by
  unfold tailWord_3888088
  simp only [CollatzResearch.WordTrace]
  refine ⟨70905109769064341704588459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94540146358752455606117945 70905109769064341704588459)
  ·
    refine ⟨106357664653596512556882689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70905109769064341704588459 106357664653596512556882689)
    ·
      refine ⟨79768248490197384417662017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106357664653596512556882689 79768248490197384417662017)
      ·
        refine ⟨59826186367648038313246513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79768248490197384417662017 59826186367648038313246513)
        ·
          refine ⟨44869639775736028734934885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59826186367648038313246513 44869639775736028734934885)
          ·
            refine ⟨8413057457950505387800291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44869639775736028734934885 8413057457950505387800291)
            ·
              refine ⟨12619586186925758081700437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413057457950505387800291 12619586186925758081700437)
              ·
                refine ⟨147885775628036227519927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12619586186925758081700437 147885775628036227519927)
                ·
                  rfl

theorem cell22_3888088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_3888088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888088 prefixEnd_3888088 := by exact prefixLift 3888088
  have htrace : WordTrace (prefixWord ++ tailWord_3888088) baseStart_3888088 baseEnd_3888088 := by
    simpa [prefixWord, tailWord_3888088, baseEnd_3888088] using wordTrace_append hprefix tailTrace_3888088
  have hstable : (prefixWord ++ tailWord_3888088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888088).length < 2 ^ (prefixWord ++ tailWord_3888088).sum := by decide
  have hdescent : baseEnd_3888088 < baseStart_3888088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888167 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 5]
def baseStart_3888167 : Nat := 118140960795 + 3888167 * 2 ^ 59
def prefixEnd_3888167 : Nat := 4983230072969 + 3 ^ 40 * 3888167 * 2
def baseEnd_3888167 : Nat := 443666341322265391651367

theorem tailTrace_3888167 : CollatzResearch.WordTrace tailWord_3888167 prefixEnd_3888167 443666341322265391651367 := by
  unfold tailWord_3888167
  simp only [CollatzResearch.WordTrace]
  refine ⟨141813100904842479901302755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94542067269894986600868503 141813100904842479901302755)
  ·
    refine ⟨212719651357263719851954133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141813100904842479901302755 212719651357263719851954133)
    ·
      refine ⟨4985616828685868434030175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 212719651357263719851954133 4985616828685868434030175)
      ·
        refine ⟨7478425243028802651045263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4985616828685868434030175 7478425243028802651045263)
        ·
          refine ⟨11217637864543203976567895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478425243028802651045263 11217637864543203976567895)
          ·
            refine ⟨16826456796814805964851843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217637864543203976567895 16826456796814805964851843)
            ·
              refine ⟨25239685195222208947277765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16826456796814805964851843 25239685195222208947277765)
              ·
                refine ⟨4732440974104164177614581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25239685195222208947277765 4732440974104164177614581)
                ·
                  refine ⟨443666341322265391651367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4732440974104164177614581 443666341322265391651367)
                  ·
                    rfl

theorem cell22_3888167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 5].length) (baseStart_3888167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888167 prefixEnd_3888167 := by exact prefixLift 3888167
  have htrace : WordTrace (prefixWord ++ tailWord_3888167) baseStart_3888167 baseEnd_3888167 := by
    simpa [prefixWord, tailWord_3888167, baseEnd_3888167] using wordTrace_append hprefix tailTrace_3888167
  have hstable : (prefixWord ++ tailWord_3888167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888167).length < 2 ^ (prefixWord ++ tailWord_3888167).sum := by decide
  have hdescent : baseEnd_3888167 < baseStart_3888167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888182 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3888182 : Nat := 118140960795 + 3888182 * 2 ^ 59
def prefixEnd_3888182 : Nat := 4983230072969 + 3 ^ 40 * 3888182 * 2
def baseEnd_3888182 : Nat := 1331004158773341135829055

theorem tailTrace_3888182 : CollatzResearch.WordTrace tailWord_3888182 prefixEnd_3888182 1331004158773341135829055 := by
  unfold tailWord_3888182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8863352999986758591443675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94542431999858758308732533 8863352999986758591443675)
  ·
    refine ⟨13295029499980137887165513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8863352999986758591443675 13295029499980137887165513)
    ·
      refine ⟨9971272124985103415374135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13295029499980137887165513 9971272124985103415374135)
      ·
        refine ⟨14956908187477655123061203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9971272124985103415374135 14956908187477655123061203)
        ·
          refine ⟨22435362281216482684591805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14956908187477655123061203 22435362281216482684591805)
          ·
            refine ⟨8413260855456181006721927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22435362281216482684591805 8413260855456181006721927)
            ·
              refine ⟨12619891283184271510082891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413260855456181006721927 12619891283184271510082891)
              ·
                refine ⟨18929836924776407265124337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12619891283184271510082891 18929836924776407265124337)
                ·
                  refine ⟨14197377693582305448843253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18929836924776407265124337 14197377693582305448843253)
                  ·
                    refine ⟨1331004158773341135829055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14197377693582305448843253 1331004158773341135829055)
                    ·
                      rfl

theorem cell22_3888182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3888182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888182 prefixEnd_3888182 := by exact prefixLift 3888182
  have htrace : WordTrace (prefixWord ++ tailWord_3888182) baseStart_3888182 baseEnd_3888182 := by
    simpa [prefixWord, tailWord_3888182, baseEnd_3888182] using wordTrace_append hprefix tailTrace_3888182
  have hstable : (prefixWord ++ tailWord_3888182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888182).length < 2 ^ (prefixWord ++ tailWord_3888182).sum := by decide
  have hdescent : baseEnd_3888182 < baseStart_3888182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888212 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_3888212 : Nat := 118140960795 + 3888212 * 2 ^ 59
def prefixEnd_3888212 : Nat := 4983230072969 + 3 ^ 40 * 3888212 * 2
def baseEnd_3888212 : Nat := 443671476128810352526321

theorem tailTrace_3888212 : CollatzResearch.WordTrace tailWord_3888212 prefixEnd_3888212 443671476128810352526321 := by
  unfold tailWord_3888212
  simp only [CollatzResearch.WordTrace]
  refine ⟨70907371094839726293345445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94543161459786301724460593 70907371094839726293345445)
  ·
    refine ⟨13295132080282448680002271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70907371094839726293345445 13295132080282448680002271)
    ·
      refine ⟨19942698120423673020003407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13295132080282448680002271 19942698120423673020003407)
      ·
        refine ⟨29914047180635509530005111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19942698120423673020003407 29914047180635509530005111)
        ·
          refine ⟨44871070770953264295007667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29914047180635509530005111 44871070770953264295007667)
          ·
            refine ⟨67306606156429896442511501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44871070770953264295007667 67306606156429896442511501)
            ·
              refine ⟨25239977308661211165941813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67306606156429896442511501 25239977308661211165941813)
              ·
                refine ⟨2366247872686988546807045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25239977308661211165941813 2366247872686988546807045)
                ·
                  refine ⟨443671476128810352526321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366247872686988546807045 443671476128810352526321)
                  ·
                    rfl

theorem cell22_3888212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_3888212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888212 prefixEnd_3888212 := by exact prefixLift 3888212
  have htrace : WordTrace (prefixWord ++ tailWord_3888212) baseStart_3888212 baseEnd_3888212 := by
    simpa [prefixWord, tailWord_3888212, baseEnd_3888212] using wordTrace_append hprefix tailTrace_3888212
  have hstable : (prefixWord ++ tailWord_3888212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888212).length < 2 ^ (prefixWord ++ tailWord_3888212).sum := by decide
  have hdescent : baseEnd_3888212 < baseStart_3888212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888223 : List Nat := [1, 1, 2, 3, 1, 1, 13]
def baseStart_3888223 : Nat := 118140960795 + 3888223 * 2 ^ 59
def prefixEnd_3888223 : Nat := 4983230072969 + 3 ^ 40 * 3888223 * 2
def baseEnd_3888223 : Nat := 49296970144860396131627

theorem tailTrace_3888223 : CollatzResearch.WordTrace tailWord_3888223 prefixEnd_3888223 49296970144860396131627 := by
  unfold tailWord_3888223
  simp only [CollatzResearch.WordTrace]
  refine ⟨141815143392639601465341323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94543428928426400976894215 141815143392639601465341323)
  ·
    refine ⟨212722715088959402198011985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141815143392639601465341323 212722715088959402198011985)
    ·
      refine ⟨159542036316719551648508989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212722715088959402198011985 159542036316719551648508989)
      ·
        refine ⟨59828263618769831868190871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159542036316719551648508989 59828263618769831868190871)
        ·
          refine ⟨89742395428154747802286307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59828263618769831868190871 89742395428154747802286307)
          ·
            refine ⟨134613593142232121703429461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89742395428154747802286307 134613593142232121703429461)
            ·
              refine ⟨49296970144860396131627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 134613593142232121703429461 49296970144860396131627)
              ·
                rfl

theorem cell22_3888223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 13].length) (baseStart_3888223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888223 prefixEnd_3888223 := by exact prefixLift 3888223
  have htrace : WordTrace (prefixWord ++ tailWord_3888223) baseStart_3888223 baseEnd_3888223 := by
    simpa [prefixWord, tailWord_3888223, baseEnd_3888223] using wordTrace_append hprefix tailTrace_3888223
  have hstable : (prefixWord ++ tailWord_3888223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888223).length < 2 ^ (prefixWord ++ tailWord_3888223).sum := by decide
  have hdescent : baseEnd_3888223 < baseStart_3888223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888225 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3888225 : Nat := 118140960795 + 3888225 * 2 ^ 59
def prefixEnd_3888225 : Nat := 4983230072969 + 3 ^ 40 * 3888225 * 2
def baseEnd_3888225 : Nat := 1331018878552103357003923

theorem tailTrace_3888225 : CollatzResearch.WordTrace tailWord_3888225 prefixEnd_3888225 1331018878552103357003923 := by
  unfold tailWord_3888225
  simp only [CollatzResearch.WordTrace]
  refine ⟨141815216338632355806914129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94543477559088237204609419 141815216338632355806914129)
  ·
    refine ⟨106361412253974266855185597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141815216338632355806914129 106361412253974266855185597)
    ·
      refine ⟨39885529595240350070694599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106361412253974266855185597 39885529595240350070694599)
      ·
        refine ⟨59828294392860525106041899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39885529595240350070694599 59828294392860525106041899)
        ·
          refine ⟨89742441589290787659062849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59828294392860525106041899 89742441589290787659062849)
          ·
            refine ⟨67306831191968090744297137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89742441589290787659062849 67306831191968090744297137)
            ·
              refine ⟨50480123393976068058222853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67306831191968090744297137 50480123393976068058222853)
              ·
                refine ⟨9465023136370512760916785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50480123393976068058222853 9465023136370512760916785)
                ·
                  refine ⟨7098767352277884570687589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465023136370512760916785 7098767352277884570687589)
                  ·
                    refine ⟨1331018878552103357003923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7098767352277884570687589 1331018878552103357003923)
                    ·
                      rfl

theorem cell22_3888225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3888225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888225 prefixEnd_3888225 := by exact prefixLift 3888225
  have htrace : WordTrace (prefixWord ++ tailWord_3888225) baseStart_3888225 baseEnd_3888225 := by
    simpa [prefixWord, tailWord_3888225, baseEnd_3888225] using wordTrace_append hprefix tailTrace_3888225
  have hstable : (prefixWord ++ tailWord_3888225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888225).length < 2 ^ (prefixWord ++ tailWord_3888225).sum := by decide
  have hdescent : baseEnd_3888225 < baseStart_3888225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888257 : List Nat := [1, 2, 4, 2, 2, 1, 4, 6]
def baseStart_3888257 : Nat := 118140960795 + 3888257 * 2 ^ 59
def prefixEnd_3888257 : Nat := 4983230072969 + 3 ^ 40 * 3888257 * 2
def baseEnd_3888257 : Nat := 147892203645118437800425

theorem tailTrace_3888257 : CollatzResearch.WordTrace tailWord_3888257 prefixEnd_3888257 147892203645118437800425 := by
  unfold tailWord_3888257
  simp only [CollatzResearch.WordTrace]
  refine ⟨141816383474516425272079025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94544255649677616848052683 141816383474516425272079025)
  ·
    refine ⟨106362287605887318954059269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141816383474516425272079025 106362287605887318954059269)
    ·
      refine ⟨19942928926103872303886113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106362287605887318954059269 19942928926103872303886113)
      ·
        refine ⟨14957196694577904227914585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19942928926103872303886113 14957196694577904227914585)
        ·
          refine ⟨11217897520933428170935939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14957196694577904227914585 11217897520933428170935939)
          ·
            refine ⟨16826846281400142256403909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11217897520933428170935939 16826846281400142256403909)
            ·
              refine ⟨3155033677762526673075733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16826846281400142256403909 3155033677762526673075733)
              ·
                refine ⟨147892203645118437800425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3155033677762526673075733 147892203645118437800425)
                ·
                  rfl

theorem cell22_3888257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 6].length) (baseStart_3888257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888257 prefixEnd_3888257 := by exact prefixLift 3888257
  have htrace : WordTrace (prefixWord ++ tailWord_3888257) baseStart_3888257 baseEnd_3888257 := by
    simpa [prefixWord, tailWord_3888257, baseEnd_3888257] using wordTrace_append hprefix tailTrace_3888257
  have hstable : (prefixWord ++ tailWord_3888257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888257).length < 2 ^ (prefixWord ++ tailWord_3888257).sum := by decide
  have hdescent : baseEnd_3888257 < baseStart_3888257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888285 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3888285 : Nat := 118140960795 + 3888285 * 2 ^ 59
def prefixEnd_3888285 : Nat := 4983230072969 + 3 ^ 40 * 3888285 * 2
def baseEnd_3888285 : Nat := 443679805926094400167913

theorem tailTrace_3888285 : CollatzResearch.WordTrace tailWord_3888285 prefixEnd_3888285 443679805926094400167913 := by
  unfold tailWord_3888285
  simp only [CollatzResearch.WordTrace]
  refine ⟨141817404718414986054098309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94544936478943324036065539 141817404718414986054098309)
  ·
    refine ⟨26590763384702809885143433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141817404718414986054098309 26590763384702809885143433)
    ·
      refine ⟨19943072538527107413857575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26590763384702809885143433 19943072538527107413857575)
      ·
        refine ⟨29914608807790661120786363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19943072538527107413857575 29914608807790661120786363)
        ·
          refine ⟨44871913211685991681179545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29914608807790661120786363 44871913211685991681179545)
          ·
            refine ⟨33653934908764493760884659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44871913211685991681179545 33653934908764493760884659)
            ·
              refine ⟨50480902363146740641326989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33653934908764493760884659 50480902363146740641326989)
              ·
                refine ⟨18930338386180027740497621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50480902363146740641326989 18930338386180027740497621)
                ·
                  refine ⟨443679805926094400167913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18930338386180027740497621 443679805926094400167913)
                  ·
                    rfl

theorem cell22_3888285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3888285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888285 prefixEnd_3888285 := by exact prefixLift 3888285
  have htrace : WordTrace (prefixWord ++ tailWord_3888285) baseStart_3888285 baseEnd_3888285 := by
    simpa [prefixWord, tailWord_3888285, baseEnd_3888285] using wordTrace_append hprefix tailTrace_3888285
  have hstable : (prefixWord ++ tailWord_3888285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888285).length < 2 ^ (prefixWord ++ tailWord_3888285).sum := by decide
  have hdescent : baseEnd_3888285 < baseStart_3888285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888345 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_3888345 : Nat := 118140960795 + 3888345 * 2 ^ 59
def prefixEnd_3888345 : Nat := 4983230072969 + 3 ^ 40 * 3888345 * 2
def baseEnd_3888345 : Nat := 1331059957004463044003555

theorem tailTrace_3888345 : CollatzResearch.WordTrace tailWord_3888345 prefixEnd_3888345 1331059957004463044003555 := by
  unfold tailWord_3888345
  simp only [CollatzResearch.WordTrace]
  refine ⟨141819593098197616301282489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94546395398798410867521659 141819593098197616301282489)
  ·
    refine ⟨106364694823648212225961867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141819593098197616301282489 106364694823648212225961867)
    ·
      refine ⟨159547042235472318338942801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106364694823648212225961867 159547042235472318338942801)
      ·
        refine ⟨119660281676604238754207101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159547042235472318338942801 119660281676604238754207101)
        ·
          refine ⟨44872605628726589532827663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119660281676604238754207101 44872605628726589532827663)
          ·
            refine ⟨67308908443089884299241495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44872605628726589532827663 67308908443089884299241495)
            ·
              refine ⟨100963362664634826448862243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67308908443089884299241495 100963362664634826448862243)
              ·
                refine ⟨151445043996952239673293365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100963362664634826448862243 151445043996952239673293365)
                ·
                  refine ⟨14197972874714272469371253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151445043996952239673293365 14197972874714272469371253)
                  ·
                    refine ⟨1331059957004463044003555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14197972874714272469371253 1331059957004463044003555)
                    ·
                      rfl

theorem cell22_3888345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_3888345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888345 prefixEnd_3888345 := by exact prefixLift 3888345
  have htrace : WordTrace (prefixWord ++ tailWord_3888345) baseStart_3888345 baseEnd_3888345 := by
    simpa [prefixWord, tailWord_3888345, baseEnd_3888345] using wordTrace_append hprefix tailTrace_3888345
  have hstable : (prefixWord ++ tailWord_3888345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888345).length < 2 ^ (prefixWord ++ tailWord_3888345).sum := by decide
  have hdescent : baseEnd_3888345 < baseStart_3888345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888362 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3888362 : Nat := 118140960795 + 3888362 * 2 ^ 59
def prefixEnd_3888362 : Nat := 4983230072969 + 3 ^ 40 * 3888362 * 2
def baseEnd_3888362 : Nat := 1331065776451880666328503

theorem tailTrace_3888362 : CollatzResearch.WordTrace tailWord_3888362 prefixEnd_3888362 1331065776451880666328503 := by
  unfold tailWord_3888362
  simp only [CollatzResearch.WordTrace]
  refine ⟨35455053284784007051162835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94546808759424018803100893 35455053284784007051162835)
  ·
    refine ⟨53182579927176010576744253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35455053284784007051162835 53182579927176010576744253)
    ·
      refine ⟨19943467472691003966279095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53182579927176010576744253 19943467472691003966279095)
      ·
        refine ⟨29915201209036505949418643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19943467472691003966279095 29915201209036505949418643)
        ·
          refine ⟨44872801813554758924127965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29915201209036505949418643 44872801813554758924127965)
          ·
            refine ⟨16827300680083034596547987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44872801813554758924127965 16827300680083034596547987)
            ·
              refine ⟨25240951020124551894821981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827300680083034596547987 25240951020124551894821981)
              ·
                refine ⟨9465356632546706960558243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25240951020124551894821981 9465356632546706960558243)
                ·
                  refine ⟨14198034948820060440837365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9465356632546706960558243 14198034948820060440837365)
                  ·
                    refine ⟨1331065776451880666328503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14198034948820060440837365 1331065776451880666328503)
                    ·
                      rfl

theorem cell22_3888362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3888362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888362 prefixEnd_3888362 := by exact prefixLift 3888362
  have htrace : WordTrace (prefixWord ++ tailWord_3888362) baseStart_3888362 baseEnd_3888362 := by
    simpa [prefixWord, tailWord_3888362, baseEnd_3888362] using wordTrace_append hprefix tailTrace_3888362
  have hstable : (prefixWord ++ tailWord_3888362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888362).length < 2 ^ (prefixWord ++ tailWord_3888362).sum := by decide
  have hdescent : baseEnd_3888362 < baseStart_3888362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888392 : List Nat := [2, 1, 3, 2, 4, 1, 9]
def baseStart_3888392 : Nat := 118140960795 + 3888392 * 2 ^ 59
def prefixEnd_3888392 : Nat := 4983230072969 + 3 ^ 40 * 3888392 * 2
def baseEnd_3888392 : Nat := 49299112817221132891793

theorem tailTrace_3888392 : CollatzResearch.WordTrace tailWord_3888392 prefixEnd_3888392 49299112817221132891793 := by
  unfold tailWord_3888392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70910653664513671664121715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94547538219351562218828953 70910653664513671664121715)
  ·
    refine ⟨106365980496770507496182573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70910653664513671664121715 106365980496770507496182573)
    ·
      refine ⟨39887242686288940311068465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106365980496770507496182573 39887242686288940311068465)
      ·
        refine ⟨29915432014716705233301349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39887242686288940311068465 29915432014716705233301349)
        ·
          refine ⟨5609143502759382231244003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29915432014716705233301349 5609143502759382231244003)
          ·
            refine ⟨8413715254139073346866005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609143502759382231244003 8413715254139073346866005)
            ·
              refine ⟨49299112817221132891793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8413715254139073346866005 49299112817221132891793)
              ·
                rfl

theorem cell22_3888392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 9].length) (baseStart_3888392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888392 prefixEnd_3888392 := by exact prefixLift 3888392
  have htrace : WordTrace (prefixWord ++ tailWord_3888392) baseStart_3888392 baseEnd_3888392 := by
    simpa [prefixWord, tailWord_3888392, baseEnd_3888392] using wordTrace_append hprefix tailTrace_3888392
  have hstable : (prefixWord ++ tailWord_3888392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888392).length < 2 ^ (prefixWord ++ tailWord_3888392).sum := by decide
  have hdescent : baseEnd_3888392 < baseStart_3888392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888396 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 2, 3]
def baseStart_3888396 : Nat := 118140960795 + 3888396 * 2 ^ 59
def prefixEnd_3888396 : Nat := 4983230072969 + 3 ^ 40 * 3888396 * 2
def baseEnd_3888396 : Nat := 1331077415346715910978399

theorem tailTrace_3888396 : CollatzResearch.WordTrace tailWord_3888396 prefixEnd_3888396 1331077415346715910978399 := by
  unfold tailWord_3888396
  simp only [CollatzResearch.WordTrace]
  refine ⟨70910726610506426005694521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94547635480675234674259361 70910726610506426005694521)
  ·
    refine ⟨53183044957879819504270891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70910726610506426005694521 53183044957879819504270891)
    ·
      refine ⟨79774567436819729256406337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53183044957879819504270891 79774567436819729256406337)
      ·
        refine ⟨59830925577614796942304753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79774567436819729256406337 59830925577614796942304753)
        ·
          refine ⟨44873194183211097706728565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59830925577614796942304753 44873194183211097706728565)
          ·
            refine ⟨4206861954676040410005803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44873194183211097706728565 4206861954676040410005803)
            ·
              refine ⟨6310292932014060615008705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4206861954676040410005803 6310292932014060615008705)
              ·
                refine ⟨4732719699010545461256529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6310292932014060615008705 4732719699010545461256529)
                ·
                  refine ⟨3549539774257909095942397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4732719699010545461256529 3549539774257909095942397)
                  ·
                    refine ⟨1331077415346715910978399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549539774257909095942397 1331077415346715910978399)
                    ·
                      rfl

theorem cell22_3888396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_3888396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888396 prefixEnd_3888396 := by exact prefixLift 3888396
  have htrace : WordTrace (prefixWord ++ tailWord_3888396) baseStart_3888396 baseEnd_3888396 := by
    simpa [prefixWord, tailWord_3888396, baseEnd_3888396] using wordTrace_append hprefix tailTrace_3888396
  have hstable : (prefixWord ++ tailWord_3888396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888396).length < 2 ^ (prefixWord ++ tailWord_3888396).sum := by decide
  have hdescent : baseEnd_3888396 < baseStart_3888396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888413 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_3888413 : Nat := 118140960795 + 3888413 * 2 ^ 59
def prefixEnd_3888413 : Nat := 4983230072969 + 3 ^ 40 * 3888413 * 2
def baseEnd_3888413 : Nat := 1331083234794133533303347

theorem tailTrace_3888413 : CollatzResearch.WordTrace tailWord_3888413 prefixEnd_3888413 1331083234794133533303347 := by
  unfold tailWord_3888413
  simp only [CollatzResearch.WordTrace]
  refine ⟨141822073261951263914757893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94548048841300842609838595 141822073261951263914757893)
  ·
    refine ⟨26591638736615861984017105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141822073261951263914757893 26591638736615861984017105)
    ·
      refine ⟨19943729052461896488012829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26591638736615861984017105 19943729052461896488012829)
      ·
        refine ⟨7478898394673211183004811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19943729052461896488012829 7478898394673211183004811)
        ·
          refine ⟨11218347592009816774507217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478898394673211183004811 11218347592009816774507217)
          ·
            refine ⟨8413760694007362580880413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11218347592009816774507217 8413760694007362580880413)
            ·
              refine ⟨3155160260252760967830155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8413760694007362580880413 3155160260252760967830155)
              ·
                refine ⟨4732740390379141451745233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155160260252760967830155 4732740390379141451745233)
                ·
                  refine ⟨3549555292784356088808925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4732740390379141451745233 3549555292784356088808925)
                  ·
                    refine ⟨1331083234794133533303347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549555292784356088808925 1331083234794133533303347)
                    ·
                      rfl

theorem cell22_3888413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_3888413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888413 prefixEnd_3888413 := by exact prefixLift 3888413
  have htrace : WordTrace (prefixWord ++ tailWord_3888413) baseStart_3888413 baseEnd_3888413 := by
    simpa [prefixWord, tailWord_3888413, baseEnd_3888413] using wordTrace_append hprefix tailTrace_3888413
  have hstable : (prefixWord ++ tailWord_3888413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888413).length < 2 ^ (prefixWord ++ tailWord_3888413).sum := by decide
  have hdescent : baseEnd_3888413 < baseStart_3888413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888426 : List Nat := [3, 1, 4, 2, 1, 3, 2, 6]
def baseStart_3888426 : Nat := 118140960795 + 3888426 * 2 ^ 59
def prefixEnd_3888426 : Nat := 4983230072969 + 3 ^ 40 * 3888426 * 2
def baseEnd_3888426 : Nat := 147898631662200648080923

theorem tailTrace_3888426 : CollatzResearch.WordTrace tailWord_3888426 prefixEnd_3888426 147898631662200648080923 := by
  unfold tailWord_3888426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35455636852726041783745283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94548364940602778089987421 35455636852726041783745283)
  ·
    refine ⟨53183455279089062675617925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35455636852726041783745283 53183455279089062675617925)
    ·
      refine ⟨9971897864829199251678361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53183455279089062675617925 9971897864829199251678361)
      ·
        refine ⟨7478923398621899438758771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9971897864829199251678361 7478923398621899438758771)
        ·
          refine ⟨11218385097932849158138157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7478923398621899438758771 11218385097932849158138157)
          ·
            refine ⟨4206894411724818434301809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11218385097932849158138157 4206894411724818434301809)
            ·
              refine ⟨3155170808793613825726357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4206894411724818434301809 3155170808793613825726357)
              ·
                refine ⟨147898631662200648080923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3155170808793613825726357 147898631662200648080923)
                ·
                  rfl

theorem cell22_3888426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_3888426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888426 prefixEnd_3888426 := by exact prefixLift 3888426
  have htrace : WordTrace (prefixWord ++ tailWord_3888426) baseStart_3888426 baseEnd_3888426 := by
    simpa [prefixWord, tailWord_3888426, baseEnd_3888426] using wordTrace_append hprefix tailTrace_3888426
  have hstable : (prefixWord ++ tailWord_3888426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888426).length < 2 ^ (prefixWord ++ tailWord_3888426).sum := by decide
  have hdescent : baseEnd_3888426 < baseStart_3888426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888437 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 7]
def baseStart_3888437 : Nat := 118140960795 + 3888437 * 2 ^ 59
def prefixEnd_3888437 : Nat := 4983230072969 + 3 ^ 40 * 3888437 * 2
def baseEnd_3888437 : Nat := 443697150161535156901091

theorem tailTrace_3888437 : CollatzResearch.WordTrace tailWord_3888437 prefixEnd_3888437 443697150161535156901091 := by
  unfold tailWord_3888437
  simp only [CollatzResearch.WordTrace]
  refine ⟨141822948613864316013631565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94548632409242877342421043 141822948613864316013631565)
  ·
    refine ⟨53183605730199118505111837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141822948613864316013631565 53183605730199118505111837)
    ·
      refine ⟨19943852148824669439416939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53183605730199118505111837 19943852148824669439416939)
      ·
        refine ⟨29915778223237004159125409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19943852148824669439416939 29915778223237004159125409)
        ·
          refine ⟨22436833667427753119344057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29915778223237004159125409 22436833667427753119344057)
          ·
            refine ⟨16827625250570814839508043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22436833667427753119344057 16827625250570814839508043)
            ·
              refine ⟨25241437875856222259262065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16827625250570814839508043 25241437875856222259262065)
              ·
                refine ⟨18931078406892166694446549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25241437875856222259262065 18931078406892166694446549)
                ·
                  refine ⟨443697150161535156901091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18931078406892166694446549 443697150161535156901091)
                  ·
                    rfl

theorem cell22_3888437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_3888437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888437 prefixEnd_3888437 := by exact prefixLift 3888437
  have htrace : WordTrace (prefixWord ++ tailWord_3888437) baseStart_3888437 baseEnd_3888437 := by
    simpa [prefixWord, tailWord_3888437, baseEnd_3888437] using wordTrace_append hprefix tailTrace_3888437
  have hstable : (prefixWord ++ tailWord_3888437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888437).length < 2 ^ (prefixWord ++ tailWord_3888437).sum := by decide
  have hdescent : baseEnd_3888437 < baseStart_3888437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888467 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_3888467 : Nat := 118140960795 + 3888467 * 2 ^ 59
def prefixEnd_3888467 : Nat := 4983230072969 + 3 ^ 40 * 3888467 * 2
def baseEnd_3888467 : Nat := 1331101720097695392453181

theorem tailTrace_3888467 : CollatzResearch.WordTrace tailWord_3888467 prefixEnd_3888467 1331101720097695392453181 := by
  unfold tailWord_3888467
  simp only [CollatzResearch.WordTrace]
  refine ⟨141824042803755631137223655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94549361869170420758149103 141824042803755631137223655)
  ·
    refine ⟨212736064205633446705835483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141824042803755631137223655 212736064205633446705835483)
    ·
      refine ⟨319104096308450170058753225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212736064205633446705835483 319104096308450170058753225)
      ·
        refine ⟨239328072231337627544064919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319104096308450170058753225 239328072231337627544064919)
        ·
          refine ⟨358992108347006441316097379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239328072231337627544064919 358992108347006441316097379)
          ·
            refine ⟨538488162520509661974146069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358992108347006441316097379 538488162520509661974146069)
            ·
              refine ⟨25241632618148890405038097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 538488162520509661974146069 25241632618148890405038097)
              ·
                refine ⟨18931224463611667803778573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25241632618148890405038097 18931224463611667803778573)
                ·
                  refine ⟨7099209173854375426416965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18931224463611667803778573 7099209173854375426416965)
                  ·
                    refine ⟨1331101720097695392453181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099209173854375426416965 1331101720097695392453181)
                    ·
                      rfl

theorem cell22_3888467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_3888467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888467 prefixEnd_3888467 := by exact prefixLift 3888467
  have htrace : WordTrace (prefixWord ++ tailWord_3888467) baseStart_3888467 baseEnd_3888467 := by
    simpa [prefixWord, tailWord_3888467, baseEnd_3888467] using wordTrace_append hprefix tailTrace_3888467
  have hstable : (prefixWord ++ tailWord_3888467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888467).length < 2 ^ (prefixWord ++ tailWord_3888467).sum := by decide
  have hdescent : baseEnd_3888467 < baseStart_3888467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888471 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 5]
def baseStart_3888471 : Nat := 118140960795 + 3888471 * 2 ^ 59
def prefixEnd_3888471 : Nat := 4983230072969 + 3 ^ 40 * 3888471 * 2
def baseEnd_3888471 : Nat := 443701029793146905117723

theorem tailTrace_3888471 : CollatzResearch.WordTrace tailWord_3888471 prefixEnd_3888471 443701029793146905117723 := by
  unfold tailWord_3888471
  simp only [CollatzResearch.WordTrace]
  refine ⟨141824188695741139820369267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94549459130494093213579511 141824188695741139820369267)
  ·
    refine ⟨212736283043611709730553901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141824188695741139820369267 212736283043611709730553901)
    ·
      refine ⟨79776106141354391148957713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212736283043611709730553901 79776106141354391148957713)
      ·
        refine ⟨59832079606015793361718285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79776106141354391148957713 59832079606015793361718285)
        ·
          refine ⟨22437029852255922510644357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59832079606015793361718285 22437029852255922510644357)
          ·
            refine ⟨4206943097297985470745817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22437029852255922510644357 4206943097297985470745817)
            ·
              refine ⟨3155207322973489103059363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4206943097297985470745817 3155207322973489103059363)
              ·
                refine ⟨4732810984460233654589045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155207322973489103059363 4732810984460233654589045)
                ·
                  refine ⟨443701029793146905117723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4732810984460233654589045 443701029793146905117723)
                  ·
                    rfl

theorem cell22_3888471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 5].length) (baseStart_3888471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888471 prefixEnd_3888471 := by exact prefixLift 3888471
  have htrace : WordTrace (prefixWord ++ tailWord_3888471) baseStart_3888471 baseEnd_3888471 := by
    simpa [prefixWord, tailWord_3888471, baseEnd_3888471] using wordTrace_append hprefix tailTrace_3888471
  have hstable : (prefixWord ++ tailWord_3888471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888471).length < 2 ^ (prefixWord ++ tailWord_3888471).sum := by decide
  have hdescent : baseEnd_3888471 < baseStart_3888471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888484 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_3888484 : Nat := 118140960795 + 3888484 * 2 ^ 59
def prefixEnd_3888484 : Nat := 4983230072969 + 3 ^ 40 * 3888484 * 2
def baseEnd_3888484 : Nat := 1331107539545113014778129

theorem tailTrace_3888484 : CollatzResearch.WordTrace tailWord_3888484 prefixEnd_3888484 1331107539545113014778129 := by
  unfold tailWord_3888484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70912331422347021520296253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94549775229796028693728337 70912331422347021520296253)
  ·
    refine ⟨26592124283380133070111095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70912331422347021520296253 26592124283380133070111095)
    ·
      refine ⟨39888186425070199605166643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26592124283380133070111095 39888186425070199605166643)
      ·
        refine ⟨59832279637605299407749965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39888186425070199605166643 59832279637605299407749965)
        ·
          refine ⟨22437104864101987277906237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59832279637605299407749965 22437104864101987277906237)
          ·
            refine ⟨8413914324038245229214839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22437104864101987277906237 8413914324038245229214839)
            ·
              refine ⟨12620871486057367843822259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413914324038245229214839 12620871486057367843822259)
              ·
                refine ⟨18931307229086051765733389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12620871486057367843822259 18931307229086051765733389)
                ·
                  refine ⟨7099240210907269412150021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18931307229086051765733389 7099240210907269412150021)
                  ·
                    refine ⟨1331107539545113014778129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099240210907269412150021 1331107539545113014778129)
                    ·
                      rfl

theorem cell22_3888484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_3888484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888484 prefixEnd_3888484 := by exact prefixLift 3888484
  have htrace : WordTrace (prefixWord ++ tailWord_3888484) baseStart_3888484 baseEnd_3888484 := by
    simpa [prefixWord, tailWord_3888484, baseEnd_3888484] using wordTrace_append hprefix tailTrace_3888484
  have hstable : (prefixWord ++ tailWord_3888484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888484).length < 2 ^ (prefixWord ++ tailWord_3888484).sum := by decide
  have hdescent : baseEnd_3888484 < baseStart_3888484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888497 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_3888497 : Nat := 118140960795 + 3888497 * 2 ^ 59
def prefixEnd_3888497 : Nat := 4983230072969 + 3 ^ 40 * 3888497 * 2
def baseEnd_3888497 : Nat := 1331111989710785314203089

theorem tailTrace_3888497 : CollatzResearch.WordTrace tailWord_3888497 prefixEnd_3888497 1331111989710785314203089 := by
  unfold tailWord_3888497
  simp only [CollatzResearch.WordTrace]
  refine ⟨141825136993646946260815745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94550091329097964173877163 141825136993646946260815745)
  ·
    refine ⟨106368852745235209695611809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141825136993646946260815745 106368852745235209695611809)
    ·
      refine ⟨79776639558926407271708857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106368852745235209695611809 79776639558926407271708857)
      ·
        refine ⟨59832479669194805453781643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79776639558926407271708857 59832479669194805453781643)
        ·
          refine ⟨89748719503792208180672465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59832479669194805453781643 89748719503792208180672465)
          ·
            refine ⟨67311539627844156135504349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89748719503792208180672465 67311539627844156135504349)
            ·
              refine ⟨25241827360441558550814131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67311539627844156135504349 25241827360441558550814131)
              ·
                refine ⟨37862741040662337826221197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25241827360441558550814131 37862741040662337826221197)
                ·
                  refine ⟨14198527890248376684832949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37862741040662337826221197 14198527890248376684832949)
                  ·
                    refine ⟨1331111989710785314203089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14198527890248376684832949 1331111989710785314203089)
                    ·
                      rfl

theorem cell22_3888497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_3888497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888497 prefixEnd_3888497 := by exact prefixLift 3888497
  have htrace : WordTrace (prefixWord ++ tailWord_3888497) baseStart_3888497 baseEnd_3888497 := by
    simpa [prefixWord, tailWord_3888497, baseEnd_3888497] using wordTrace_append hprefix tailTrace_3888497
  have hstable : (prefixWord ++ tailWord_3888497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888497).length < 2 ^ (prefixWord ++ tailWord_3888497).sum := by decide
  have hdescent : baseEnd_3888497 < baseStart_3888497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888516 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3888516 : Nat := 118140960795 + 3888516 * 2 ^ 59
def prefixEnd_3888516 : Nat := 4983230072969 + 3 ^ 40 * 3888516 * 2
def baseEnd_3888516 : Nat := 443706164599691865992677

theorem tailTrace_3888516 : CollatzResearch.WordTrace tailWord_3888516 prefixEnd_3888516 443706164599691865992677 := by
  unfold tailWord_3888516
  simp only [CollatzResearch.WordTrace]
  refine ⟨70912914990289056252878701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94550553320385408337171601 70912914990289056252878701)
  ·
    refine ⟨26592343121358396094829513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70912914990289056252878701 26592343121358396094829513)
    ·
      refine ⟨19944257341018797071122135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26592343121358396094829513 19944257341018797071122135)
      ·
        refine ⟨29916386011528195606683203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19944257341018797071122135 29916386011528195606683203)
        ·
          refine ⟨44874579017292293410024805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29916386011528195606683203 44874579017292293410024805)
          ·
            refine ⟨8413983565742305014379651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44874579017292293410024805 8413983565742305014379651)
            ·
              refine ⟨12620975348613457521569477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8413983565742305014379651 12620975348613457521569477)
              ·
                refine ⟨2366432877865023285294277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12620975348613457521569477 2366432877865023285294277)
                ·
                  refine ⟨443706164599691865992677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366432877865023285294277 443706164599691865992677)
                  ·
                    rfl

theorem cell22_3888516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3888516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888516 prefixEnd_3888516 := by exact prefixLift 3888516
  have htrace : WordTrace (prefixWord ++ tailWord_3888516) baseStart_3888516 baseEnd_3888516 := by
    simpa [prefixWord, tailWord_3888516, baseEnd_3888516] using wordTrace_append hprefix tailTrace_3888516
  have hstable : (prefixWord ++ tailWord_3888516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888516).length < 2 ^ (prefixWord ++ tailWord_3888516).sum := by decide
  have hdescent : baseEnd_3888516 < baseStart_3888516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888544 : List Nat := [2, 1, 1, 4, 1, 2, 5, 6]
def baseStart_3888544 : Nat := 118140960795 + 3888544 * 2 ^ 59
def prefixEnd_3888544 : Nat := 4983230072969 + 3 ^ 40 * 3888544 * 2
def baseEnd_3888544 : Nat := 147903119863476984253105

theorem tailTrace_3888544 : CollatzResearch.WordTrace tailWord_3888544 prefixEnd_3888544 147903119863476984253105 := by
  unfold tailWord_3888544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70913425612238336643888343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94551234149651115525184457 70913425612238336643888343)
  ·
    refine ⟨106370138418357504965832515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70913425612238336643888343 106370138418357504965832515)
    ·
      refine ⟨159555207627536257448748773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106370138418357504965832515 159555207627536257448748773)
      ·
        refine ⟨29916601430163048271640395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159555207627536257448748773 29916601430163048271640395)
        ·
          refine ⟨44874902145244572407460593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29916601430163048271640395 44874902145244572407460593)
          ·
            refine ⟨33656176608933429305595445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44874902145244572407460593 33656176608933429305595445)
            ·
              refine ⟨3155266557087508997399573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33656176608933429305595445 3155266557087508997399573)
              ·
                refine ⟨147903119863476984253105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3155266557087508997399573 147903119863476984253105)
                ·
                  rfl

theorem cell22_3888544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_3888544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888544 prefixEnd_3888544 := by exact prefixLift 3888544
  have htrace : WordTrace (prefixWord ++ tailWord_3888544) baseStart_3888544 baseEnd_3888544 := by
    simpa [prefixWord, tailWord_3888544, baseEnd_3888544] using wordTrace_append hprefix tailTrace_3888544
  have hstable : (prefixWord ++ tailWord_3888544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888544).length < 2 ^ (prefixWord ++ tailWord_3888544).sum := by decide
  have hdescent : baseEnd_3888544 < baseStart_3888544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888546 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3888546 : Nat := 118140960795 + 3888546 * 2 ^ 59
def prefixEnd_3888546 : Nat := 4983230072969 + 3 ^ 40 * 3888546 * 2
def baseEnd_3888546 : Nat := 1331128763412165519727939

theorem tailTrace_3888546 : CollatzResearch.WordTrace tailWord_3888546 prefixEnd_3888546 1331128763412165519727939 := by
  unfold tailWord_3888546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35456731042617356907337373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94551282780312951752899661 35456731042617356907337373)
  ·
    refine ⟨13296274140981508840251515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35456731042617356907337373 13296274140981508840251515)
    ·
      refine ⟨19944411211472263260377273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13296274140981508840251515 19944411211472263260377273)
      ·
        refine ⟨14958308408604197445282955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19944411211472263260377273 14958308408604197445282955)
        ·
          refine ⟨22437462612906296167924433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14958308408604197445282955 22437462612906296167924433)
          ·
            refine ⟨16828096959679722125943325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22437462612906296167924433 16828096959679722125943325)
            ·
              refine ⟨6310536359879895797228747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16828096959679722125943325 6310536359879895797228747)
              ·
                refine ⟨9465804539819843695843121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6310536359879895797228747 9465804539819843695843121)
                ·
                  refine ⟨7099353404864882771882341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9465804539819843695843121 7099353404864882771882341)
                  ·
                    refine ⟨1331128763412165519727939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099353404864882771882341 1331128763412165519727939)
                    ·
                      rfl

theorem cell22_3888546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3888546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888546 prefixEnd_3888546 := by exact prefixLift 3888546
  have htrace : WordTrace (prefixWord ++ tailWord_3888546) baseStart_3888546 baseEnd_3888546 := by
    simpa [prefixWord, tailWord_3888546, baseEnd_3888546] using wordTrace_append hprefix tailTrace_3888546
  have hstable : (prefixWord ++ tailWord_3888546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888546).length < 2 ^ (prefixWord ++ tailWord_3888546).sum := by decide
  have hdescent : baseEnd_3888546 < baseStart_3888546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888552 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3888552 : Nat := 118140960795 + 3888552 * 2 ^ 59
def prefixEnd_3888552 : Nat := 4983230072969 + 3 ^ 40 * 3888552 * 2
def baseEnd_3888552 : Nat := 1331130817334783504077921

theorem tailTrace_3888552 : CollatzResearch.WordTrace tailWord_3888552 prefixEnd_3888552 1331130817334783504077921 := by
  unfold tailWord_3888552
  simp only [CollatzResearch.WordTrace]
  refine ⟨70913571504223845327033955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94551428672298460436045273 70913571504223845327033955)
  ·
    refine ⟨106370357256335767990550933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70913571504223845327033955 106370357256335767990550933)
    ·
      refine ⟨4986110496390739124557075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106370357256335767990550933 4986110496390739124557075)
      ·
        refine ⟨7479165744586108686835613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986110496390739124557075 7479165744586108686835613)
        ·
          refine ⟨2804687154219790757563355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7479165744586108686835613 2804687154219790757563355)
          ·
            refine ⟨4207030731329686136345033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804687154219790757563355 4207030731329686136345033)
            ·
              refine ⟨3155273048497264602258775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4207030731329686136345033 3155273048497264602258775)
              ·
                refine ⟨4732909572745896903388163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3155273048497264602258775 4732909572745896903388163)
                ·
                  refine ⟨7099364359118845355082245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4732909572745896903388163 7099364359118845355082245)
                  ·
                    refine ⟨1331130817334783504077921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099364359118845355082245 1331130817334783504077921)
                    ·
                      rfl

theorem cell22_3888552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3888552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888552 prefixEnd_3888552 := by exact prefixLift 3888552
  have htrace : WordTrace (prefixWord ++ tailWord_3888552) baseStart_3888552 baseEnd_3888552 := by
    simpa [prefixWord, tailWord_3888552, baseEnd_3888552] using wordTrace_append hprefix tailTrace_3888552
  have hstable : (prefixWord ++ tailWord_3888552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888552).length < 2 ^ (prefixWord ++ tailWord_3888552).sum := by decide
  have hdescent : baseEnd_3888552 < baseStart_3888552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888649 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_3888649 : Nat := 118140960795 + 3888649 * 2 ^ 59
def prefixEnd_3888649 : Nat := 4983230072969 + 3 ^ 40 * 3888649 * 2
def baseEnd_3888649 : Nat := 1331164022417107584402623

theorem tailTrace_3888649 : CollatzResearch.WordTrace tailWord_3888649 prefixEnd_3888649 1331164022417107584402623 := by
  unfold tailWord_3888649
  simp only [CollatzResearch.WordTrace]
  refine ⟨141830680889096276220349001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94553787259397517480232667 141830680889096276220349001)
  ·
    refine ⟨106373010666822207165261751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141830680889096276220349001 106373010666822207165261751)
    ·
      refine ⟨159559516000233310747892627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106373010666822207165261751 159559516000233310747892627)
      ·
        refine ⟨239339274000349966121838941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159559516000233310747892627 239339274000349966121838941)
        ·
          refine ⟨89752227750131237295689603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239339274000349966121838941 89752227750131237295689603)
          ·
            refine ⟨134628341625196855943534405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89752227750131237295689603 134628341625196855943534405)
            ·
              refine ⟨25242814054724410489412701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134628341625196855943534405 25242814054724410489412701)
              ·
                refine ⟨9466055270521653933529763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25242814054724410489412701 9466055270521653933529763)
                ·
                  refine ⟨14199082905782480900294645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9466055270521653933529763 14199082905782480900294645)
                  ·
                    refine ⟨1331164022417107584402623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14199082905782480900294645 1331164022417107584402623)
                    ·
                      rfl

theorem cell22_3888649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_3888649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888649 prefixEnd_3888649 := by exact prefixLift 3888649
  have htrace : WordTrace (prefixWord ++ tailWord_3888649) baseStart_3888649 baseEnd_3888649 := by
    simpa [prefixWord, tailWord_3888649, baseEnd_3888649] using wordTrace_append hprefix tailTrace_3888649
  have hstable : (prefixWord ++ tailWord_3888649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888649).length < 2 ^ (prefixWord ++ tailWord_3888649).sum := by decide
  have hdescent : baseEnd_3888649 < baseStart_3888649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888679 : List Nat := [1, 1, 7, 13]
def baseStart_3888679 : Nat := 118140960795 + 3888679 * 2 ^ 59
def prefixEnd_3888679 : Nat := 4983230072969 + 3 ^ 40 * 3888679 * 2
def baseEnd_3888679 : Nat := 1826027835432369692939

theorem tailTrace_3888679 : CollatzResearch.WordTrace tailWord_3888679 prefixEnd_3888679 1826027835432369692939 := by
  unfold tailWord_3888679
  simp only [CollatzResearch.WordTrace]
  refine ⟨141831775078987591343941091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94554516719325060895960727 141831775078987591343941091)
  ·
    refine ⟨212747662618481387015911637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141831775078987591343941091 212747662618481387015911637)
    ·
      refine ⟨4986273342620657508185429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 212747662618481387015911637 4986273342620657508185429)
      ·
        refine ⟨1826027835432369692939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4986273342620657508185429 1826027835432369692939)
        ·
          rfl

theorem cell22_3888679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 13].length) (baseStart_3888679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888679 prefixEnd_3888679 := by exact prefixLift 3888679
  have htrace : WordTrace (prefixWord ++ tailWord_3888679) baseStart_3888679 baseEnd_3888679 := by
    simpa [prefixWord, tailWord_3888679, baseEnd_3888679] using wordTrace_append hprefix tailTrace_3888679
  have hstable : (prefixWord ++ tailWord_3888679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888679).length < 2 ^ (prefixWord ++ tailWord_3888679).sum := by decide
  have hdescent : baseEnd_3888679 < baseStart_3888679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888696 : List Nat := [2, 1, 2, 1, 4, 4, 1, 7]
def baseStart_3888696 : Nat := 118140960795 + 3888696 * 2 ^ 59
def prefixEnd_3888696 : Nat := 4983230072969 + 3 ^ 40 * 3888696 * 2
def baseEnd_3888696 : Nat := 147908901275290569830831

theorem tailTrace_3888696 : CollatzResearch.WordTrace tailWord_3888696 prefixEnd_3888696 147908901275290569830831 := by
  unfold tailWord_3888696
  simp only [CollatzResearch.WordTrace]
  refine ⟨70916197559963001623654971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94554930079950668831539961 70916197559963001623654971)
  ·
    refine ⟨106374296339944502435482457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70916197559963001623654971 106374296339944502435482457)
    ·
      refine ⟨79780722254958376826611843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106374296339944502435482457 79780722254958376826611843)
      ·
        refine ⟨119671083382437565239917765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79780722254958376826611843 119671083382437565239917765)
        ·
          refine ⟨22438328134207043482484581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119671083382437565239917765 22438328134207043482484581)
          ·
            refine ⟨4207186525163820652965859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22438328134207043482484581 4207186525163820652965859)
            ·
              refine ⟨6310779787745730979448789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207186525163820652965859 6310779787745730979448789)
              ·
                refine ⟨147908901275290569830831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6310779787745730979448789 147908901275290569830831)
                ·
                  rfl

theorem cell22_3888696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 7].length) (baseStart_3888696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888696 prefixEnd_3888696 := by exact prefixLift 3888696
  have htrace : WordTrace (prefixWord ++ tailWord_3888696) baseStart_3888696 baseEnd_3888696 := by
    simpa [prefixWord, tailWord_3888696, baseEnd_3888696] using wordTrace_append hprefix tailTrace_3888696
  have hstable : (prefixWord ++ tailWord_3888696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888696).length < 2 ^ (prefixWord ++ tailWord_3888696).sum := by decide
  have hdescent : baseEnd_3888696 < baseStart_3888696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888709 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3888709 : Nat := 118140960795 + 3888709 * 2 ^ 59
def prefixEnd_3888709 : Nat := 4983230072969 + 3 ^ 40 * 3888709 * 2
def baseEnd_3888709 : Nat := 1331184561643287427902439

theorem tailTrace_3888709 : CollatzResearch.WordTrace tailWord_3888709 prefixEnd_3888709 1331184561643287427902439 := by
  unfold tailWord_3888709
  simp only [CollatzResearch.WordTrace]
  refine ⟨141832869268878906467533181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94555246179252604311688787 141832869268878906467533181)
  ·
    refine ⟨53187325975829589925324943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141832869268878906467533181 53187325975829589925324943)
    ·
      refine ⟨79780988963744384887987415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53187325975829589925324943 79780988963744384887987415)
      ·
        refine ⟨119671483445616577331981123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79780988963744384887987415 119671483445616577331981123)
        ·
          refine ⟨179507225168424865997971685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119671483445616577331981123 179507225168424865997971685)
          ·
            refine ⟨33657604719079662374619691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179507225168424865997971685 33657604719079662374619691)
            ·
              refine ⟨50486407078619493561929537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33657604719079662374619691 50486407078619493561929537)
              ·
                refine ⟨37864805308964620171447153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50486407078619493561929537 37864805308964620171447153)
                ·
                  refine ⟨28398603981723465128585365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37864805308964620171447153 28398603981723465128585365)
                  ·
                    refine ⟨1331184561643287427902439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28398603981723465128585365 1331184561643287427902439)
                    ·
                      rfl

theorem cell22_3888709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3888709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888709 prefixEnd_3888709 := by exact prefixLift 3888709
  have htrace : WordTrace (prefixWord ++ tailWord_3888709) baseStart_3888709 baseEnd_3888709 := by
    simpa [prefixWord, tailWord_3888709, baseEnd_3888709] using wordTrace_append hprefix tailTrace_3888709
  have hstable : (prefixWord ++ tailWord_3888709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888709).length < 2 ^ (prefixWord ++ tailWord_3888709).sum := by decide
  have hdescent : baseEnd_3888709 < baseStart_3888709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888741 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 7]
def baseStart_3888741 : Nat := 118140960795 + 3888741 * 2 ^ 59
def prefixEnd_3888741 : Nat := 4983230072969 + 3 ^ 40 * 3888741 * 2
def baseEnd_3888741 : Nat := 443731838632416670367447

theorem tailTrace_3888741 : CollatzResearch.WordTrace tailWord_3888741 prefixEnd_3888741 443731838632416670367447 := by
  unfold tailWord_3888741
  simp only [CollatzResearch.WordTrace]
  refine ⟨141834036404762975932698077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94556024269841983955132051 141834036404762975932698077)
  ·
    refine ⟨53187763651786115974761779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141834036404762975932698077 53187763651786115974761779)
    ·
      refine ⟨79781645477679173962142669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53187763651786115974761779 79781645477679173962142669)
      ·
        refine ⟨29918117054129690235803501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79781645477679173962142669 29918117054129690235803501)
        ·
          refine ⟨11219293895298633838426313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29918117054129690235803501 11219293895298633838426313)
          ·
            refine ⟨8414470421473975378819735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11219293895298633838426313 8414470421473975378819735)
            ·
              refine ⟨12621705632210963068229603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414470421473975378819735 12621705632210963068229603)
              ·
                refine ⟨18932558448316444602344405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12621705632210963068229603 18932558448316444602344405)
                ·
                  refine ⟨443731838632416670367447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18932558448316444602344405 443731838632416670367447)
                  ·
                    rfl

theorem cell22_3888741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_3888741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888741 prefixEnd_3888741 := by exact prefixLift 3888741
  have htrace : WordTrace (prefixWord ++ tailWord_3888741) baseStart_3888741 baseEnd_3888741 := by
    simpa [prefixWord, tailWord_3888741, baseEnd_3888741] using wordTrace_append hprefix tailTrace_3888741
  have hstable : (prefixWord ++ tailWord_3888741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888741).length < 2 ^ (prefixWord ++ tailWord_3888741).sum := by decide
  have hdescent : baseEnd_3888741 < baseStart_3888741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888822 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3888822 : Nat := 118140960795 + 3888822 * 2 ^ 59
def prefixEnd_3888822 : Nat := 4983230072969 + 3 ^ 40 * 3888822 * 2
def baseEnd_3888822 : Nat := 1331223243852592799827093

theorem tailTrace_3888822 : CollatzResearch.WordTrace tailWord_3888822 prefixEnd_3888822 1331223243852592799827093 := by
  unfold tailWord_3888822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864811919841845422899795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94557993811646351177597813 8864811919841845422899795)
  ·
    refine ⟨13297217879762768134349693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8864811919841845422899795 13297217879762768134349693)
    ·
      refine ⟨4986456704911038050381135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13297217879762768134349693 4986456704911038050381135)
      ·
        refine ⟨7479685057366557075571703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986456704911038050381135 7479685057366557075571703)
        ·
          refine ⟨11219527586049835613357555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479685057366557075571703 11219527586049835613357555)
          ·
            refine ⟨16829291379074753420036333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11219527586049835613357555 16829291379074753420036333)
            ·
              refine ⟨6310984267153032532513625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16829291379074753420036333 6310984267153032532513625)
              ·
                refine ⟨4733238200364774399385219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6310984267153032532513625 4733238200364774399385219)
                ·
                  refine ⟨7099857300547161599077829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733238200364774399385219 7099857300547161599077829)
                  ·
                    refine ⟨1331223243852592799827093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099857300547161599077829 1331223243852592799827093)
                    ·
                      rfl

theorem cell22_3888822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3888822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888822 prefixEnd_3888822 := by exact prefixLift 3888822
  have htrace : WordTrace (prefixWord ++ tailWord_3888822) baseStart_3888822 baseEnd_3888822 := by
    simpa [prefixWord, tailWord_3888822, baseEnd_3888822] using wordTrace_append hprefix tailTrace_3888822
  have hstable : (prefixWord ++ tailWord_3888822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888822).length < 2 ^ (prefixWord ++ tailWord_3888822).sum := by decide
  have hdescent : baseEnd_3888822 < baseStart_3888822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888852 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_3888852 : Nat := 118140960795 + 3888852 * 2 ^ 59
def prefixEnd_3888852 : Nat := 4983230072969 + 3 ^ 40 * 3888852 * 2
def baseEnd_3888852 : Nat := 1331233513465682721577001

theorem tailTrace_3888852 : CollatzResearch.WordTrace tailWord_3888852 prefixEnd_3888852 1331233513465682721577001 := by
  unfold tailWord_3888852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70919042453680420944994405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94558723271573894593325873 70919042453680420944994405)
  ·
    refine ⟨13297320460065078927186451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70919042453680420944994405 13297320460065078927186451)
    ·
      refine ⟨19945980690097618390779677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13297320460065078927186451 19945980690097618390779677)
      ·
        refine ⟨7479742758786606896542379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19945980690097618390779677 7479742758786606896542379)
        ·
          refine ⟨11219614138179910344813569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479742758786606896542379 11219614138179910344813569)
          ·
            refine ⟨8414710603634932758610177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11219614138179910344813569 8414710603634932758610177)
            ·
              refine ⟨6311032952726199568957633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8414710603634932758610177 6311032952726199568957633)
              ·
                refine ⟨4733274714544649676718225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311032952726199568957633 4733274714544649676718225)
                ·
                  refine ⟨3549956035908487257538669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733274714544649676718225 3549956035908487257538669)
                  ·
                    refine ⟨1331233513465682721577001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549956035908487257538669 1331233513465682721577001)
                    ·
                      rfl

theorem cell22_3888852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_3888852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888852 prefixEnd_3888852 := by exact prefixLift 3888852
  have htrace : WordTrace (prefixWord ++ tailWord_3888852) baseStart_3888852 baseEnd_3888852 := by
    simpa [prefixWord, tailWord_3888852, baseEnd_3888852] using wordTrace_append hprefix tailTrace_3888852
  have hstable : (prefixWord ++ tailWord_3888852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888852).length < 2 ^ (prefixWord ++ tailWord_3888852).sum := by decide
  have hdescent : baseEnd_3888852 < baseStart_3888852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888854 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3888854 : Nat := 118140960795 + 3888854 * 2 ^ 59
def prefixEnd_3888854 : Nat := 4983230072969 + 3 ^ 40 * 3888854 * 2
def baseEnd_3888854 : Nat := 443744732702185127675665

theorem tailTrace_3888854 : CollatzResearch.WordTrace tailWord_3888854 prefixEnd_3888854 443744732702185127675665 := by
  unfold tailWord_3888854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8864884865834599764472601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94558771902235730821041077 8864884865834599764472601)
  ·
    refine ⟨6648663649375949823354451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8864884865834599764472601 6648663649375949823354451)
    ·
      refine ⟨9972995474063924735031677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648663649375949823354451 9972995474063924735031677)
      ·
        refine ⟨3739873302773971775636879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9972995474063924735031677 3739873302773971775636879)
        ·
          refine ⟨5609809954160957663455319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3739873302773971775636879 5609809954160957663455319)
          ·
            refine ⟨8414714931241436495182979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5609809954160957663455319 8414714931241436495182979)
            ·
              refine ⟨12622072396862154742774469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8414714931241436495182979 12622072396862154742774469)
              ·
                refine ⟨2366638574411654014270213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12622072396862154742774469 2366638574411654014270213)
                ·
                  refine ⟨443744732702185127675665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2366638574411654014270213 443744732702185127675665)
                  ·
                    rfl

theorem cell22_3888854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3888854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888854 prefixEnd_3888854 := by exact prefixLift 3888854
  have htrace : WordTrace (prefixWord ++ tailWord_3888854) baseStart_3888854 baseEnd_3888854 := by
    simpa [prefixWord, tailWord_3888854, baseEnd_3888854] using wordTrace_append hprefix tailTrace_3888854
  have hstable : (prefixWord ++ tailWord_3888854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888854).length < 2 ^ (prefixWord ++ tailWord_3888854).sum := by decide
  have hdescent : baseEnd_3888854 < baseStart_3888854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888863 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 3, 3]
def baseStart_3888863 : Nat := 118140960795 + 3888863 * 2 ^ 59
def prefixEnd_3888863 : Nat := 4983230072969 + 3 ^ 40 * 3888863 * 2
def baseEnd_3888863 : Nat := 1331237278990482359551967

theorem tailTrace_3888863 : CollatzResearch.WordTrace tailWord_3888863 prefixEnd_3888863 1331237278990482359551967 := by
  unfold tailWord_3888863
  simp only [CollatzResearch.WordTrace]
  refine ⟨141838486110320990768639243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94558990740213993845759495 141838486110320990768639243)
  ·
    refine ⟨212757729165481486152958865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141838486110320990768639243 212757729165481486152958865)
    ·
      refine ⟨159568296874111114614719149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212757729165481486152958865 159568296874111114614719149)
      ·
        refine ⟨59838111327791667980519681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159568296874111114614719149 59838111327791667980519681)
        ·
          refine ⟨44878583495843750985389761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59838111327791667980519681 44878583495843750985389761)
          ·
            refine ⟨33658937621882813239042321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44878583495843750985389761 33658937621882813239042321)
            ·
              refine ⟨25244203216412109929281741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33658937621882813239042321 25244203216412109929281741)
              ·
                refine ⟨9466576206154541223480653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25244203216412109929281741 9466576206154541223480653)
                ·
                  refine ⟨3549966077307952958805245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9466576206154541223480653 3549966077307952958805245)
                  ·
                    refine ⟨1331237278990482359551967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3549966077307952958805245 1331237278990482359551967)
                    ·
                      rfl

theorem cell22_3888863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_3888863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888863 prefixEnd_3888863 := by exact prefixLift 3888863
  have htrace : WordTrace (prefixWord ++ tailWord_3888863) baseStart_3888863 baseEnd_3888863 := by
    simpa [prefixWord, tailWord_3888863, baseEnd_3888863] using wordTrace_append hprefix tailTrace_3888863
  have hstable : (prefixWord ++ tailWord_3888863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888863).length < 2 ^ (prefixWord ++ tailWord_3888863).sum := by decide
  have hdescent : baseEnd_3888863 < baseStart_3888863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888865 : List Nat := [1, 2, 3, 1, 6, 1, 1, 7]
def baseStart_3888865 : Nat := 118140960795 + 3888865 * 2 ^ 59
def prefixEnd_3888865 : Nat := 4983230072969 + 3 ^ 40 * 3888865 * 2
def baseEnd_3888865 : Nat := 147915329292372780111329

theorem tailTrace_3888865 : CollatzResearch.WordTrace tailWord_3888865 prefixEnd_3888865 147915329292372780111329 := by
  unfold tailWord_3888865
  simp only [CollatzResearch.WordTrace]
  refine ⟨141838559056313745110212049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94559039370875830073474699 141838559056313745110212049)
  ·
    refine ⟨106378919292235308832659037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141838559056313745110212049 106378919292235308832659037)
    ·
      refine ⟨39892094734588240812247139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106378919292235308832659037 39892094734588240812247139)
      ·
        refine ⟨59838142101882361218370709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39892094734588240812247139 59838142101882361218370709)
        ·
          refine ⟨2804912911025735682111127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59838142101882361218370709 2804912911025735682111127)
          ·
            refine ⟨4207369366538603523166691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804912911025735682111127 4207369366538603523166691)
            ·
              refine ⟨6311054049807905284750037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207369366538603523166691 6311054049807905284750037)
              ·
                refine ⟨147915329292372780111329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6311054049807905284750037 147915329292372780111329)
                ·
                  rfl

theorem cell22_3888865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 7].length) (baseStart_3888865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888865 prefixEnd_3888865 := by exact prefixLift 3888865
  have htrace : WordTrace (prefixWord ++ tailWord_3888865) baseStart_3888865 baseEnd_3888865 := by
    simpa [prefixWord, tailWord_3888865, baseEnd_3888865] using wordTrace_append hprefix tailTrace_3888865
  have hstable : (prefixWord ++ tailWord_3888865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888865).length < 2 ^ (prefixWord ++ tailWord_3888865).sum := by decide
  have hdescent : baseEnd_3888865 < baseStart_3888865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888884 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_3888884 : Nat := 118140960795 + 3888884 * 2 ^ 59
def prefixEnd_3888884 : Nat := 4983230072969 + 3 ^ 40 * 3888884 * 2
def baseEnd_3888884 : Nat := 1331244467719645304776903

theorem tailTrace_3888884 : CollatzResearch.WordTrace tailWord_3888884 prefixEnd_3888884 1331244467719645304776903 := by
  unfold tailWord_3888884
  simp only [CollatzResearch.WordTrace]
  refine ⟨70919626021622455677576853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94559501362163274236769137 70919626021622455677576853)
  ·
    refine ⟨3324357469763552609886415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70919626021622455677576853 3324357469763552609886415)
    ·
      refine ⟨4986536204645328914829623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324357469763552609886415 4986536204645328914829623)
      ·
        refine ⟨7479804306967993372244435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986536204645328914829623 7479804306967993372244435)
        ·
          refine ⟨11219706460451990058366653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479804306967993372244435 11219706460451990058366653)
          ·
            refine ⟨4207389922669496271887495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11219706460451990058366653 4207389922669496271887495)
            ·
              refine ⟨6311084884004244407831243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207389922669496271887495 6311084884004244407831243)
              ·
                refine ⟨9466627326006366611746865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311084884004244407831243 9466627326006366611746865)
                ·
                  refine ⟨7099970494504774958810149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9466627326006366611746865 7099970494504774958810149)
                  ·
                    refine ⟨1331244467719645304776903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7099970494504774958810149 1331244467719645304776903)
                    ·
                      rfl

theorem cell22_3888884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_3888884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888884 prefixEnd_3888884 := by exact prefixLift 3888884
  have htrace : WordTrace (prefixWord ++ tailWord_3888884) baseStart_3888884 baseEnd_3888884 := by
    simpa [prefixWord, tailWord_3888884, baseEnd_3888884] using wordTrace_append hprefix tailTrace_3888884
  have hstable : (prefixWord ++ tailWord_3888884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888884).length < 2 ^ (prefixWord ++ tailWord_3888884).sum := by decide
  have hdescent : baseEnd_3888884 < baseStart_3888884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888914 : List Nat := [3, 2, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3888914 : Nat := 118140960795 + 3888914 * 2 ^ 59
def prefixEnd_3888914 : Nat := 4983230072969 + 3 ^ 40 * 3888914 * 2
def baseEnd_3888914 : Nat := 1331254737332735226526811

theorem tailTrace_3888914 : CollatzResearch.WordTrace tailWord_3888914 prefixEnd_3888914 1331254737332735226526811 := by
  unfold tailWord_3888914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35460086558284056619686449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94560230822090817652497197 35460086558284056619686449)
  ·
    refine ⟨26595064918713042464764837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35460086558284056619686449 26595064918713042464764837)
    ·
      refine ⟨4986574672258695462143407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26595064918713042464764837 4986574672258695462143407)
      ·
        refine ⟨7479862008388043193215111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4986574672258695462143407 7479862008388043193215111)
        ·
          refine ⟨11219793012582064789822667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7479862008388043193215111 11219793012582064789822667)
          ·
            refine ⟨16829689518873097184734001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11219793012582064789822667 16829689518873097184734001)
            ·
              refine ⟨12622267139154822888550501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16829689518873097184734001 12622267139154822888550501)
              ·
                refine ⟨2366675088591529291603219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12622267139154822888550501 2366675088591529291603219)
                ·
                  refine ⟨3550012632887293937404829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366675088591529291603219 3550012632887293937404829)
                  ·
                    refine ⟨1331254737332735226526811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550012632887293937404829 1331254737332735226526811)
                    ·
                      rfl

theorem cell22_3888914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3888914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888914 prefixEnd_3888914 := by exact prefixLift 3888914
  have htrace : WordTrace (prefixWord ++ tailWord_3888914) baseStart_3888914 baseEnd_3888914 := by
    simpa [prefixWord, tailWord_3888914, baseEnd_3888914] using wordTrace_append hprefix tailTrace_3888914
  have hstable : (prefixWord ++ tailWord_3888914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888914).length < 2 ^ (prefixWord ++ tailWord_3888914).sum := by decide
  have hdescent : baseEnd_3888914 < baseStart_3888914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888940 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_3888940 : Nat := 118140960795 + 3888940 * 2 ^ 59
def prefixEnd_3888940 : Nat := 4983230072969 + 3 ^ 40 * 3888940 * 2
def baseEnd_3888940 : Nat := 1331263637664079825376731

theorem tailTrace_3888940 : CollatzResearch.WordTrace tailWord_3888940 prefixEnd_3888940 1331263637664079825376731 := by
  unfold tailWord_3888940
  simp only [CollatzResearch.WordTrace]
  refine ⟨70920647265521016459596137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94560863020694688612794849 70920647265521016459596137)
  ·
    refine ⟨53190485449140762344697103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70920647265521016459596137 53190485449140762344697103)
    ·
      refine ⟨79785728173711143517045655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53190485449140762344697103 79785728173711143517045655)
      ·
        refine ⟨119678592260566715275568483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79785728173711143517045655 119678592260566715275568483)
        ·
          refine ⟨179517888390850072913352725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119678592260566715275568483 179517888390850072913352725)
          ·
            refine ⟨8414901018321097167813409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179517888390850072913352725 8414901018321097167813409)
            ·
              refine ⟨6311175763740822875860057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8414901018321097167813409 6311175763740822875860057)
              ·
                refine ⟨4733381822805617156895043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6311175763740822875860057 4733381822805617156895043)
                ·
                  refine ⟨7100072734208425735342565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733381822805617156895043 7100072734208425735342565)
                  ·
                    refine ⟨1331263637664079825376731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100072734208425735342565 1331263637664079825376731)
                    ·
                      rfl

theorem cell22_3888940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_3888940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888940 prefixEnd_3888940 := by exact prefixLift 3888940
  have htrace : WordTrace (prefixWord ++ tailWord_3888940) baseStart_3888940 baseEnd_3888940 := by
    simpa [prefixWord, tailWord_3888940, baseEnd_3888940] using wordTrace_append hprefix tailTrace_3888940
  have hstable : (prefixWord ++ tailWord_3888940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888940).length < 2 ^ (prefixWord ++ tailWord_3888940).sum := by decide
  have hdescent : baseEnd_3888940 < baseStart_3888940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888968 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_3888968 : Nat := 118140960795 + 3888968 * 2 ^ 59
def prefixEnd_3888968 : Nat := 4983230072969 + 3 ^ 40 * 3888968 * 2
def baseEnd_3888968 : Nat := 1331273222636297085676645

theorem tailTrace_3888968 : CollatzResearch.WordTrace tailWord_3888968 prefixEnd_3888968 1331273222636297085676645 := by
  unfold tailWord_3888968
  simp only [CollatzResearch.WordTrace]
  refine ⟨70921157887470296850605779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94561543849960395800807705 70921157887470296850605779)
  ·
    refine ⟨106381736831205445275908669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70921157887470296850605779 106381736831205445275908669)
    ·
      refine ⟨39893151311702041978465751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106381736831205445275908669 39893151311702041978465751)
      ·
        refine ⟨59839726967553062967698627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39893151311702041978465751 59839726967553062967698627)
        ·
          refine ⟨89759590451329594451547941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59839726967553062967698627 89759590451329594451547941)
          ·
            refine ⟨16829923209624298959665239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89759590451329594451547941 16829923209624298959665239)
            ·
              refine ⟨25244884814436448439497859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16829923209624298959665239 25244884814436448439497859)
              ·
                refine ⟨37867327221654672659246789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25244884814436448439497859 37867327221654672659246789)
                ·
                  refine ⟨7100123854060251123608773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37867327221654672659246789 7100123854060251123608773)
                  ·
                    refine ⟨1331273222636297085676645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100123854060251123608773 1331273222636297085676645)
                    ·
                      rfl

theorem cell22_3888968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_3888968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888968 prefixEnd_3888968 := by exact prefixLift 3888968
  have htrace : WordTrace (prefixWord ++ tailWord_3888968) baseStart_3888968 baseEnd_3888968 := by
    simpa [prefixWord, tailWord_3888968, baseEnd_3888968] using wordTrace_append hprefix tailTrace_3888968
  have hstable : (prefixWord ++ tailWord_3888968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888968).length < 2 ^ (prefixWord ++ tailWord_3888968).sum := by decide
  have hdescent : baseEnd_3888968 < baseStart_3888968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888970 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3888970 : Nat := 118140960795 + 3888970 * 2 ^ 59
def prefixEnd_3888970 : Nat := 4983230072969 + 3 ^ 40 * 3888970 * 2
def baseEnd_3888970 : Nat := 1331273907277169747126639

theorem tailTrace_3888970 : CollatzResearch.WordTrace tailWord_3888970 prefixEnd_3888970 1331273907277169747126639 := by
  unfold tailWord_3888970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35460597180233337010696091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94561592480622232028522909 35460597180233337010696091)
  ·
    refine ⟨53190895770350005516044137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35460597180233337010696091 53190895770350005516044137)
    ·
      refine ⟨39893171827762504137033103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53190895770350005516044137 39893171827762504137033103)
      ·
        refine ⟨59839757741643756205549655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39893171827762504137033103 59839757741643756205549655)
        ·
          refine ⟨89759636612465634308324483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59839757741643756205549655 89759636612465634308324483)
          ·
            refine ⟨134639454918698451462486725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89759636612465634308324483 134639454918698451462486725)
            ·
              refine ⟨25244897797255959649216261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134639454918698451462486725 25244897797255959649216261)
              ·
                refine ⟨4733418336985492434228049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25244897797255959649216261 4733418336985492434228049)
                ·
                  refine ⟨3550063752739119325671037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733418336985492434228049 3550063752739119325671037)
                  ·
                    refine ⟨1331273907277169747126639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550063752739119325671037 1331273907277169747126639)
                    ·
                      rfl

theorem cell22_3888970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3888970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888970 prefixEnd_3888970 := by exact prefixLift 3888970
  have htrace : WordTrace (prefixWord ++ tailWord_3888970) baseStart_3888970 baseEnd_3888970 := by
    simpa [prefixWord, tailWord_3888970, baseEnd_3888970] using wordTrace_append hprefix tailTrace_3888970
  have hstable : (prefixWord ++ tailWord_3888970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888970).length < 2 ^ (prefixWord ++ tailWord_3888970).sum := by decide
  have hdescent : baseEnd_3888970 < baseStart_3888970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3888972 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 6]
def baseStart_3888972 : Nat := 118140960795 + 3888972 * 2 ^ 59
def prefixEnd_3888972 : Nat := 4983230072969 + 3 ^ 40 * 3888972 * 2
def baseEnd_3888972 : Nat := 443758197306014136192211

theorem tailTrace_3888972 : CollatzResearch.WordTrace tailWord_3888972 prefixEnd_3888972 443758197306014136192211 := by
  unfold tailWord_3888972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70921230833463051192178585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94561641111284068256238113 70921230833463051192178585)
  ·
    refine ⟨53190923125097288394133939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70921230833463051192178585 53190923125097288394133939)
    ·
      refine ⟨79786384687645932591200909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53190923125097288394133939 79786384687645932591200909)
      ·
        refine ⟨29919894257867224721700341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79786384687645932591200909 29919894257867224721700341)
        ·
          refine ⟨2804990086675052317659407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29919894257867224721700341 2804990086675052317659407)
          ·
            refine ⟨4207485130012578476489111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2804990086675052317659407 4207485130012578476489111)
            ·
              refine ⟨6311227695018867714733667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4207485130012578476489111 6311227695018867714733667)
              ·
                refine ⟨9466841542528301572100501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6311227695018867714733667 9466841542528301572100501)
                ·
                  refine ⟨443758197306014136192211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9466841542528301572100501 443758197306014136192211)
                  ·
                    rfl

theorem cell22_3888972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_3888972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3888972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3888972 prefixEnd_3888972 := by exact prefixLift 3888972
  have htrace : WordTrace (prefixWord ++ tailWord_3888972) baseStart_3888972 baseEnd_3888972 := by
    simpa [prefixWord, tailWord_3888972, baseEnd_3888972] using wordTrace_append hprefix tailTrace_3888972
  have hstable : (prefixWord ++ tailWord_3888972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3888972).length < 2 ^ (prefixWord ++ tailWord_3888972).sum := by decide
  have hdescent : baseEnd_3888972 < baseStart_3888972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3888972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889028 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_3889028 : Nat := 118140960795 + 3889028 * 2 ^ 59
def prefixEnd_3889028 : Nat := 4983230072969 + 3 ^ 40 * 3889028 * 2
def baseEnd_3889028 : Nat := 443764587287492309725487

theorem tailTrace_3889028 : CollatzResearch.WordTrace tailWord_3889028 prefixEnd_3889028 443764587287492309725487 := by
  unfold tailWord_3889028
  simp only [CollatzResearch.WordTrace]
  refine ⟨70922252077361611974197869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94563002769815482632263825 70922252077361611974197869)
  ·
    refine ⟨26595844529010604490324201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70922252077361611974197869 26595844529010604490324201)
    ·
      refine ⟨19946883396757953367743151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26595844529010604490324201 19946883396757953367743151)
      ·
        refine ⟨29920325095136930051614727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19946883396757953367743151 29920325095136930051614727)
        ·
          refine ⟨44880487642705395077422091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29920325095136930051614727 44880487642705395077422091)
          ·
            refine ⟨67320731464058092616133137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44880487642705395077422091 67320731464058092616133137)
            ·
              refine ⟨50490548598043569462099853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67320731464058092616133137 50490548598043569462099853)
              ·
                refine ⟨18933955724266338548287445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50490548598043569462099853 18933955724266338548287445)
                ·
                  refine ⟨443764587287492309725487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18933955724266338548287445 443764587287492309725487)
                  ·
                    rfl

theorem cell22_3889028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_3889028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889028 prefixEnd_3889028 := by exact prefixLift 3889028
  have htrace : WordTrace (prefixWord ++ tailWord_3889028) baseStart_3889028 baseEnd_3889028 := by
    simpa [prefixWord, tailWord_3889028, baseEnd_3889028] using wordTrace_append hprefix tailTrace_3889028
  have hstable : (prefixWord ++ tailWord_3889028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889028).length < 2 ^ (prefixWord ++ tailWord_3889028).sum := by decide
  have hdescent : baseEnd_3889028 < baseStart_3889028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889075 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 1, 4]
def baseStart_3889075 : Nat := 118140960795 + 3889075 * 2 ^ 59
def prefixEnd_3889075 : Nat := 4983230072969 + 3 ^ 40 * 3889075 * 2
def baseEnd_3889075 : Nat := 1331309850922984473251317

theorem tailTrace_3889075 : CollatzResearch.WordTrace tailWord_3889075 prefixEnd_3889075 1331309850922984473251317 := by
  unfold tailWord_3889075
  simp only [CollatzResearch.WordTrace]
  refine ⟨141846218385552950975356679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94564145590368633983571119 141846218385552950975356679)
  ·
    refine ⟨212769327578329426463035019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141846218385552950975356679 212769327578329426463035019)
    ·
      refine ⟨319153991367494139694552529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212769327578329426463035019 319153991367494139694552529)
      ·
        refine ⟨239365493525620604770914397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319153991367494139694552529 239365493525620604770914397)
        ·
          refine ⟨89762060072107726789092899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239365493525620604770914397 89762060072107726789092899)
          ·
            refine ⟨134643090108161590183639349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89762060072107726789092899 134643090108161590183639349)
            ·
              refine ⟨12622789697640149079716189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134643090108161590183639349 12622789697640149079716189)
              ·
                refine ⟨4733546136615055904893571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12622789697640149079716189 4733546136615055904893571)
                ·
                  refine ⟨7100319204922583857340357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733546136615055904893571 7100319204922583857340357)
                  ·
                    refine ⟨1331309850922984473251317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100319204922583857340357 1331309850922984473251317)
                    ·
                      rfl

theorem cell22_3889075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4].length) (baseStart_3889075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889075 prefixEnd_3889075 := by exact prefixLift 3889075
  have htrace : WordTrace (prefixWord ++ tailWord_3889075) baseStart_3889075 baseEnd_3889075 := by
    simpa [prefixWord, tailWord_3889075, baseEnd_3889075] using wordTrace_append hprefix tailTrace_3889075
  have hstable : (prefixWord ++ tailWord_3889075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889075).length < 2 ^ (prefixWord ++ tailWord_3889075).sum := by decide
  have hdescent : baseEnd_3889075 < baseStart_3889075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889103 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_3889103 : Nat := 118140960795 + 3889103 * 2 ^ 59
def prefixEnd_3889103 : Nat := 4983230072969 + 3 ^ 40 * 3889103 * 2
def baseEnd_3889103 : Nat := 1331319435895201733551231

theorem tailTrace_3889103 : CollatzResearch.WordTrace tailWord_3889103 prefixEnd_3889103 1331319435895201733551231 := by
  unfold tailWord_3889103
  simp only [CollatzResearch.WordTrace]
  refine ⟨141847239629451511757375963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94564826419634341171583975 141847239629451511757375963)
  ·
    refine ⟨212770859444177267636063945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141847239629451511757375963 212770859444177267636063945)
    ·
      refine ⟨159578144583132950727047959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212770859444177267636063945 159578144583132950727047959)
      ·
        refine ⟨239367216874699426090571939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159578144583132950727047959 239367216874699426090571939)
        ·
          refine ⟨359050825312049139135857909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239367216874699426090571939 359050825312049139135857909)
          ·
            refine ⟨33661014873004606793986679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359050825312049139135857909 33661014873004606793986679)
            ·
              refine ⟨50491522309506910190980019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33661014873004606793986679 50491522309506910190980019)
              ·
                refine ⟨75737283464260365286470029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50491522309506910190980019 75737283464260365286470029)
                ·
                  refine ⟨28401481299097636982426261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75737283464260365286470029 28401481299097636982426261)
                  ·
                    refine ⟨1331319435895201733551231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28401481299097636982426261 1331319435895201733551231)
                    ·
                      rfl

theorem cell22_3889103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_3889103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889103 prefixEnd_3889103 := by exact prefixLift 3889103
  have htrace : WordTrace (prefixWord ++ tailWord_3889103) baseStart_3889103 baseEnd_3889103 := by
    simpa [prefixWord, tailWord_3889103, baseEnd_3889103] using wordTrace_append hprefix tailTrace_3889103
  have hstable : (prefixWord ++ tailWord_3889103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889103).length < 2 ^ (prefixWord ++ tailWord_3889103).sum := by decide
  have hdescent : baseEnd_3889103 < baseStart_3889103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889137 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3889137 : Nat := 118140960795 + 3889137 * 2 ^ 59
def prefixEnd_3889137 : Nat := 4983230072969 + 3 ^ 40 * 3889137 * 2
def baseEnd_3889137 : Nat := 1331331074790036978201127

theorem tailTrace_3889137 : CollatzResearch.WordTrace tailWord_3889137 prefixEnd_3889137 1331331074790036978201127 := by
  unfold tailWord_3889137
  simp only [CollatzResearch.WordTrace]
  refine ⟨141848479711328335564113665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94565653140885557042742443 141848479711328335564113665)
  ·
    refine ⟨106386359783496251673085249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141848479711328335564113665 106386359783496251673085249)
    ·
      refine ⟨79789769837622188754813937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106386359783496251673085249 79789769837622188754813937)
      ·
        refine ⟨59842327378216641566110453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79789769837622188754813937 59842327378216641566110453)
        ·
          refine ⟨5610218191707810146822855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59842327378216641566110453 5610218191707810146822855)
          ·
            refine ⟨8415327287561715220234283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610218191707810146822855 8415327287561715220234283)
            ·
              refine ⟨12622990931342572830351425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415327287561715220234283 12622990931342572830351425)
              ·
                refine ⟨9467243198506929622763569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12622990931342572830351425 9467243198506929622763569)
                ·
                  refine ⟨7100432398880197217072677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9467243198506929622763569 7100432398880197217072677)
                  ·
                    refine ⟨1331331074790036978201127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100432398880197217072677 1331331074790036978201127)
                    ·
                      rfl

theorem cell22_3889137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3889137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889137 prefixEnd_3889137 := by exact prefixLift 3889137
  have htrace : WordTrace (prefixWord ++ tailWord_3889137) baseStart_3889137 baseEnd_3889137 := by
    simpa [prefixWord, tailWord_3889137, baseEnd_3889137] using wordTrace_append hprefix tailTrace_3889137
  have hstable : (prefixWord ++ tailWord_3889137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889137).length < 2 ^ (prefixWord ++ tailWord_3889137).sum := by decide
  have hdescent : baseEnd_3889137 < baseStart_3889137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889156 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3889156 : Nat := 118140960795 + 3889156 * 2 ^ 59
def prefixEnd_3889156 : Nat := 4983230072969 + 3 ^ 40 * 3889156 * 2
def baseEnd_3889156 : Nat := 1331337578878327261976069

theorem tailTrace_3889156 : CollatzResearch.WordTrace tailWord_3889156 prefixEnd_3889156 1331337578878327261976069 := by
  unfold tailWord_3889156
  simp only [CollatzResearch.WordTrace]
  refine ⟨70924586349129750904527661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94566115132173001206036881 70924586349129750904527661)
  ·
    refine ⟨26596719880923656589197873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70924586349129750904527661 26596719880923656589197873)
    ·
      refine ⟨19947539910692742441898405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26596719880923656589197873 19947539910692742441898405)
      ·
        refine ⟨3740163733254889207855951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19947539910692742441898405 3740163733254889207855951)
        ·
          refine ⟨5610245599882333811783927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740163733254889207855951 5610245599882333811783927)
          ·
            refine ⟨8415368399823500717675891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5610245599882333811783927 8415368399823500717675891)
            ·
              refine ⟨12623052599735251076513837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415368399823500717675891 12623052599735251076513837)
              ·
                refine ⟨4733644724900719153692689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623052599735251076513837 4733644724900719153692689)
                ·
                  refine ⟨3550233543675539365269517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4733644724900719153692689 3550233543675539365269517)
                  ·
                    refine ⟨1331337578878327261976069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550233543675539365269517 1331337578878327261976069)
                    ·
                      rfl

theorem cell22_3889156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3889156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889156 prefixEnd_3889156 := by exact prefixLift 3889156
  have htrace : WordTrace (prefixWord ++ tailWord_3889156) baseStart_3889156 baseEnd_3889156 := by
    simpa [prefixWord, tailWord_3889156, baseEnd_3889156] using wordTrace_append hprefix tailTrace_3889156
  have hstable : (prefixWord ++ tailWord_3889156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889156).length < 2 ^ (prefixWord ++ tailWord_3889156).sum := by decide
  have hdescent : baseEnd_3889156 < baseStart_3889156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889201 : List Nat := [1, 2, 2, 3, 1, 3, 4, 2, 1, 3]
def baseStart_3889201 : Nat := 118140960795 + 3889201 * 2 ^ 59
def prefixEnd_3889201 : Nat := 4983230072969 + 3 ^ 40 * 3889201 * 2
def baseEnd_3889201 : Nat := 1331352983297962144600931

theorem tailTrace_3889201 : CollatzResearch.WordTrace tailWord_3889201 prefixEnd_3889201 1331352983297962144600931 := by
  unfold tailWord_3889201
  simp only [CollatzResearch.WordTrace]
  refine ⟨141850813983096474494443457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94567209322064316329628971 141850813983096474494443457)
  ·
    refine ⟨106388110487322355870832593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141850813983096474494443457 106388110487322355870832593)
    ·
      refine ⟨79791082865491766903124445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106388110487322355870832593 79791082865491766903124445)
      ·
        refine ⟨29921656074559412588671667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79791082865491766903124445 29921656074559412588671667)
        ·
          refine ⟨44882484111839118883007501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29921656074559412588671667 44882484111839118883007501)
          ·
            refine ⟨16830931541939669581127813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44882484111839118883007501 16830931541939669581127813)
            ·
              refine ⟨3155799664113688046461465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16830931541939669581127813 3155799664113688046461465)
              ·
                refine ⟨2366849748085266034846099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3155799664113688046461465 2366849748085266034846099)
                ·
                  refine ⟨3550274622127899052269149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2366849748085266034846099 3550274622127899052269149)
                  ·
                    refine ⟨1331352983297962144600931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550274622127899052269149 1331352983297962144600931)
                    ·
                      rfl

theorem cell22_3889201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_3889201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889201 prefixEnd_3889201 := by exact prefixLift 3889201
  have htrace : WordTrace (prefixWord ++ tailWord_3889201) baseStart_3889201 baseEnd_3889201 := by
    simpa [prefixWord, tailWord_3889201, baseEnd_3889201] using wordTrace_append hprefix tailTrace_3889201
  have hstable : (prefixWord ++ tailWord_3889201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889201).length < 2 ^ (prefixWord ++ tailWord_3889201).sum := by decide
  have hdescent : baseEnd_3889201 < baseStart_3889201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889225 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 6]
def baseStart_3889225 : Nat := 118140960795 + 3889225 * 2 ^ 59
def prefixEnd_3889225 : Nat := 4983230072969 + 3 ^ 40 * 3889225 * 2
def baseEnd_3889225 : Nat := 443787066329478027333619

theorem tailTrace_3889225 : CollatzResearch.WordTrace tailWord_3889225 prefixEnd_3889225 443787066329478027333619 := by
  unfold tailWord_3889225
  simp only [CollatzResearch.WordTrace]
  refine ⟨141851689335009526593317129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94567792890006351062211419 141851689335009526593317129)
  ·
    refine ⟨106388767001257144944987847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141851689335009526593317129 106388767001257144944987847)
    ·
      refine ⟨159583150501885717417481771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106388767001257144944987847 159583150501885717417481771)
      ·
        refine ⟨239374725752828576126222657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159583150501885717417481771 239374725752828576126222657)
        ·
          refine ⟨179531044314621432094666993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239374725752828576126222657 179531044314621432094666993)
          ·
            refine ⟨134648283235966074071000245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179531044314621432094666993 134648283235966074071000245)
            ·
              refine ⟨12623276553371819444156273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134648283235966074071000245 12623276553371819444156273)
              ·
                refine ⟨9467457415028864583117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12623276553371819444156273 9467457415028864583117205)
                ·
                  refine ⟨443787066329478027333619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9467457415028864583117205 443787066329478027333619)
                  ·
                    rfl

theorem cell22_3889225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_3889225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889225 prefixEnd_3889225 := by exact prefixLift 3889225
  have htrace : WordTrace (prefixWord ++ tailWord_3889225) baseStart_3889225 baseEnd_3889225 := by
    simpa [prefixWord, tailWord_3889225, baseEnd_3889225] using wordTrace_append hprefix tailTrace_3889225
  have hstable : (prefixWord ++ tailWord_3889225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889225).length < 2 ^ (prefixWord ++ tailWord_3889225).sum := by decide
  have hdescent : baseEnd_3889225 < baseStart_3889225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889244 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3889244 : Nat := 118140960795 + 3889244 * 2 ^ 59
def prefixEnd_3889244 : Nat := 4983230072969 + 3 ^ 40 * 3889244 * 2
def baseEnd_3889244 : Nat := 1331367703076724365775799

theorem tailTrace_3889244 : CollatzResearch.WordTrace tailWord_3889244 prefixEnd_3889244 1331367703076724365775799 := by
  unfold tailWord_3889244
  simp only [CollatzResearch.WordTrace]
  refine ⟨70926191160970346419129393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94568254881293795225505857 70926191160970346419129393)
  ·
    refine ⟨53194643370727759814347045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70926191160970346419129393 53194643370727759814347045)
    ·
      refine ⟨9973995632011454965190071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53194643370727759814347045 9973995632011454965190071)
      ·
        refine ⟨14960993448017182447785107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9973995632011454965190071 14960993448017182447785107)
        ·
          refine ⟨22441490172025773671677661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14960993448017182447785107 22441490172025773671677661)
          ·
            refine ⟨8415558814509665126879123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22441490172025773671677661 8415558814509665126879123)
            ·
              refine ⟨12623338221764497690318685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415558814509665126879123 12623338221764497690318685)
              ·
                refine ⟨4733751833161686633869507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12623338221764497690318685 4733751833161686633869507)
                ·
                  refine ⟨7100627749742529950804261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4733751833161686633869507 7100627749742529950804261)
                  ·
                    refine ⟨1331367703076724365775799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7100627749742529950804261 1331367703076724365775799)
                    ·
                      rfl

theorem cell22_3889244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3889244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889244 prefixEnd_3889244 := by exact prefixLift 3889244
  have htrace : WordTrace (prefixWord ++ tailWord_3889244) baseStart_3889244 baseEnd_3889244 := by
    simpa [prefixWord, tailWord_3889244, baseEnd_3889244] using wordTrace_append hprefix tailTrace_3889244
  have hstable : (prefixWord ++ tailWord_3889244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889244).length < 2 ^ (prefixWord ++ tailWord_3889244).sum := by decide
  have hdescent : baseEnd_3889244 < baseStart_3889244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889257 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_3889257 : Nat := 118140960795 + 3889257 * 2 ^ 59
def prefixEnd_3889257 : Nat := 4983230072969 + 3 ^ 40 * 3889257 * 2
def baseEnd_3889257 : Nat := 1331372153242396665200759

theorem tailTrace_3889257 : CollatzResearch.WordTrace tailWord_3889257 prefixEnd_3889257 1331372153242396665200759 := by
  unfold tailWord_3889257
  simp only [CollatzResearch.WordTrace]
  refine ⟨141852856470893596058482025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94568570980595730705654683 141852856470893596058482025)
  ·
    refine ⟨106389642353170197043861519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141852856470893596058482025 106389642353170197043861519)
    ·
      refine ⟨159584463529755295565792279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106389642353170197043861519 159584463529755295565792279)
      ·
        refine ⟨239376695294632943348688419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159584463529755295565792279 239376695294632943348688419)
        ·
          refine ⟨359065042941949415023032629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239376695294632943348688419 359065042941949415023032629)
          ·
            refine ⟨33662347775807757658409309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359065042941949415023032629 33662347775807757658409309)
            ·
              refine ⟨12623380415927909121903491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33662347775807757658409309 12623380415927909121903491)
              ·
                refine ⟨18935070623891863682855237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12623380415927909121903491 18935070623891863682855237)
                ·
                  refine ⟨3550325741979724440535357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18935070623891863682855237 3550325741979724440535357)
                  ·
                    refine ⟨1331372153242396665200759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550325741979724440535357 1331372153242396665200759)
                    ·
                      rfl

theorem cell22_3889257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_3889257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889257 prefixEnd_3889257 := by exact prefixLift 3889257
  have htrace : WordTrace (prefixWord ++ tailWord_3889257) baseStart_3889257 baseEnd_3889257 := by
    simpa [prefixWord, tailWord_3889257, baseEnd_3889257] using wordTrace_append hprefix tailTrace_3889257
  have hstable : (prefixWord ++ tailWord_3889257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889257).length < 2 ^ (prefixWord ++ tailWord_3889257).sum := by decide
  have hdescent : baseEnd_3889257 < baseStart_3889257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889287 : List Nat := [1, 1, 4, 2, 1, 1, 6, 6]
def baseStart_3889287 : Nat := 118140960795 + 3889287 * 2 ^ 59
def prefixEnd_3889287 : Nat := 4983230072969 + 3 ^ 40 * 3889287 * 2
def baseEnd_3889287 : Nat := 147931380317276287438963

theorem tailTrace_3889287 : CollatzResearch.WordTrace tailWord_3889287 prefixEnd_3889287 147931380317276287438963 := by
  unfold tailWord_3889287
  simp only [CollatzResearch.WordTrace]
  refine ⟨141853950660784911182074115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94569300440523274121382743 141853950660784911182074115)
  ·
    refine ⟨212780925991177366773111173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141853950660784911182074115 212780925991177366773111173)
    ·
      refine ⟨39896423623345756269958345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212780925991177366773111173 39896423623345756269958345)
      ·
        refine ⟨29922317717509317202468759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39896423623345756269958345 29922317717509317202468759)
        ·
          refine ⟨44883476576263975803703139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29922317717509317202468759 44883476576263975803703139)
          ·
            refine ⟨67325214864395963705554709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44883476576263975803703139 67325214864395963705554709)
            ·
              refine ⟨3155869446768560798697877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67325214864395963705554709 3155869446768560798697877)
              ·
                refine ⟨147931380317276287438963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3155869446768560798697877 147931380317276287438963)
                ·
                  rfl

theorem cell22_3889287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 6].length) (baseStart_3889287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889287 prefixEnd_3889287 := by exact prefixLift 3889287
  have htrace : WordTrace (prefixWord ++ tailWord_3889287) baseStart_3889287 baseEnd_3889287 := by
    simpa [prefixWord, tailWord_3889287, baseEnd_3889287] using wordTrace_append hprefix tailTrace_3889287
  have hstable : (prefixWord ++ tailWord_3889287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889287).length < 2 ^ (prefixWord ++ tailWord_3889287).sum := by decide
  have hdescent : baseEnd_3889287 < baseStart_3889287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889304 : List Nat := [2, 1, 2, 4, 4, 1, 8]
def baseStart_3889304 : Nat := 118140960795 + 3889304 * 2 ^ 59
def prefixEnd_3889304 : Nat := 4983230072969 + 3 ^ 40 * 3889304 * 2
def baseEnd_3889304 : Nat := 49310675640848304047245

theorem tailTrace_3889304 : CollatzResearch.WordTrace tailWord_3889304 prefixEnd_3889304 49310675640848304047245 := by
  unfold tailWord_3889304
  simp only [CollatzResearch.WordTrace]
  refine ⟨70927285350861661542721483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94569713801148882056961977 70927285350861661542721483)
  ·
    refine ⟨106390928026292492314082225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70927285350861661542721483 106390928026292492314082225)
    ·
      refine ⟨79793196019719369235561669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106390928026292492314082225 79793196019719369235561669)
      ·
        refine ⟨14961224253697381731667813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79793196019719369235561669 14961224253697381731667813)
        ·
          refine ⟨2805229547568259074687715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14961224253697381731667813 2805229547568259074687715)
          ·
            refine ⟨4207844321352388612031573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805229547568259074687715 4207844321352388612031573)
            ·
              refine ⟨49310675640848304047245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4207844321352388612031573 49310675640848304047245)
              ·
                rfl

theorem cell22_3889304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 8].length) (baseStart_3889304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889304 prefixEnd_3889304 := by exact prefixLift 3889304
  have htrace : WordTrace (prefixWord ++ tailWord_3889304) baseStart_3889304 baseEnd_3889304 := by
    simpa [prefixWord, tailWord_3889304, baseEnd_3889304] using wordTrace_append hprefix tailTrace_3889304
  have hstable : (prefixWord ++ tailWord_3889304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889304).length < 2 ^ (prefixWord ++ tailWord_3889304).sum := by decide
  have hdescent : baseEnd_3889304 < baseStart_3889304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889366 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3889366 : Nat := 118140960795 + 3889366 * 2 ^ 59
def prefixEnd_3889366 : Nat := 4983230072969 + 3 ^ 40 * 3889366 * 2
def baseEnd_3889366 : Nat := 443803155389985571408475

theorem tailTrace_3889366 : CollatzResearch.WordTrace tailWord_3889366 prefixEnd_3889366 443803155389985571408475 := by
  unfold tailWord_3889366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8866052001718669229637497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94571221351665805116133301 8866052001718669229637497)
  ·
    refine ⟨6649539001289001922228123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8866052001718669229637497 6649539001289001922228123)
    ·
      refine ⟨9974308501933502883342185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6649539001289001922228123 9974308501933502883342185)
      ·
        refine ⟨7480731376450127162506639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9974308501933502883342185 7480731376450127162506639)
        ·
          refine ⟨11221097064675190743759959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7480731376450127162506639 11221097064675190743759959)
          ·
            refine ⟨16831645597012786115639939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11221097064675190743759959 16831645597012786115639939)
            ·
              refine ⟨25247468395519179173459909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16831645597012786115639939 25247468395519179173459909)
              ·
                refine ⟨4733900324159846095023733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25247468395519179173459909 4733900324159846095023733)
                ·
                  refine ⟨443803155389985571408475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4733900324159846095023733 443803155389985571408475)
                  ·
                    rfl

theorem cell22_3889366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3889366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889366 prefixEnd_3889366 := by exact prefixLift 3889366
  have htrace : WordTrace (prefixWord ++ tailWord_3889366) baseStart_3889366 baseEnd_3889366 := by
    simpa [prefixWord, tailWord_3889366, baseEnd_3889366] using wordTrace_append hprefix tailTrace_3889366
  have hstable : (prefixWord ++ tailWord_3889366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889366).length < 2 ^ (prefixWord ++ tailWord_3889366).sum := by decide
  have hdescent : baseEnd_3889366 < baseStart_3889366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889377 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 6]
def baseStart_3889377 : Nat := 118140960795 + 3889377 * 2 ^ 59
def prefixEnd_3889377 : Nat := 4983230072969 + 3 ^ 40 * 3889377 * 2
def baseEnd_3889377 : Nat := 443804410564918784066797

theorem tailTrace_3889377 : CollatzResearch.WordTrace tailWord_3889377 prefixEnd_3889377 443804410564918784066797 := by
  unfold tailWord_3889377
  simp only [CollatzResearch.WordTrace]
  refine ⟨141857233230458856552850385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94571488820305904368566923 141857233230458856552850385)
  ·
    refine ⟨106392924922844142414637789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141857233230458856552850385 106392924922844142414637789)
    ·
      refine ⟨39897346846066553405489171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106392924922844142414637789 39897346846066553405489171)
      ·
        refine ⟨59846020269099830108233757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39897346846066553405489171 59846020269099830108233757)
        ·
          refine ⟨22442257600912436290587659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59846020269099830108233757 22442257600912436290587659)
          ·
            refine ⟨33663386401368654435881489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22442257600912436290587659 33663386401368654435881489)
            ·
              refine ⟨25247539801026490826911117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33663386401368654435881489 25247539801026490826911117)
              ·
                refine ⟨9467827425384934060091669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25247539801026490826911117 9467827425384934060091669)
                ·
                  refine ⟨443804410564918784066797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9467827425384934060091669 443804410564918784066797)
                  ·
                    rfl

theorem cell22_3889377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_3889377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889377 prefixEnd_3889377 := by exact prefixLift 3889377
  have htrace : WordTrace (prefixWord ++ tailWord_3889377) baseStart_3889377 baseEnd_3889377 := by
    simpa [prefixWord, tailWord_3889377, baseEnd_3889377] using wordTrace_append hprefix tailTrace_3889377
  have hstable : (prefixWord ++ tailWord_3889377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889377).length < 2 ^ (prefixWord ++ tailWord_3889377).sum := by decide
  have hdescent : baseEnd_3889377 < baseStart_3889377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889394 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_3889394 : Nat := 118140960795 + 3889394 * 2 ^ 59
def prefixEnd_3889394 : Nat := 4983230072969 + 3 ^ 40 * 3889394 * 2
def baseEnd_3889394 : Nat := 443806350380724658175113

theorem tailTrace_3889394 : CollatzResearch.WordTrace tailWord_3889394 prefixEnd_3889394 443806350380724658175113 := by
  unfold tailWord_3889394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35464463317849317114054809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94571902180931512304146157 35464463317849317114054809)
  ·
    refine ⟨26598347488386987835541107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35464463317849317114054809 26598347488386987835541107)
    ·
      refine ⟨39897521232580481753311661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26598347488386987835541107 39897521232580481753311661)
      ·
        refine ⟨14961570462217680657491873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39897521232580481753311661 14961570462217680657491873)
        ·
          refine ⟨11221177846663260493118905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14961570462217680657491873 11221177846663260493118905)
          ·
            refine ⟨8415883384997445369839179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11221177846663260493118905 8415883384997445369839179)
            ·
              refine ⟨12623825077496168054758769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8415883384997445369839179 12623825077496168054758769)
              ·
                refine ⟨9467868808122126041069077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12623825077496168054758769 9467868808122126041069077)
                ·
                  refine ⟨443806350380724658175113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9467868808122126041069077 443806350380724658175113)
                  ·
                    rfl

theorem cell22_3889394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_3889394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889394 prefixEnd_3889394 := by exact prefixLift 3889394
  have htrace : WordTrace (prefixWord ++ tailWord_3889394) baseStart_3889394 baseEnd_3889394 := by
    simpa [prefixWord, tailWord_3889394, baseEnd_3889394] using wordTrace_append hprefix tailTrace_3889394
  have hstable : (prefixWord ++ tailWord_3889394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889394).length < 2 ^ (prefixWord ++ tailWord_3889394).sum := by decide
  have hdescent : baseEnd_3889394 < baseStart_3889394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889407 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_3889407 : Nat := 118140960795 + 3889407 * 2 ^ 59
def prefixEnd_3889407 : Nat := 4983230072969 + 3 ^ 40 * 3889407 * 2
def baseEnd_3889407 : Nat := 1331423501307846273950299

theorem tailTrace_3889407 : CollatzResearch.WordTrace tailWord_3889407 prefixEnd_3889407 1331423501307846273950299 := by
  unfold tailWord_3889407
  simp only [CollatzResearch.WordTrace]
  refine ⟨141858327420350171676442475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94572218280233447784294983 141858327420350171676442475)
  ·
    refine ⟨212787491130525257514663713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141858327420350171676442475 212787491130525257514663713)
    ·
      refine ⟨159590618347893943135997785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212787491130525257514663713 159590618347893943135997785)
      ·
        refine ⟨119692963760920457351998339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159590618347893943135997785 119692963760920457351998339)
        ·
          refine ⟨179539445641380686027997509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119692963760920457351998339 179539445641380686027997509)
          ·
            refine ⟨33663646057758878630249533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179539445641380686027997509 33663646057758878630249533)
            ·
              refine ⟨12623867271659579486343575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33663646057758878630249533 12623867271659579486343575)
              ·
                refine ⟨18935800907489369229515363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12623867271659579486343575 18935800907489369229515363)
                ·
                  refine ⟨28403701361234053844273045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18935800907489369229515363 28403701361234053844273045)
                  ·
                    refine ⟨1331423501307846273950299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28403701361234053844273045 1331423501307846273950299)
                    ·
                      rfl

theorem cell22_3889407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_3889407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889407 prefixEnd_3889407 := by exact prefixLift 3889407
  have htrace : WordTrace (prefixWord ++ tailWord_3889407) baseStart_3889407 baseEnd_3889407 := by
    simpa [prefixWord, tailWord_3889407, baseEnd_3889407] using wordTrace_append hprefix tailTrace_3889407
  have hstable : (prefixWord ++ tailWord_3889407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889407).length < 2 ^ (prefixWord ++ tailWord_3889407).sum := by decide
  have hdescent : baseEnd_3889407 < baseStart_3889407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889409 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3889409 : Nat := 118140960795 + 3889409 * 2 ^ 59
def prefixEnd_3889409 : Nat := 4983230072969 + 3 ^ 40 * 3889409 * 2
def baseEnd_3889409 : Nat := 1331424185948718935400293

theorem tailTrace_3889409 : CollatzResearch.WordTrace tailWord_3889409 prefixEnd_3889409 1331424185948718935400293 := by
  unfold tailWord_3889409
  simp only [CollatzResearch.WordTrace]
  refine ⟨141858400366342926018015281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94572266910895284012010187 141858400366342926018015281)
  ·
    refine ⟨106393800274757194513511461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141858400366342926018015281 106393800274757194513511461)
    ·
      refine ⟨19948837551516973971283399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106393800274757194513511461 19948837551516973971283399)
      ·
        refine ⟨29923256327275460956925099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19948837551516973971283399 29923256327275460956925099)
        ·
          refine ⟨44884884490913191435387649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29923256327275460956925099 44884884490913191435387649)
          ·
            refine ⟨33663663368184893576540737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44884884490913191435387649 33663663368184893576540737)
            ·
              refine ⟨25247747526138670182405553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33663663368184893576540737 25247747526138670182405553)
              ·
                refine ⟨18935810644604002636804165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25247747526138670182405553 18935810644604002636804165)
                ·
                  refine ⟨3550464495863250494400781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18935810644604002636804165 3550464495863250494400781)
                  ·
                    refine ⟨1331424185948718935400293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550464495863250494400781 1331424185948718935400293)
                    ·
                      rfl

theorem cell22_3889409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3889409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889409 prefixEnd_3889409 := by exact prefixLift 3889409
  have htrace : WordTrace (prefixWord ++ tailWord_3889409) baseStart_3889409 baseEnd_3889409 := by
    simpa [prefixWord, tailWord_3889409, baseEnd_3889409] using wordTrace_append hprefix tailTrace_3889409
  have hstable : (prefixWord ++ tailWord_3889409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889409).length < 2 ^ (prefixWord ++ tailWord_3889409).sum := by decide
  have hdescent : baseEnd_3889409 < baseStart_3889409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889422 : List Nat := [4, 1, 1, 2, 1, 2, 11]
def baseStart_3889422 : Nat := 118140960795 + 3889422 * 2 ^ 59
def prefixEnd_3889422 : Nat := 4983230072969 + 3 ^ 40 * 3889422 * 2
def baseEnd_3889422 : Nat := 49312171707940416104639

theorem tailTrace_3889422 : CollatzResearch.WordTrace tailWord_3889422 prefixEnd_3889422 49312171707940416104639 := by
  unfold tailWord_3889422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17732359314411978654779815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94572583010197219492159013 17732359314411978654779815)
  ·
    refine ⟨26598538971617967982169723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17732359314411978654779815 26598538971617967982169723)
    ·
      refine ⟨39897808457426951973254585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26598538971617967982169723 39897808457426951973254585)
      ·
        refine ⟨29923356343070213979940939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39897808457426951973254585 29923356343070213979940939)
        ·
          refine ⟨44885034514605320969911409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29923356343070213979940939 44885034514605320969911409)
          ·
            refine ⟨33663775885953990727433557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44885034514605320969911409 33663775885953990727433557)
            ·
              refine ⟨49312171707940416104639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33663775885953990727433557 49312171707940416104639)
              ·
                rfl

theorem cell22_3889422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 11].length) (baseStart_3889422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889422 prefixEnd_3889422 := by exact prefixLift 3889422
  have htrace : WordTrace (prefixWord ++ tailWord_3889422) baseStart_3889422 baseEnd_3889422 := by
    simpa [prefixWord, tailWord_3889422, baseEnd_3889422] using wordTrace_append hprefix tailTrace_3889422
  have hstable : (prefixWord ++ tailWord_3889422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889422).length < 2 ^ (prefixWord ++ tailWord_3889422).sum := by decide
  have hdescent : baseEnd_3889422 < baseStart_3889422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889452 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_3889452 : Nat := 118140960795 + 3889452 * 2 ^ 59
def prefixEnd_3889452 : Nat := 4983230072969 + 3 ^ 40 * 3889452 * 2
def baseEnd_3889452 : Nat := 1331438905727481156575161

theorem tailTrace_3889452 : CollatzResearch.WordTrace tailWord_3889452 prefixEnd_3889452 1331438905727481156575161 := by
  unfold tailWord_3889452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70929984352593572180915305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94573312470124762907887073 70929984352593572180915305)
  ·
    refine ⟨53197488264445179135686479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70929984352593572180915305 53197488264445179135686479)
    ·
      refine ⟨79796232396667768703529719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53197488264445179135686479 79796232396667768703529719)
      ·
        refine ⟨119694348595001653055294579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79796232396667768703529719 119694348595001653055294579)
        ·
          refine ⟨179541522892502479582941869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119694348595001653055294579 179541522892502479582941869)
          ·
            refine ⟨67328071084688429843603201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179541522892502479582941869 67328071084688429843603201)
            ·
              refine ⟨50496053313516322382702401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67328071084688429843603201 50496053313516322382702401)
              ·
                refine ⟨37872039985137241787026801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50496053313516322382702401 37872039985137241787026801)
                ·
                  refine ⟨28404029988852931340270101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37872039985137241787026801 28404029988852931340270101)
                  ·
                    refine ⟨1331438905727481156575161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28404029988852931340270101 1331438905727481156575161)
                    ·
                      rfl

theorem cell22_3889452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_3889452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889452 prefixEnd_3889452 := by exact prefixLift 3889452
  have htrace : WordTrace (prefixWord ++ tailWord_3889452) baseStart_3889452 baseEnd_3889452 := by
    simpa [prefixWord, tailWord_3889452, baseEnd_3889452] using wordTrace_append hprefix tailTrace_3889452
  have hstable : (prefixWord ++ tailWord_3889452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889452).length < 2 ^ (prefixWord ++ tailWord_3889452).sum := by decide
  have hdescent : baseEnd_3889452 < baseStart_3889452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889484 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_3889484 : Nat := 118140960795 + 3889484 * 2 ^ 59
def prefixEnd_3889484 : Nat := 4983230072969 + 3 ^ 40 * 3889484 * 2
def baseEnd_3889484 : Nat := 443816619993814579925021

theorem tailTrace_3889484 : CollatzResearch.WordTrace tailWord_3889484 prefixEnd_3889484 443816619993814579925021 := by
  unfold tailWord_3889484
  simp only [CollatzResearch.WordTrace]
  refine ⟨70930567920535606913497753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94574090560714142551330337 70930567920535606913497753)
  ·
    refine ⟨53197925940401705185123315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70930567920535606913497753 53197925940401705185123315)
    ·
      refine ⟨79796888910602557777684973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53197925940401705185123315 79796888910602557777684973)
      ·
        refine ⟨29923833341475959166631865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79796888910602557777684973 29923833341475959166631865)
        ·
          refine ⟨22442875006106969374973899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29923833341475959166631865 22442875006106969374973899)
          ·
            refine ⟨33664312509160454062460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22442875006106969374973899 33664312509160454062460849)
            ·
              refine ⟨25248234381870340546845637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33664312509160454062460849 25248234381870340546845637)
              ·
                refine ⟨4734043946600688852533557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25248234381870340546845637 4734043946600688852533557)
                ·
                  refine ⟨443816619993814579925021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4734043946600688852533557 443816619993814579925021)
                  ·
                    rfl

theorem cell22_3889484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_3889484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889484 prefixEnd_3889484 := by exact prefixLift 3889484
  have htrace : WordTrace (prefixWord ++ tailWord_3889484) baseStart_3889484 baseEnd_3889484 := by
    simpa [prefixWord, tailWord_3889484, baseEnd_3889484] using wordTrace_append hprefix tailTrace_3889484
  have hstable : (prefixWord ++ tailWord_3889484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889484).length < 2 ^ (prefixWord ++ tailWord_3889484).sum := by decide
  have hdescent : baseEnd_3889484 < baseStart_3889484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889497 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_3889497 : Nat := 118140960795 + 3889497 * 2 ^ 59
def prefixEnd_3889497 : Nat := 4983230072969 + 3 ^ 40 * 3889497 * 2
def baseEnd_3889497 : Nat := 1331454310147116039200023

theorem tailTrace_3889497 : CollatzResearch.WordTrace tailWord_3889497 prefixEnd_3889497 1331454310147116039200023 := by
  unfold tailWord_3889497
  simp only [CollatzResearch.WordTrace]
  refine ⟨141861609990024117047218745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94574406660016078031479163 141861609990024117047218745)
  ·
    refine ⟨106396207492518087785414059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141861609990024117047218745 106396207492518087785414059)
    ·
      refine ⟨159594311238777131678121089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106396207492518087785414059 159594311238777131678121089)
      ·
        refine ⟨119695733429082848758590817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159594311238777131678121089 119695733429082848758590817)
        ·
          refine ⟨89771800071812136568943113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119695733429082848758590817 89771800071812136568943113)
          ·
            refine ⟨67328850053859102426707335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89771800071812136568943113 67328850053859102426707335)
            ·
              refine ⟨100993275080788653640061003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67328850053859102426707335 100993275080788653640061003)
              ·
                refine ⟨151489912621182980460091505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100993275080788653640061003 151489912621182980460091505)
                ·
                  refine ⟨113617434465887235345068629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151489912621182980460091505 113617434465887235345068629)
                  ·
                    refine ⟨1331454310147116039200023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113617434465887235345068629 1331454310147116039200023)
                    ·
                      rfl

theorem cell22_3889497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_3889497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889497 prefixEnd_3889497 := by exact prefixLift 3889497
  have htrace : WordTrace (prefixWord ++ tailWord_3889497) baseStart_3889497 baseEnd_3889497 := by
    simpa [prefixWord, tailWord_3889497, baseEnd_3889497] using wordTrace_append hprefix tailTrace_3889497
  have hstable : (prefixWord ++ tailWord_3889497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889497).length < 2 ^ (prefixWord ++ tailWord_3889497).sum := by decide
  have hdescent : baseEnd_3889497 < baseStart_3889497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889544 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3889544 : Nat := 118140960795 + 3889544 * 2 ^ 59
def prefixEnd_3889544 : Nat := 4983230072969 + 3 ^ 40 * 3889544 * 2
def baseEnd_3889544 : Nat := 1331470399207623583274879

theorem tailTrace_3889544 : CollatzResearch.WordTrace tailWord_3889544 prefixEnd_3889544 1331470399207623583274879 := by
  unfold tailWord_3889544
  simp only [CollatzResearch.WordTrace]
  refine ⟨70931662110426922037089843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94575549480569229382786457 70931662110426922037089843)
  ·
    refine ⟨106397493165640383055634765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70931662110426922037089843 106397493165640383055634765)
    ·
      refine ⟨39899059937115143645863037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106397493165640383055634765 39899059937115143645863037)
      ·
        refine ⟨14962147476418178867198639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39899059937115143645863037 14962147476418178867198639)
        ·
          refine ⟨22443221214627268300797959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14962147476418178867198639 22443221214627268300797959)
          ·
            refine ⟨33664831821940902451196939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22443221214627268300797959 33664831821940902451196939)
            ·
              refine ⟨50497247732911353676795409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33664831821940902451196939 50497247732911353676795409)
              ·
                refine ⟨37872935799683515257596557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50497247732911353676795409 37872935799683515257596557)
                ·
                  refine ⟨14202350924881318221598709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37872935799683515257596557 14202350924881318221598709)
                  ·
                    refine ⟨1331470399207623583274879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14202350924881318221598709 1331470399207623583274879)
                    ·
                      rfl

theorem cell22_3889544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3889544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889544 prefixEnd_3889544 := by exact prefixLift 3889544
  have htrace : WordTrace (prefixWord ++ tailWord_3889544) baseStart_3889544 baseEnd_3889544 := by
    simpa [prefixWord, tailWord_3889544, baseEnd_3889544] using wordTrace_append hprefix tailTrace_3889544
  have hstable : (prefixWord ++ tailWord_3889544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889544).length < 2 ^ (prefixWord ++ tailWord_3889544).sum := by decide
  have hdescent : baseEnd_3889544 < baseStart_3889544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889559 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_3889559 : Nat := 118140960795 + 3889559 * 2 ^ 59
def prefixEnd_3889559 : Nat := 4983230072969 + 3 ^ 40 * 3889559 * 2
def baseEnd_3889559 : Nat := 1331475534014168544149833

theorem tailTrace_3889559 : CollatzResearch.WordTrace tailWord_3889559 prefixEnd_3889559 1331475534014168544149833 := by
  unfold tailWord_3889559
  simp only [CollatzResearch.WordTrace]
  refine ⟨141863871315799501635975731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94575914210533001090650487 141863871315799501635975731)
  ·
    refine ⟨212795806973699252453963597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141863871315799501635975731 212795806973699252453963597)
    ·
      refine ⟨79798427615137219670236349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212795806973699252453963597 79798427615137219670236349)
      ·
        refine ⟨29924410355676457376338631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79798427615137219670236349 29924410355676457376338631)
        ·
          refine ⟨44886615533514686064507947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29924410355676457376338631 44886615533514686064507947)
          ·
            refine ⟨67329923300272029096761921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44886615533514686064507947 67329923300272029096761921)
            ·
              refine ⟨50497442475204021822571441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67329923300272029096761921 50497442475204021822571441)
              ·
                refine ⟨37873081856403016366928581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50497442475204021822571441 37873081856403016366928581)
                ·
                  refine ⟨7101202848075565568799109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37873081856403016366928581 7101202848075565568799109)
                  ·
                    refine ⟨1331475534014168544149833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7101202848075565568799109 1331475534014168544149833)
                    ·
                      rfl

theorem cell22_3889559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_3889559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889559 prefixEnd_3889559 := by exact prefixLift 3889559
  have htrace : WordTrace (prefixWord ++ tailWord_3889559) baseStart_3889559 baseEnd_3889559 := by
    simpa [prefixWord, tailWord_3889559, baseEnd_3889559] using wordTrace_append hprefix tailTrace_3889559
  have hstable : (prefixWord ++ tailWord_3889559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889559).length < 2 ^ (prefixWord ++ tailWord_3889559).sum := by decide
  have hdescent : baseEnd_3889559 < baseStart_3889559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889561 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_3889561 : Nat := 118140960795 + 3889561 * 2 ^ 59
def prefixEnd_3889561 : Nat := 4983230072969 + 3 ^ 40 * 3889561 * 2
def baseEnd_3889561 : Nat := 1331476218655041205599827

theorem tailTrace_3889561 : CollatzResearch.WordTrace tailWord_3889561 prefixEnd_3889561 1331476218655041205599827 := by
  unfold tailWord_3889561
  simp only [CollatzResearch.WordTrace]
  refine ⟨141863944261792255977548537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94575962841194837318365691 141863944261792255977548537)
  ·
    refine ⟨106397958196344191983161403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141863944261792255977548537 106397958196344191983161403)
    ·
      refine ⟨159596937294516287974742105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106397958196344191983161403 159596937294516287974742105)
      ·
        refine ⟨119697702970887215981056579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159596937294516287974742105 119697702970887215981056579)
        ·
          refine ⟨179546554456330823971584869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119697702970887215981056579 179546554456330823971584869)
          ·
            refine ⟨33664978960562029494672163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179546554456330823971584869 33664978960562029494672163)
            ·
              refine ⟨50497468440843044242008245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33664978960562029494672163 50497468440843044242008245)
              ·
                refine ⟨4734137666329035397688273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50497468440843044242008245 4734137666329035397688273)
                ·
                  refine ⟨3550603249746776548266205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734137666329035397688273 3550603249746776548266205)
                  ·
                    refine ⟨1331476218655041205599827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550603249746776548266205 1331476218655041205599827)
                    ·
                      rfl

theorem cell22_3889561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_3889561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889561 prefixEnd_3889561 := by exact prefixLift 3889561
  have htrace : WordTrace (prefixWord ++ tailWord_3889561) baseStart_3889561 baseEnd_3889561 := by
    simpa [prefixWord, tailWord_3889561, baseEnd_3889561] using wordTrace_append hprefix tailTrace_3889561
  have hstable : (prefixWord ++ tailWord_3889561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889561).length < 2 ^ (prefixWord ++ tailWord_3889561).sum := by decide
  have hdescent : baseEnd_3889561 < baseStart_3889561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889640 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3889640 : Nat := 118140960795 + 3889640 * 2 ^ 59
def prefixEnd_3889640 : Nat := 4983230072969 + 3 ^ 40 * 3889640 * 2
def baseEnd_3889640 : Nat := 1331503261969511332874585

theorem tailTrace_3889640 : CollatzResearch.WordTrace tailWord_3889640 prefixEnd_3889640 1331503261969511332874585 := by
  unfold tailWord_3889640
  simp only [CollatzResearch.WordTrace]
  refine ⟨70933412814253026234837187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94577883752337368313116249 70933412814253026234837187)
  ·
    refine ⟨106400119221379539352255781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70933412814253026234837187 106400119221379539352255781)
    ·
      refine ⟨19950022354008663628547959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106400119221379539352255781 19950022354008663628547959)
      ·
        refine ⟨29925033531012995442821939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950022354008663628547959 29925033531012995442821939)
        ·
          refine ⟨44887550296519493164232909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29925033531012995442821939 44887550296519493164232909)
          ·
            refine ⟨16832831361194809936587341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44887550296519493164232909 16832831361194809936587341)
            ·
              refine ⟨6312311760448053726220253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16832831361194809936587341 6312311760448053726220253)
              ·
                refine ⟨2367116910168020147332595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6312311760448053726220253 2367116910168020147332595)
                ·
                  refine ⟨3550675365252030220998893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367116910168020147332595 3550675365252030220998893)
                  ·
                    refine ⟨1331503261969511332874585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550675365252030220998893 1331503261969511332874585)
                    ·
                      rfl

theorem cell22_3889640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3889640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889640 prefixEnd_3889640 := by exact prefixLift 3889640
  have htrace : WordTrace (prefixWord ++ tailWord_3889640) baseStart_3889640 baseEnd_3889640 := by
    simpa [prefixWord, tailWord_3889640, baseEnd_3889640] using wordTrace_append hprefix tailTrace_3889640
  have hstable : (prefixWord ++ tailWord_3889640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889640).length < 2 ^ (prefixWord ++ tailWord_3889640).sum := by decide
  have hdescent : baseEnd_3889640 < baseStart_3889640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889698 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3889698 : Nat := 118140960795 + 3889698 * 2 ^ 59
def prefixEnd_3889698 : Nat := 4983230072969 + 3 ^ 40 * 3889698 * 2
def baseEnd_3889698 : Nat := 443841038851606171641469

theorem tailTrace_3889698 : CollatzResearch.WordTrace tailWord_3889698 prefixEnd_3889698 443841038851606171641469 := by
  unfold tailWord_3889698
  simp only [CollatzResearch.WordTrace]
  refine ⟨35467235265573982093821437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94579294041530618916857165 35467235265573982093821437)
  ·
    refine ⟨13300213224590243285183039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35467235265573982093821437 13300213224590243285183039)
    ·
      refine ⟨19950319836885364927774559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13300213224590243285183039 19950319836885364927774559)
      ·
        refine ⟨29925479755328047391661839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19950319836885364927774559 29925479755328047391661839)
        ·
          refine ⟨44888219632992071087492759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29925479755328047391661839 44888219632992071087492759)
          ·
            refine ⟨67332329449488106631239139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44888219632992071087492759 67332329449488106631239139)
            ·
              refine ⟨100998494174232159946858709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67332329449488106631239139 100998494174232159946858709)
              ·
                refine ⟨2367152207208566248754501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 100998494174232159946858709 2367152207208566248754501)
                ·
                  refine ⟨443841038851606171641469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367152207208566248754501 443841038851606171641469)
                  ·
                    rfl

theorem cell22_3889698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3889698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889698 prefixEnd_3889698 := by exact prefixLift 3889698
  have htrace : WordTrace (prefixWord ++ tailWord_3889698) baseStart_3889698 baseEnd_3889698 := by
    simpa [prefixWord, tailWord_3889698, baseEnd_3889698] using wordTrace_append hprefix tailTrace_3889698
  have hstable : (prefixWord ++ tailWord_3889698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889698).length < 2 ^ (prefixWord ++ tailWord_3889698).sum := by decide
  have hdescent : baseEnd_3889698 < baseStart_3889698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889713 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_3889713 : Nat := 118140960795 + 3889713 * 2 ^ 59
def prefixEnd_3889713 : Nat := 4983230072969 + 3 ^ 40 * 3889713 * 2
def baseEnd_3889713 : Nat := 1331528251361363475799361

theorem tailTrace_3889713 : CollatzResearch.WordTrace tailWord_3889713 prefixEnd_3889713 1331528251361363475799361 := by
  unfold tailWord_3889713
  simp only [CollatzResearch.WordTrace]
  refine ⟨141869488157241585937081793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94579658771494390624721195 141869488157241585937081793)
  ·
    refine ⟨106402116117931189452811345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141869488157241585937081793 106402116117931189452811345)
    ·
      refine ⟨79801587088448392089608509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106402116117931189452811345 79801587088448392089608509)
      ·
        refine ⟨29925595158168147033603191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79801587088448392089608509 29925595158168147033603191)
        ·
          refine ⟨44888392737252220550404787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29925595158168147033603191 44888392737252220550404787)
          ·
            refine ⟨67332589105878330825607181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44888392737252220550404787 67332589105878330825607181)
            ·
              refine ⟨25249720914704374059602693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67332589105878330825607181 25249720914704374059602693)
              ·
                refine ⟨4734322671507070136175505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25249720914704374059602693 4734322671507070136175505)
                ·
                  refine ⟨3550742003630302602131629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734322671507070136175505 3550742003630302602131629)
                  ·
                    refine ⟨1331528251361363475799361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550742003630302602131629 1331528251361363475799361)
                    ·
                      rfl

theorem cell22_3889713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_3889713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889713 prefixEnd_3889713 := by exact prefixLift 3889713
  have htrace : WordTrace (prefixWord ++ tailWord_3889713) baseStart_3889713 baseEnd_3889713 := by
    simpa [prefixWord, tailWord_3889713, baseEnd_3889713] using wordTrace_append hprefix tailTrace_3889713
  have hstable : (prefixWord ++ tailWord_3889713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889713).length < 2 ^ (prefixWord ++ tailWord_3889713).sum := by decide
  have hdescent : baseEnd_3889713 < baseStart_3889713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889732 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3889732 : Nat := 118140960795 + 3889732 * 2 ^ 59
def prefixEnd_3889732 : Nat := 4983230072969 + 3 ^ 40 * 3889732 * 2
def baseEnd_3889732 : Nat := 443844918483217919858101

theorem tailTrace_3889732 : CollatzResearch.WordTrace tailWord_3889732 prefixEnd_3889732 443844918483217919858101 := by
  unfold tailWord_3889732
  simp only [CollatzResearch.WordTrace]
  refine ⟨70935090572086376091011725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94580120762781834788015633 70935090572086376091011725)
  ·
    refine ⟨26600658964532391034129397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70935090572086376091011725 26600658964532391034129397)
    ·
      refine ⟨2493811777924911659449631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26600658964532391034129397 2493811777924911659449631)
      ·
        refine ⟨3740717666887367489174447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2493811777924911659449631 3740717666887367489174447)
        ·
          refine ⟨5611076500331051233761671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3740717666887367489174447 5611076500331051233761671)
          ·
            refine ⟨8416614750496576850642507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611076500331051233761671 8416614750496576850642507)
            ·
              refine ⟨12624922125744865275963761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8416614750496576850642507 12624922125744865275963761)
              ·
                refine ⟨9468691594308648956972821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12624922125744865275963761 9468691594308648956972821)
                ·
                  refine ⟨443844918483217919858101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9468691594308648956972821 443844918483217919858101)
                  ·
                    rfl

theorem cell22_3889732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3889732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889732 prefixEnd_3889732 := by exact prefixLift 3889732
  have htrace : WordTrace (prefixWord ++ tailWord_3889732) baseStart_3889732 baseEnd_3889732 := by
    simpa [prefixWord, tailWord_3889732, baseEnd_3889732] using wordTrace_append hprefix tailTrace_3889732
  have hstable : (prefixWord ++ tailWord_3889732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889732).length < 2 ^ (prefixWord ++ tailWord_3889732).sum := by decide
  have hdescent : baseEnd_3889732 < baseStart_3889732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889771 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 5]
def baseStart_3889771 : Nat := 118140960795 + 3889771 * 2 ^ 59
def prefixEnd_3889771 : Nat := 4983230072969 + 3 ^ 40 * 3889771 * 2
def baseEnd_3889771 : Nat := 443849368648890219283061

theorem tailTrace_3889771 : CollatzResearch.WordTrace tailWord_3889771 prefixEnd_3889771 443849368648890219283061 := by
  unfold tailWord_3889771
  simp only [CollatzResearch.WordTrace]
  refine ⟨141871603591031461842693167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94581069060687641228462111 141871603591031461842693167)
  ·
    refine ⟨212807405386547192764039751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141871603591031461842693167 212807405386547192764039751)
    ·
      refine ⟨319211108079820789146059627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212807405386547192764039751 319211108079820789146059627)
      ·
        refine ⟨478816662119731183719089441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319211108079820789146059627 478816662119731183719089441)
        ·
          refine ⟨359112496589798387789317081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478816662119731183719089441 359112496589798387789317081)
          ·
            refine ⟨269334372442348790841987811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359112496589798387789317081 269334372442348790841987811)
            ·
              refine ⟨404001558663523186262981717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269334372442348790841987811 404001558663523186262981717)
              ·
                refine ⟨4734393265588162339019317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 404001558663523186262981717 4734393265588162339019317)
                ·
                  refine ⟨443849368648890219283061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4734393265588162339019317 443849368648890219283061)
                  ·
                    rfl

theorem cell22_3889771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 5].length) (baseStart_3889771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889771 prefixEnd_3889771 := by exact prefixLift 3889771
  have htrace : WordTrace (prefixWord ++ tailWord_3889771) baseStart_3889771 baseEnd_3889771 := by
    simpa [prefixWord, tailWord_3889771, baseEnd_3889771] using wordTrace_append hprefix tailTrace_3889771
  have hstable : (prefixWord ++ tailWord_3889771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889771).length < 2 ^ (prefixWord ++ tailWord_3889771).sum := by decide
  have hdescent : baseEnd_3889771 < baseStart_3889771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889775 : List Nat := [1, 1, 2, 1, 3, 2, 4, 4, 1, 3]
def baseStart_3889775 : Nat := 118140960795 + 3889775 * 2 ^ 59
def prefixEnd_3889775 : Nat := 4983230072969 + 3 ^ 40 * 3889775 * 2
def baseEnd_3889775 : Nat := 1331549475228415980749171

theorem tailTrace_3889775 : CollatzResearch.WordTrace tailWord_3889775 prefixEnd_3889775 1331549475228415980749171 := by
  unfold tailWord_3889775
  simp only [CollatzResearch.WordTrace]
  refine ⟨141871749483016970525838779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94581166322011313683892519 141871749483016970525838779)
  ·
    refine ⟨212807624224525455788758169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141871749483016970525838779 212807624224525455788758169)
    ·
      refine ⟨159605718168394091841568627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212807624224525455788758169 159605718168394091841568627)
      ·
        refine ⟨239408577252591137762352941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159605718168394091841568627 239408577252591137762352941)
        ·
          refine ⟨89778216469721676660882353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239408577252591137762352941 89778216469721676660882353)
          ·
            refine ⟨67333662352291257495661765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89778216469721676660882353 67333662352291257495661765)
            ·
              refine ⟨12625061691054610780436581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67333662352291257495661765 12625061691054610780436581)
              ·
                refine ⟨2367199067072739521331859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12625061691054610780436581 2367199067072739521331859)
                ·
                  refine ⟨3550798600609109281997789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367199067072739521331859 3550798600609109281997789)
                  ·
                    refine ⟨1331549475228415980749171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3550798600609109281997789 1331549475228415980749171)
                    ·
                      rfl

theorem cell22_3889775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_3889775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889775 prefixEnd_3889775 := by exact prefixLift 3889775
  have htrace : WordTrace (prefixWord ++ tailWord_3889775) baseStart_3889775 baseEnd_3889775 := by
    simpa [prefixWord, tailWord_3889775, baseEnd_3889775] using wordTrace_append hprefix tailTrace_3889775
  have hstable : (prefixWord ++ tailWord_3889775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889775).length < 2 ^ (prefixWord ++ tailWord_3889775).sum := by decide
  have hdescent : baseEnd_3889775 < baseStart_3889775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889878 : List Nat := [5, 2, 1, 14]
def baseStart_3889878 : Nat := 118140960795 + 3889878 * 2 ^ 59
def prefixEnd_3889878 : Nat := 4983230072969 + 3 ^ 40 * 3889878 * 2
def baseEnd_3889878 : Nat := 1826590856287185247495

theorem tailTrace_3889878 : CollatzResearch.WordTrace tailWord_3889878 prefixEnd_3889878 1826590856287185247495 := by
  unfold tailWord_3889878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867219137602738694802393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94583670801095879411225525 8867219137602738694802393)
  ·
    refine ⟨6650414353202054021101795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8867219137602738694802393 6650414353202054021101795)
    ·
      refine ⟨9975621529803081031652693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650414353202054021101795 9975621529803081031652693)
      ·
        refine ⟨1826590856287185247495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9975621529803081031652693 1826590856287185247495)
        ·
          rfl

theorem cell22_3889878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 14].length) (baseStart_3889878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889878 prefixEnd_3889878 := by exact prefixLift 3889878
  have htrace : WordTrace (prefixWord ++ tailWord_3889878) baseStart_3889878 baseEnd_3889878 := by
    simpa [prefixWord, tailWord_3889878, baseEnd_3889878] using wordTrace_append hprefix tailTrace_3889878
  have hstable : (prefixWord ++ tailWord_3889878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889878).length < 2 ^ (prefixWord ++ tailWord_3889878).sum := by decide
  have hdescent : baseEnd_3889878 < baseStart_3889878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3889884 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 4]
def baseStart_3889884 : Nat := 118140960795 + 3889884 * 2 ^ 59
def prefixEnd_3889884 : Nat := 4983230072969 + 3 ^ 40 * 3889884 * 2
def baseEnd_3889884 : Nat := 443862262718658676591279

theorem tailTrace_3889884 : CollatzResearch.WordTrace tailWord_3889884 prefixEnd_3889884 443862262718658676591279 := by
  unfold tailWord_3889884
  simp only [CollatzResearch.WordTrace]
  refine ⟨70937862519811041070778353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94583816693081388094371137 70937862519811041070778353)
  ·
    refine ⟨53203396889858280803083765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70937862519811041070778353 53203396889858280803083765)
    ·
      refine ⟨4987818458424213825289103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53203396889858280803083765 4987818458424213825289103)
      ·
        refine ⟨7481727687636320737933655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4987818458424213825289103 7481727687636320737933655)
        ·
          refine ⟨11222591531454481106900483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7481727687636320737933655 11222591531454481106900483)
          ·
            refine ⟨16833887297181721660350725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11222591531454481106900483 16833887297181721660350725)
            ·
              refine ⟨3156353868221572811315761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16833887297181721660350725 3156353868221572811315761)
              ·
                refine ⟨2367265401166179608486821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156353868221572811315761 2367265401166179608486821)
                ·
                  refine ⟨443862262718658676591279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367265401166179608486821 443862262718658676591279)
                  ·
                    rfl

theorem cell22_3889884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_3889884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3889884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3889884 prefixEnd_3889884 := by exact prefixLift 3889884
  have htrace : WordTrace (prefixWord ++ tailWord_3889884) baseStart_3889884 baseEnd_3889884 := by
    simpa [prefixWord, tailWord_3889884, baseEnd_3889884] using wordTrace_append hprefix tailTrace_3889884
  have hstable : (prefixWord ++ tailWord_3889884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3889884).length < 2 ^ (prefixWord ++ tailWord_3889884).sum := by decide
  have hdescent : baseEnd_3889884 < baseStart_3889884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3889884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890000 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_3890000 : Nat := 118140960795 + 3890000 * 2 ^ 59
def prefixEnd_3890000 : Nat := 4983230072969 + 3 ^ 40 * 3890000 * 2
def baseEnd_3890000 : Nat := 1331626497326590393873481

theorem tailTrace_3890000 : CollatzResearch.WordTrace tailWord_3890000 prefixEnd_3890000 1331626497326590393873481 := by
  unfold tailWord_3890000
  simp only [CollatzResearch.WordTrace]
  refine ⟨70939977953600916976389727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94586637271467889301852969 70939977953600916976389727)
  ·
    refine ⟨106409966930401375464584591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70939977953600916976389727 106409966930401375464584591)
    ·
      refine ⟨159614950395602063196876887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106409966930401375464584591 159614950395602063196876887)
      ·
        refine ⟨239422425593403094795315331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159614950395602063196876887 239422425593403094795315331)
        ·
          refine ⟨359133638390104642192972997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239422425593403094795315331 359133638390104642192972997)
          ·
            refine ⟨67337557198144620411182437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359133638390104642192972997 67337557198144620411182437)
            ·
              refine ⟨12625791974652116327096707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67337557198144620411182437 12625791974652116327096707)
              ·
                refine ⟨18938687961978174490645061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12625791974652116327096707 18938687961978174490645061)
                ·
                  refine ⟨3551003992870907716995949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18938687961978174490645061 3551003992870907716995949)
                  ·
                    refine ⟨1331626497326590393873481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551003992870907716995949 1331626497326590393873481)
                    ·
                      rfl

theorem cell22_3890000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_3890000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890000 prefixEnd_3890000 := by exact prefixLift 3890000
  have htrace : WordTrace (prefixWord ++ tailWord_3890000) baseStart_3890000 baseEnd_3890000 := by
    simpa [prefixWord, tailWord_3890000, baseEnd_3890000] using wordTrace_append hprefix tailTrace_3890000
  have hstable : (prefixWord ++ tailWord_3890000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890000).length < 2 ^ (prefixWord ++ tailWord_3890000).sum := by decide
  have hdescent : baseEnd_3890000 < baseStart_3890000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890102 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3890102 : Nat := 118140960795 + 3890102 * 2 ^ 59
def prefixEnd_3890102 : Nat := 4983230072969 + 3 ^ 40 * 3890102 * 2
def baseEnd_3890102 : Nat := 1331661414011096127823169

theorem tailTrace_3890102 : CollatzResearch.WordTrace tailWord_3890102 prefixEnd_3890102 1331661414011096127823169 := by
  unfold tailWord_3890102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867729759552019085812035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94589117435221536915328373 8867729759552019085812035)
  ·
    refine ⟨13301594639328028628718053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8867729759552019085812035 13301594639328028628718053)
    ·
      refine ⟨2494048994874005367884635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13301594639328028628718053 2494048994874005367884635)
      ·
        refine ⟨3741073492311008051826953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494048994874005367884635 3741073492311008051826953)
        ·
          refine ⟨2805805119233256038870215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741073492311008051826953 2805805119233256038870215)
          ·
            refine ⟨4208707678849884058305323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2805805119233256038870215 4208707678849884058305323)
            ·
              refine ⟨6313061518274826087457985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208707678849884058305323 6313061518274826087457985)
              ·
                refine ⟨4734796138706119565593489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313061518274826087457985 4734796138706119565593489)
                ·
                  refine ⟨3551097104029589674195117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734796138706119565593489 3551097104029589674195117)
                  ·
                    refine ⟨1331661414011096127823169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551097104029589674195117 1331661414011096127823169)
                    ·
                      rfl

theorem cell22_3890102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3890102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890102 prefixEnd_3890102 := by exact prefixLift 3890102
  have htrace : WordTrace (prefixWord ++ tailWord_3890102) baseStart_3890102 baseEnd_3890102 := by
    simpa [prefixWord, tailWord_3890102, baseEnd_3890102] using wordTrace_append hprefix tailTrace_3890102
  have hstable : (prefixWord ++ tailWord_3890102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890102).length < 2 ^ (prefixWord ++ tailWord_3890102).sum := by decide
  have hdescent : baseEnd_3890102 < baseStart_3890102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890109 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3890109 : Nat := 118140960795 + 3890109 * 2 ^ 59
def prefixEnd_3890109 : Nat := 4983230072969 + 3 ^ 40 * 3890109 * 2
def baseEnd_3890109 : Nat := 443887936751383480966049

theorem tailTrace_3890109 : CollatzResearch.WordTrace tailWord_3890109 prefixEnd_3890109 443887936751383480966049 := by
  unfold tailWord_3890109
  simp only [CollatzResearch.WordTrace]
  refine ⟨141883931463806945568497381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94589287642537963712331587 141883931463806945568497381)
  ·
    refine ⟨26603237149463802294093259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141883931463806945568497381 26603237149463802294093259)
    ·
      refine ⟨39904855724195703441139889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26603237149463802294093259 39904855724195703441139889)
      ·
        refine ⟨29928641793146777580854917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39904855724195703441139889 29928641793146777580854917)
        ·
          refine ⟨5611620336215020796410297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29928641793146777580854917 5611620336215020796410297)
          ·
            refine ⟨4208715252161265597307723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5611620336215020796410297 4208715252161265597307723)
            ·
              refine ⟨6313072878241898395961585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4208715252161265597307723 6313072878241898395961585)
              ·
                refine ⟨4734804658681423796971189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6313072878241898395961585 4734804658681423796971189)
                ·
                  refine ⟨443887936751383480966049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4734804658681423796971189 443887936751383480966049)
                  ·
                    rfl

theorem cell22_3890109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3890109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890109 prefixEnd_3890109 := by exact prefixLift 3890109
  have htrace : WordTrace (prefixWord ++ tailWord_3890109) baseStart_3890109 baseEnd_3890109 := by
    simpa [prefixWord, tailWord_3890109, baseEnd_3890109] using wordTrace_append hprefix tailTrace_3890109
  have hstable : (prefixWord ++ tailWord_3890109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890109).length < 2 ^ (prefixWord ++ tailWord_3890109).sum := by decide
  have hdescent : baseEnd_3890109 < baseStart_3890109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890135 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_3890135 : Nat := 118140960795 + 3890135 * 2 ^ 59
def prefixEnd_3890135 : Nat := 4983230072969 + 3 ^ 40 * 3890135 * 2
def baseEnd_3890135 : Nat := 1331672710585495041748067

theorem tailTrace_3890135 : CollatzResearch.WordTrace tailWord_3890135 prefixEnd_3890135 1331672710585495041748067 := by
  unfold tailWord_3890135
  simp only [CollatzResearch.WordTrace]
  refine ⟨141884879761712752008943859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94589919841141834672629239 141884879761712752008943859)
  ·
    refine ⟨212827319642569128013415789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141884879761712752008943859 212827319642569128013415789)
    ·
      refine ⟨79810244865963423005030921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212827319642569128013415789 79810244865963423005030921)
      ·
        refine ⟨59857683649472567253773191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79810244865963423005030921 59857683649472567253773191)
        ·
          refine ⟨89786525474208850880659787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59857683649472567253773191 89786525474208850880659787)
          ·
            refine ⟨134679788211313276320989681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89786525474208850880659787 134679788211313276320989681)
            ·
              refine ⟨101009841158484957240742261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134679788211313276320989681 101009841158484957240742261)
              ·
                refine ⟨9469672608607964741319587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101009841158484957240742261 9469672608607964741319587)
                ·
                  refine ⟨14204508912911947111979381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9469672608607964741319587 14204508912911947111979381)
                  ·
                    refine ⟨1331672710585495041748067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14204508912911947111979381 1331672710585495041748067)
                    ·
                      rfl

theorem cell22_3890135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_3890135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890135 prefixEnd_3890135 := by exact prefixLift 3890135
  have htrace : WordTrace (prefixWord ++ tailWord_3890135) baseStart_3890135 baseEnd_3890135 := by
    simpa [prefixWord, tailWord_3890135, baseEnd_3890135] using wordTrace_append hprefix tailTrace_3890135
  have hstable : (prefixWord ++ tailWord_3890135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890135).length < 2 ^ (prefixWord ++ tailWord_3890135).sum := by decide
  have hdescent : baseEnd_3890135 < baseStart_3890135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890152 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3890152 : Nat := 118140960795 + 3890152 * 2 ^ 59
def prefixEnd_3890152 : Nat := 4983230072969 + 3 ^ 40 * 3890152 * 2
def baseEnd_3890152 : Nat := 1331678530032912664073015

theorem tailTrace_3890152 : CollatzResearch.WordTrace tailWord_3890152 prefixEnd_3890152 1331678530032912664073015 := by
  unfold tailWord_3890152
  simp only [CollatzResearch.WordTrace]
  refine ⟨70942749901325581956156355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94590333201767442608208473 70942749901325581956156355)
  ·
    refine ⟨106414124851988372934234533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70942749901325581956156355 106414124851988372934234533)
    ·
      refine ⟨19952648409747819925168975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106414124851988372934234533 19952648409747819925168975)
      ·
        refine ⟨29928972614621729887753463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19952648409747819925168975 29928972614621729887753463)
        ·
          refine ⟨44893458921932594831630195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29928972614621729887753463 44893458921932594831630195)
          ·
            refine ⟨67340188382898892247445293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44893458921932594831630195 67340188382898892247445293)
            ·
              refine ⟨25252570643587084592791985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67340188382898892247445293 25252570643587084592791985)
              ·
                refine ⟨18939427982690313444593989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25252570643587084592791985 18939427982690313444593989)
                ·
                  refine ⟨3551142746754433770861373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18939427982690313444593989 3551142746754433770861373)
                  ·
                    refine ⟨1331678530032912664073015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551142746754433770861373 1331678530032912664073015)
                    ·
                      rfl

theorem cell22_3890152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3890152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890152 prefixEnd_3890152 := by exact prefixLift 3890152
  have htrace : WordTrace (prefixWord ++ tailWord_3890152) baseStart_3890152 baseEnd_3890152 := by
    simpa [prefixWord, tailWord_3890152, baseEnd_3890152] using wordTrace_append hprefix tailTrace_3890152
  have hstable : (prefixWord ++ tailWord_3890152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890152).length < 2 ^ (prefixWord ++ tailWord_3890152).sum := by decide
  have hdescent : baseEnd_3890152 < baseStart_3890152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890154 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_3890154 : Nat := 118140960795 + 3890154 * 2 ^ 59
def prefixEnd_3890154 : Nat := 4983230072969 + 3 ^ 40 * 3890154 * 2
def baseEnd_3890154 : Nat := 443893071557928441841003

theorem tailTrace_3890154 : CollatzResearch.WordTrace tailWord_3890154 prefixEnd_3890154 443893071557928441841003 := by
  unfold tailWord_3890154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471393187160979563471379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94590381832429278835923677 35471393187160979563471379)
  ·
    refine ⟨53207089780741469345207069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35471393187160979563471379 53207089780741469345207069)
    ·
      refine ⟨19952658667778051004452651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53207089780741469345207069 19952658667778051004452651)
      ·
        refine ⟨29928988001667076506678977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19952658667778051004452651 29928988001667076506678977)
        ·
          refine ⟨22446741001250307380009233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29928988001667076506678977 22446741001250307380009233)
          ·
            refine ⟨16835055750937730535006925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22446741001250307380009233 16835055750937730535006925)
            ·
              refine ⟨6313145906601648950627597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16835055750937730535006925 6313145906601648950627597)
              ·
                refine ⟨2367429714975618356485349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6313145906601648950627597 2367429714975618356485349)
                ·
                  refine ⟨443893071557928441841003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367429714975618356485349 443893071557928441841003)
                  ·
                    rfl

theorem cell22_3890154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_3890154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890154 prefixEnd_3890154 := by exact prefixLift 3890154
  have htrace : WordTrace (prefixWord ++ tailWord_3890154) baseStart_3890154 baseEnd_3890154 := by
    simpa [prefixWord, tailWord_3890154, baseEnd_3890154] using wordTrace_append hprefix tailTrace_3890154
  have hstable : (prefixWord ++ tailWord_3890154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890154).length < 2 ^ (prefixWord ++ tailWord_3890154).sum := by decide
  have hdescent : baseEnd_3890154 < baseStart_3890154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890164 : List Nat := [2, 6, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3890164 : Nat := 118140960795 + 3890164 * 2 ^ 59
def prefixEnd_3890164 : Nat := 4983230072969 + 3 ^ 40 * 3890164 * 2
def baseEnd_3890164 : Nat := 1331682637878148632772979

theorem tailTrace_3890164 : CollatzResearch.WordTrace tailWord_3890164 prefixEnd_3890164 1331682637878148632772979 := by
  unfold tailWord_3890164
  simp only [CollatzResearch.WordTrace]
  refine ⟨70942968739303844980874773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94590624985738459974499697 70942968739303844980874773)
  ·
    refine ⟨3325451659654867733478505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70942968739303844980874773 3325451659654867733478505)
    ·
      refine ⟨2494088744741150800108879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3325451659654867733478505 2494088744741150800108879)
      ·
        refine ⟨3741133117111726200163319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494088744741150800108879 3741133117111726200163319)
        ·
          refine ⟨5611699675667589300244979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741133117111726200163319 5611699675667589300244979)
          ·
            refine ⟨8417549513501383950367469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611699675667589300244979 8417549513501383950367469)
            ·
              refine ⟨3156581067563018981387801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8417549513501383950367469 3156581067563018981387801)
              ·
                refine ⟨2367435800672264236040851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156581067563018981387801 2367435800672264236040851)
                ·
                  refine ⟨3551153701008396354061277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367435800672264236040851 3551153701008396354061277)
                  ·
                    refine ⟨1331682637878148632772979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551153701008396354061277 1331682637878148632772979)
                    ·
                      rfl

theorem cell22_3890164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3890164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890164 prefixEnd_3890164 := by exact prefixLift 3890164
  have htrace : WordTrace (prefixWord ++ tailWord_3890164) baseStart_3890164 baseEnd_3890164 := by
    simpa [prefixWord, tailWord_3890164, baseEnd_3890164] using wordTrace_append hprefix tailTrace_3890164
  have hstable : (prefixWord ++ tailWord_3890164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890164).length < 2 ^ (prefixWord ++ tailWord_3890164).sum := by decide
  have hdescent : baseEnd_3890164 < baseStart_3890164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890186 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_3890186 : Nat := 118140960795 + 3890186 * 2 ^ 59
def prefixEnd_3890186 : Nat := 4983230072969 + 3 ^ 40 * 3890186 * 2
def baseEnd_3890186 : Nat := 1331690168927747908722911

theorem tailTrace_3890186 : CollatzResearch.WordTrace tailWord_3890186 prefixEnd_3890186 1331690168927747908722911 := by
  unfold tailWord_3890186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35471684971131996929762603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94591159923018658479366941 35471684971131996929762603)
  ·
    refine ⟨53207527456697995394643905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35471684971131996929762603 53207527456697995394643905)
    ·
      refine ⟨39905645592523496545982929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53207527456697995394643905 39905645592523496545982929)
      ·
        refine ⟨29929234194392622409487197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39905645592523496545982929 29929234194392622409487197)
        ·
          refine ⟨11223462822897233403557699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29929234194392622409487197 11223462822897233403557699)
          ·
            refine ⟨16835194234345850105336549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223462822897233403557699 16835194234345850105336549)
            ·
              refine ⟨3156598918939846894750603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16835194234345850105336549 3156598918939846894750603)
              ·
                refine ⟨4734898378409770342125905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156598918939846894750603 4734898378409770342125905)
                ·
                  refine ⟨3551173783807327756594429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4734898378409770342125905 3551173783807327756594429)
                  ·
                    refine ⟨1331690168927747908722911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551173783807327756594429 1331690168927747908722911)
                    ·
                      rfl

theorem cell22_3890186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_3890186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890186 prefixEnd_3890186 := by exact prefixLift 3890186
  have htrace : WordTrace (prefixWord ++ tailWord_3890186) baseStart_3890186 baseEnd_3890186 := by
    simpa [prefixWord, tailWord_3890186, baseEnd_3890186] using wordTrace_append hprefix tailTrace_3890186
  have hstable : (prefixWord ++ tailWord_3890186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890186).length < 2 ^ (prefixWord ++ tailWord_3890186).sum := by decide
  have hdescent : baseEnd_3890186 < baseStart_3890186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890257 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_3890257 : Nat := 118140960795 + 3890257 * 2 ^ 59
def prefixEnd_3890257 : Nat := 4983230072969 + 3 ^ 40 * 3890257 * 2
def baseEnd_3890257 : Nat := 1331714473678727390197693

theorem tailTrace_3890257 : CollatzResearch.WordTrace tailWord_3890257 prefixEnd_3890257 1331714473678727390197693 := by
  unfold tailWord_3890257
  simp only [CollatzResearch.WordTrace]
  refine ⟨141889329467270766844885025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94592886311513844563256683 141889329467270766844885025)
  ·
    refine ⟨106416997100453075133663769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141889329467270766844885025 106416997100453075133663769)
    ·
      refine ⟨79812747825339806350247827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106416997100453075133663769 79812747825339806350247827)
      ·
        refine ⟨119719121738009709525371741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79812747825339806350247827 119719121738009709525371741)
        ·
          refine ⟨44894670651753641072014403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119719121738009709525371741 44894670651753641072014403)
          ·
            refine ⟨67342005977630461608021605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44894670651753641072014403 67342005977630461608021605)
            ·
              refine ⟨12626626120805711551504051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67342005977630461608021605 12626626120805711551504051)
              ·
                refine ⟨18939939181208567327256077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12626626120805711551504051 18939939181208567327256077)
                ·
                  refine ⟨7102477192953212747721029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18939939181208567327256077 7102477192953212747721029)
                  ·
                    refine ⟨1331714473678727390197693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102477192953212747721029 1331714473678727390197693)
                    ·
                      rfl

theorem cell22_3890257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_3890257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890257 prefixEnd_3890257 := by exact prefixLift 3890257
  have htrace : WordTrace (prefixWord ++ tailWord_3890257) baseStart_3890257 baseEnd_3890257 := by
    simpa [prefixWord, tailWord_3890257, baseEnd_3890257] using wordTrace_append hprefix tailTrace_3890257
  have hstable : (prefixWord ++ tailWord_3890257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890257).length < 2 ^ (prefixWord ++ tailWord_3890257).sum := by decide
  have hdescent : baseEnd_3890257 < baseStart_3890257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890304 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 2, 3]
def baseStart_3890304 : Nat := 118140960795 + 3890304 * 2 ^ 59
def prefixEnd_3890304 : Nat := 4983230072969 + 3 ^ 40 * 3890304 * 2
def baseEnd_3890304 : Nat := 1331730562739234934272549

theorem tailTrace_3890304 : CollatzResearch.WordTrace tailWord_3890304 prefixEnd_3890304 1331730562739234934272549 := by
  unfold tailWord_3890304
  simp only [CollatzResearch.WordTrace]
  refine ⟨70945521849050246935922983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94594029132066995914563977 70945521849050246935922983)
  ·
    refine ⟨106418282773575370403884475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70945521849050246935922983 106418282773575370403884475)
    ·
      refine ⟨159627424160363055605826713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106418282773575370403884475 159627424160363055605826713)
      ·
        refine ⟨119720568120272291704370035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159627424160363055605826713 119720568120272291704370035)
        ·
          refine ⟨179580852180408437556555053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119720568120272291704370035 179580852180408437556555053)
          ·
            refine ⟨67342819567653164083708145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179580852180408437556555053 67342819567653164083708145)
            ·
              refine ⟨50507114675739873062781109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67342819567653164083708145 50507114675739873062781109)
              ·
                refine ⟨4735042000850613099635729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50507114675739873062781109 4735042000850613099635729)
                ·
                  refine ⟨3551281500637959824726797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4735042000850613099635729 3551281500637959824726797)
                  ·
                    refine ⟨1331730562739234934272549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551281500637959824726797 1331730562739234934272549)
                    ·
                      rfl

theorem cell22_3890304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 3].length) (baseStart_3890304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890304 prefixEnd_3890304 := by exact prefixLift 3890304
  have htrace : WordTrace (prefixWord ++ tailWord_3890304) baseStart_3890304 baseEnd_3890304 := by
    simpa [prefixWord, tailWord_3890304, baseEnd_3890304] using wordTrace_append hprefix tailTrace_3890304
  have hstable : (prefixWord ++ tailWord_3890304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890304).length < 2 ^ (prefixWord ++ tailWord_3890304).sum := by decide
  have hdescent : baseEnd_3890304 < baseStart_3890304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890334 : List Nat := [4, 3, 1, 1, 2, 1, 10]
def baseStart_3890334 : Nat := 118140960795 + 3890334 * 2 ^ 59
def prefixEnd_3890334 : Nat := 4983230072969 + 3 ^ 40 * 3890334 * 2
def baseEnd_3890334 : Nat := 49323734531567587260091

theorem tailTrace_3890334 : CollatzResearch.WordTrace tailWord_3890334 prefixEnd_3890334 49323734531567587260091 := by
  unfold tailWord_3890334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17736517235998976124429757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94594758591994539330292037 17736517235998976124429757)
  ·
    refine ⟨6651193963499616046661159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17736517235998976124429757 6651193963499616046661159)
    ·
      refine ⟨9976790945249424069991739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651193963499616046661159 9976790945249424069991739)
      ·
        refine ⟨14965186417874136104987609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9976790945249424069991739 14965186417874136104987609)
        ·
          refine ⟨11223889813405602078740707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14965186417874136104987609 11223889813405602078740707)
          ·
            refine ⟨16835834720108403118111061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11223889813405602078740707 16835834720108403118111061)
            ·
              refine ⟨49323734531567587260091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16835834720108403118111061 49323734531567587260091)
              ·
                rfl

theorem cell22_3890334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 10].length) (baseStart_3890334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890334 prefixEnd_3890334 := by exact prefixLift 3890334
  have htrace : WordTrace (prefixWord ++ tailWord_3890334) baseStart_3890334 baseEnd_3890334 := by
    simpa [prefixWord, tailWord_3890334, baseEnd_3890334] using wordTrace_append hprefix tailTrace_3890334
  have hstable : (prefixWord ++ tailWord_3890334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890334).length < 2 ^ (prefixWord ++ tailWord_3890334).sum := by decide
  have hdescent : baseEnd_3890334 < baseStart_3890334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890370 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3890370 : Nat := 118140960795 + 3890370 * 2 ^ 59
def prefixEnd_3890370 : Nat := 4983230072969 + 3 ^ 40 * 3890370 * 2
def baseEnd_3890370 : Nat := 1331753155888032762122347

theorem tailTrace_3890370 : CollatzResearch.WordTrace tailWord_3890370 prefixEnd_3890370 1331753155888032762122347 := by
  unfold tailWord_3890370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35473362728965346785937141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94595633943907591429165709 35473362728965346785937141)
  ·
    refine ⟨3325627755840501261181607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35473362728965346785937141 3325627755840501261181607)
    ·
      refine ⟨4988441633760751891772411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3325627755840501261181607 4988441633760751891772411)
      ·
        refine ⟨7482662450641127837658617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4988441633760751891772411 7482662450641127837658617)
        ·
          refine ⟨5611996837980845878243963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7482662450641127837658617 5611996837980845878243963)
          ·
            refine ⟨8417995256971268817365945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5611996837980845878243963 8417995256971268817365945)
            ·
              refine ⟨6313496442728451613024459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8417995256971268817365945 6313496442728451613024459)
              ·
                refine ⟨9470244664092677419536689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6313496442728451613024459 9470244664092677419536689)
                ·
                  refine ⟨7102683498069508064652517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9470244664092677419536689 7102683498069508064652517)
                  ·
                    refine ⟨1331753155888032762122347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102683498069508064652517 1331753155888032762122347)
                    ·
                      rfl

theorem cell22_3890370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3890370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890370 prefixEnd_3890370 := by exact prefixLift 3890370
  have htrace : WordTrace (prefixWord ++ tailWord_3890370) baseStart_3890370 baseEnd_3890370 := by
    simpa [prefixWord, tailWord_3890370, baseEnd_3890370] using wordTrace_append hprefix tailTrace_3890370
  have hstable : (prefixWord ++ tailWord_3890370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890370).length < 2 ^ (prefixWord ++ tailWord_3890370).sum := by decide
  have hdescent : baseEnd_3890370 < baseStart_3890370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890400 : List Nat := [2, 1, 1, 3, 1, 6, 2, 2, 1, 3]
def baseStart_3890400 : Nat := 118140960795 + 3890400 * 2 ^ 59
def prefixEnd_3890400 : Nat := 4983230072969 + 3 ^ 40 * 3890400 * 2
def baseEnd_3890400 : Nat := 1331763425501122683872255

theorem tailTrace_3890400 : CollatzResearch.WordTrace tailWord_3890400 prefixEnd_3890400 1331763425501122683872255 := by
  unfold tailWord_3890400
  simp only [CollatzResearch.WordTrace]
  refine ⟨70947272552876351133670327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94596363403835134844893769 70947272552876351133670327)
  ·
    refine ⟨106420908829314526700505491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70947272552876351133670327 106420908829314526700505491)
    ·
      refine ⟨159631363243971790050758237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106420908829314526700505491 159631363243971790050758237)
      ·
        refine ⟨59861761216489421269034339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159631363243971790050758237 59861761216489421269034339)
        ·
          refine ⟨89792641824734131903551509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59861761216489421269034339 89792641824734131903551509)
          ·
            refine ⟨4209030085534412432978977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89792641824734131903551509 4209030085534412432978977)
            ·
              refine ⟨3156772564150809324734233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209030085534412432978977 3156772564150809324734233)
              ·
                refine ⟨2367579423113106993550675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156772564150809324734233 2367579423113106993550675)
                ·
                  refine ⟨3551369134669660490326013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367579423113106993550675 3551369134669660490326013)
                  ·
                    refine ⟨1331763425501122683872255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551369134669660490326013 1331763425501122683872255)
                    ·
                      rfl

theorem cell22_3890400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 2, 1, 3].length) (baseStart_3890400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890400 prefixEnd_3890400 := by exact prefixLift 3890400
  have htrace : WordTrace (prefixWord ++ tailWord_3890400) baseStart_3890400 baseEnd_3890400 := by
    simpa [prefixWord, tailWord_3890400, baseEnd_3890400] using wordTrace_append hprefix tailTrace_3890400
  have hstable : (prefixWord ++ tailWord_3890400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890400).length < 2 ^ (prefixWord ++ tailWord_3890400).sum := by decide
  have hdescent : baseEnd_3890400 < baseStart_3890400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890441 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 4]
def baseStart_3890441 : Nat := 118140960795 + 3890441 * 2 ^ 59
def prefixEnd_3890441 : Nat := 4983230072969 + 3 ^ 40 * 3890441 * 2
def baseEnd_3890441 : Nat := 443925820213004081199043

theorem tailTrace_3890441 : CollatzResearch.WordTrace tailWord_3890441 prefixEnd_3890441 443925820213004081199043 := by
  unfold tailWord_3890441
  simp only [CollatzResearch.WordTrace]
  refine ⟨141896040498604166269583177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94597360332402777513055451 141896040498604166269583177)
  ·
    refine ⟨106422030373953124702187383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141896040498604166269583177 106422030373953124702187383)
    ·
      refine ⟨159633045560929687053281075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106422030373953124702187383 159633045560929687053281075)
      ·
        refine ⟨239449568341394530579921613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159633045560929687053281075 239449568341394530579921613)
        ·
          refine ⟨89793588128022948967470605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239449568341394530579921613 89793588128022948967470605)
          ·
            refine ⟨33672595548008605862801477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89793588128022948967470605 33672595548008605862801477)
            ·
              refine ⟨6313611665251613599275277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33672595548008605862801477 6313611665251613599275277)
              ·
                refine ⟨2367604374469355099728229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6313611665251613599275277 2367604374469355099728229)
                ·
                  refine ⟨443925820213004081199043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367604374469355099728229 443925820213004081199043)
                  ·
                    rfl

theorem cell22_3890441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_3890441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890441 prefixEnd_3890441 := by exact prefixLift 3890441
  have htrace : WordTrace (prefixWord ++ tailWord_3890441) baseStart_3890441 baseEnd_3890441 := by
    simpa [prefixWord, tailWord_3890441, baseEnd_3890441] using wordTrace_append hprefix tailTrace_3890441
  have hstable : (prefixWord ++ tailWord_3890441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890441).length < 2 ^ (prefixWord ++ tailWord_3890441).sum := by decide
  have hdescent : baseEnd_3890441 < baseStart_3890441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890443 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 1, 4]
def baseStart_3890443 : Nat := 118140960795 + 3890443 * 2 ^ 59
def prefixEnd_3890443 : Nat := 4983230072969 + 3 ^ 40 * 3890443 * 2
def baseEnd_3890443 : Nat := 1331778145279884905047123

theorem tailTrace_3890443 : CollatzResearch.WordTrace tailWord_3890443 prefixEnd_3890443 1331778145279884905047123 := by
  unfold tailWord_3890443
  simp only [CollatzResearch.WordTrace]
  refine ⟨141896113444596920611155983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94597408963064613740770655 141896113444596920611155983)
  ·
    refine ⟨212844170166895380916733975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141896113444596920611155983 212844170166895380916733975)
    ·
      refine ⟨319266255250343071375100963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212844170166895380916733975 319266255250343071375100963)
      ·
        refine ⟨478899382875514607062651445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319266255250343071375100963 478899382875514607062651445)
        ·
          refine ⟨44896817144579494412123573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 478899382875514607062651445 44896817144579494412123573)
          ·
            refine ⟨4209076607304327601136585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44896817144579494412123573 4209076607304327601136585)
            ·
              refine ⟨3156807455478245700852439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209076607304327601136585 3156807455478245700852439)
              ·
                refine ⟨4735211183217368551278659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3156807455478245700852439 4735211183217368551278659)
                ·
                  refine ⟨7102816774826052826917989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735211183217368551278659 7102816774826052826917989)
                  ·
                    refine ⟨1331778145279884905047123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7102816774826052826917989 1331778145279884905047123)
                    ·
                      rfl

theorem cell22_3890443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 1, 4].length) (baseStart_3890443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890443 prefixEnd_3890443 := by exact prefixLift 3890443
  have htrace : WordTrace (prefixWord ++ tailWord_3890443) baseStart_3890443 baseEnd_3890443 := by
    simpa [prefixWord, tailWord_3890443, baseEnd_3890443] using wordTrace_append hprefix tailTrace_3890443
  have hstable : (prefixWord ++ tailWord_3890443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890443).length < 2 ^ (prefixWord ++ tailWord_3890443).sum := by decide
  have hdescent : baseEnd_3890443 < baseStart_3890443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890456 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_3890456 : Nat := 118140960795 + 3890456 * 2 ^ 59
def prefixEnd_3890456 : Nat := 4983230072969 + 3 ^ 40 * 3890456 * 2
def baseEnd_3890456 : Nat := 1331782595445557204472083

theorem tailTrace_3890456 : CollatzResearch.WordTrace tailWord_3890456 prefixEnd_3890456 1331782595445557204472083 := by
  unfold tailWord_3890456
  simp only [CollatzResearch.WordTrace]
  refine ⟨70948293796774911915689611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94597725062366549220919481 70948293796774911915689611)
  ·
    refine ⟨106422440695162367873534417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70948293796774911915689611 106422440695162367873534417)
    ·
      refine ⟨79816830521371775905150813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106422440695162367873534417 79816830521371775905150813)
      ·
        refine ⟨29931311445514415964431555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79816830521371775905150813 29931311445514415964431555)
        ·
          refine ⟨44896967168271623946647333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29931311445514415964431555 44896967168271623946647333)
          ·
            refine ⟨8418181344050929489996375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44896967168271623946647333 8418181344050929489996375)
            ·
              refine ⟨12627272016076394234994563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418181344050929489996375 12627272016076394234994563)
              ·
                refine ⟨18940908024114591352491845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12627272016076394234994563 18940908024114591352491845)
                ·
                  refine ⟨3551420254521485878592221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18940908024114591352491845 3551420254521485878592221)
                  ·
                    refine ⟨1331782595445557204472083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551420254521485878592221 1331782595445557204472083)
                    ·
                      rfl

theorem cell22_3890456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_3890456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890456 prefixEnd_3890456 := by exact prefixLift 3890456
  have htrace : WordTrace (prefixWord ++ tailWord_3890456) baseStart_3890456 baseEnd_3890456 := by
    simpa [prefixWord, tailWord_3890456, baseEnd_3890456] using wordTrace_append hprefix tailTrace_3890456
  have hstable : (prefixWord ++ tailWord_3890456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890456).length < 2 ^ (prefixWord ++ tailWord_3890456).sum := by decide
  have hdescent : baseEnd_3890456 < baseStart_3890456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890529 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3890529 : Nat := 118140960795 + 3890529 * 2 ^ 59
def prefixEnd_3890529 : Nat := 4983230072969 + 3 ^ 40 * 3890529 * 2
def baseEnd_3890529 : Nat := 1331807584837409347396859

theorem tailTrace_3890529 : CollatzResearch.WordTrace tailWord_3890529 prefixEnd_3890529 1331807584837409347396859 := by
  unfold tailWord_3890529
  simp only [CollatzResearch.WordTrace]
  refine ⟨141899250122285357298786641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94599500081523571532524427 141899250122285357298786641)
  ·
    refine ⟨106424437591714017974089981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141899250122285357298786641 106424437591714017974089981)
    ·
      refine ⟨39909164096892756740283743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106424437591714017974089981 39909164096892756740283743)
      ·
        refine ⟨59863746145339135110425615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39909164096892756740283743 59863746145339135110425615)
        ·
          refine ⟨89795619218008702665638423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59863746145339135110425615 89795619218008702665638423)
          ·
            refine ⟨134693428827013053998457635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89795619218008702665638423 134693428827013053998457635)
            ·
              refine ⟨202040143240519580997686453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134693428827013053998457635 202040143240519580997686453)
              ·
                refine ⟨18941263428798710718533105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202040143240519580997686453 18941263428798710718533105)
                ·
                  refine ⟨14205947571599033038899829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18941263428798710718533105 14205947571599033038899829)
                  ·
                    refine ⟨1331807584837409347396859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14205947571599033038899829 1331807584837409347396859)
                    ·
                      rfl

theorem cell22_3890529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3890529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890529 prefixEnd_3890529 := by exact prefixLift 3890529
  have htrace : WordTrace (prefixWord ++ tailWord_3890529) baseStart_3890529 baseEnd_3890529 := by
    simpa [prefixWord, tailWord_3890529, baseEnd_3890529] using wordTrace_append hprefix tailTrace_3890529
  have hstable : (prefixWord ++ tailWord_3890529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890529).length < 2 ^ (prefixWord ++ tailWord_3890529).sum := by decide
  have hdescent : baseEnd_3890529 < baseStart_3890529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890531 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 5]
def baseStart_3890531 : Nat := 118140960795 + 3890531 * 2 ^ 59
def prefixEnd_3890531 : Nat := 4983230072969 + 3 ^ 40 * 3890531 * 2
def baseEnd_3890531 : Nat := 443936089826094002948951

theorem tailTrace_3890531 : CollatzResearch.WordTrace tailWord_3890531 prefixEnd_3890531 443936089826094002948951 := by
  unfold tailWord_3890531
  simp only [CollatzResearch.WordTrace]
  refine ⟨141899323068278111640359447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94599548712185407760239631 141899323068278111640359447)
  ·
    refine ⟨212848984602417167460539171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141899323068278111640359447 212848984602417167460539171)
    ·
      refine ⟨319273476903625751190808757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212848984602417167460539171 319273476903625751190808757)
      ·
        refine ⟨29931888459714914174138321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319273476903625751190808757 29931888459714914174138321)
        ·
          refine ⟨22448916344786185630603741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29931888459714914174138321 22448916344786185630603741)
          ·
            refine ⟨8418343629294819611476403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22448916344786185630603741 8418343629294819611476403)
            ·
              refine ⟨12627515443942229417214605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418343629294819611476403 12627515443942229417214605)
              ·
                refine ⟨4735318291478336031455477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12627515443942229417214605 4735318291478336031455477)
                ·
                  refine ⟨443936089826094002948951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735318291478336031455477 443936089826094002948951)
                  ·
                    rfl

theorem cell22_3890531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 5].length) (baseStart_3890531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890531 prefixEnd_3890531 := by exact prefixLift 3890531
  have htrace : WordTrace (prefixWord ++ tailWord_3890531) baseStart_3890531 baseEnd_3890531 := by
    simpa [prefixWord, tailWord_3890531, baseEnd_3890531] using wordTrace_append hprefix tailTrace_3890531
  have hstable : (prefixWord ++ tailWord_3890531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890531).length < 2 ^ (prefixWord ++ tailWord_3890531).sum := by decide
  have hdescent : baseEnd_3890531 < baseStart_3890531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890569 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 1, 3]
def baseStart_3890569 : Nat := 118140960795 + 3890569 * 2 ^ 59
def prefixEnd_3890569 : Nat := 4983230072969 + 3 ^ 40 * 3890569 * 2
def baseEnd_3890569 : Nat := 1331821277654862576396737

theorem tailTrace_3890569 : CollatzResearch.WordTrace tailWord_3890569 prefixEnd_3890569 1331821277654862576396737 := by
  unfold tailWord_3890569
  simp only [CollatzResearch.WordTrace]
  refine ⟨141900709042140444130242761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94600472694760296086828507 141900709042140444130242761)
  ·
    refine ⟨106425531781605333097682071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141900709042140444130242761 106425531781605333097682071)
    ·
      refine ⟨159638297672407999646523107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106425531781605333097682071 159638297672407999646523107)
      ·
        refine ⟨239457446508611999469784661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159638297672407999646523107 239457446508611999469784661)
        ·
          refine ⟨2806141951272796868786539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 239457446508611999469784661 2806141951272796868786539)
          ·
            refine ⟨4209212926909195303179809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806141951272796868786539 4209212926909195303179809)
            ·
              refine ⟨3156909695181896477384857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209212926909195303179809 3156909695181896477384857)
              ·
                refine ⟨2367682271386422358038643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3156909695181896477384857 2367682271386422358038643)
                ·
                  refine ⟨3551523407079633537057965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367682271386422358038643 3551523407079633537057965)
                  ·
                    refine ⟨1331821277654862576396737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551523407079633537057965 1331821277654862576396737)
                    ·
                      rfl

theorem cell22_3890569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 3].length) (baseStart_3890569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890569 prefixEnd_3890569 := by exact prefixLift 3890569
  have htrace : WordTrace (prefixWord ++ tailWord_3890569) baseStart_3890569 baseEnd_3890569 := by
    simpa [prefixWord, tailWord_3890569, baseEnd_3890569] using wordTrace_append hprefix tailTrace_3890569
  have hstable : (prefixWord ++ tailWord_3890569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890569).length < 2 ^ (prefixWord ++ tailWord_3890569).sum := by decide
  have hdescent : baseEnd_3890569 < baseStart_3890569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890591 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_3890591 : Nat := 118140960795 + 3890591 * 2 ^ 59
def prefixEnd_3890591 : Nat := 4983230072969 + 3 ^ 40 * 3890591 * 2
def baseEnd_3890591 : Nat := 1331828808704461852346669

theorem tailTrace_3890591 : CollatzResearch.WordTrace tailWord_3890591 prefixEnd_3890591 1331828808704461852346669 := by
  unfold tailWord_3890591
  simp only [CollatzResearch.WordTrace]
  refine ⟨141901511448060741887543627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94601007632040494591695751 141901511448060741887543627)
  ·
    refine ⟨212852267172091112831315441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141901511448060741887543627 212852267172091112831315441)
    ·
      refine ⟨159639200379068334623486581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212852267172091112831315441 159639200379068334623486581)
      ·
        refine ⟨14966175035537656370951867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159639200379068334623486581 14966175035537656370951867)
        ·
          refine ⟨22449262553306484556427801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966175035537656370951867 22449262553306484556427801)
          ·
            refine ⟨16836946914979863417320851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22449262553306484556427801 16836946914979863417320851)
            ·
              refine ⟨25255420372469795125981277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16836946914979863417320851 25255420372469795125981277)
              ·
                refine ⟨9470782639676173172242979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25255420372469795125981277 9470782639676173172242979)
                ·
                  refine ⟨14206173959514259758364469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9470782639676173172242979 14206173959514259758364469)
                  ·
                    refine ⟨1331828808704461852346669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14206173959514259758364469 1331828808704461852346669)
                    ·
                      rfl

theorem cell22_3890591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_3890591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890591 prefixEnd_3890591 := by exact prefixLift 3890591
  have htrace : WordTrace (prefixWord ++ tailWord_3890591) baseStart_3890591 baseEnd_3890591 := by
    simpa [prefixWord, tailWord_3890591, baseEnd_3890591] using wordTrace_append hprefix tailTrace_3890591
  have hstable : (prefixWord ++ tailWord_3890591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890591).length < 2 ^ (prefixWord ++ tailWord_3890591).sum := by decide
  have hdescent : baseEnd_3890591 < baseStart_3890591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890604 : List Nat := [2, 2, 1, 1, 1, 1, 4, 10]
def baseStart_3890604 : Nat := 118140960795 + 3890604 * 2 ^ 59
def prefixEnd_3890604 : Nat := 4983230072969 + 3 ^ 40 * 3890604 * 2
def baseEnd_3890604 : Nat := 147981473207792683530181

theorem tailTrace_3890604 : CollatzResearch.WordTrace tailWord_3890604 prefixEnd_3890604 147981473207792683530181 := by
  unfold tailWord_3890604
  simp only [CollatzResearch.WordTrace]
  refine ⟨70950992798506822553883433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94601323731342430071844577 70950992798506822553883433)
  ·
    refine ⟨53213244598880116915412575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70950992798506822553883433 53213244598880116915412575)
    ·
      refine ⟨79819866898320175373118863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53213244598880116915412575 79819866898320175373118863)
      ·
        refine ⟨119729800347480263059678295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79819866898320175373118863 119729800347480263059678295)
        ·
          refine ⟨179594700521220394589517443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119729800347480263059678295 179594700521220394589517443)
          ·
            refine ⟨269392050781830591884276165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179594700521220394589517443 269392050781830591884276165)
            ·
              refine ⟨50511009521593235978301781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269392050781830591884276165 50511009521593235978301781)
              ·
                refine ⟨147981473207792683530181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50511009521593235978301781 147981473207792683530181)
                ·
                  rfl

theorem cell22_3890604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 10].length) (baseStart_3890604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890604 prefixEnd_3890604 := by exact prefixLift 3890604
  have htrace : WordTrace (prefixWord ++ tailWord_3890604) baseStart_3890604 baseEnd_3890604 := by
    simpa [prefixWord, tailWord_3890604, baseEnd_3890604] using wordTrace_append hprefix tailTrace_3890604
  have hstable : (prefixWord ++ tailWord_3890604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890604).length < 2 ^ (prefixWord ++ tailWord_3890604).sum := by decide
  have hdescent : baseEnd_3890604 < baseStart_3890604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890745 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 4]
def baseStart_3890745 : Nat := 118140960795 + 3890745 * 2 ^ 59
def prefixEnd_3890745 : Nat := 4983230072969 + 3 ^ 40 * 3890745 * 2
def baseEnd_3890745 : Nat := 443960508683885594665399

theorem tailTrace_3890745 : CollatzResearch.WordTrace tailWord_3890745 prefixEnd_3890745 443960508683885594665399 := by
  unfold tailWord_3890745
  simp only [CollatzResearch.WordTrace]
  refine ⟨141907128289502826188649689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94604752193001884125766459 141907128289502826188649689)
  ·
    refine ⟨106430346217127119641487267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141907128289502826188649689 106430346217127119641487267)
    ·
      refine ⟨159645519325690679462230901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106430346217127119641487267 159645519325690679462230901)
      ·
        refine ⟨14966767436783501199584147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159645519325690679462230901 14966767436783501199584147)
        ·
          refine ⟨22450151155175251799376221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14966767436783501199584147 22450151155175251799376221)
          ·
            refine ⟨8418806683190719424766083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22450151155175251799376221 8418806683190719424766083)
            ·
              refine ⟨12628210024786079137149125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8418806683190719424766083 12628210024786079137149125)
              ·
                refine ⟨2367789379647389838215461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12628210024786079137149125 2367789379647389838215461)
                ·
                  refine ⟨443960508683885594665399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2367789379647389838215461 443960508683885594665399)
                  ·
                    rfl

theorem cell22_3890745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 4].length) (baseStart_3890745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890745 prefixEnd_3890745 := by exact prefixLift 3890745
  have htrace : WordTrace (prefixWord ++ tailWord_3890745) baseStart_3890745 baseEnd_3890745 := by
    simpa [prefixWord, tailWord_3890745, baseEnd_3890745] using wordTrace_append hprefix tailTrace_3890745
  have hstable : (prefixWord ++ tailWord_3890745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890745).length < 2 ^ (prefixWord ++ tailWord_3890745).sum := by decide
  have hdescent : baseEnd_3890745 < baseStart_3890745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890775 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 2, 4]
def baseStart_3890775 : Nat := 118140960795 + 3890775 * 2 ^ 59
def prefixEnd_3890775 : Nat := 4983230072969 + 3 ^ 40 * 3890775 * 2
def baseEnd_3890775 : Nat := 1331891795664746705746105

theorem tailTrace_3890775 : CollatzResearch.WordTrace tailWord_3890775 prefixEnd_3890775 1331891795664746705746105 := by
  unfold tailWord_3890775
  simp only [CollatzResearch.WordTrace]
  refine ⟨141908222479394141312241779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94605481652929427541494519 141908222479394141312241779)
  ·
    refine ⟨212862333719091211968362669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141908222479394141312241779 212862333719091211968362669)
    ·
      refine ⟨79823375144659204488136001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212862333719091211968362669 79823375144659204488136001)
      ·
        refine ⟨59867531358494403366102001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79823375144659204488136001 59867531358494403366102001)
        ·
          refine ⟨44900648518870802524576501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59867531358494403366102001 44900648518870802524576501)
          ·
            refine ⟨4209435798644137736679047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44900648518870802524576501 4209435798644137736679047)
            ·
              refine ⟨6314153697966206605018571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209435798644137736679047 6314153697966206605018571)
              ·
                refine ⟨9471230546949309907527857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6314153697966206605018571 9471230546949309907527857)
                ·
                  refine ⟨7103422910211982430645893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9471230546949309907527857 7103422910211982430645893)
                  ·
                    refine ⟨1331891795664746705746105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103422910211982430645893 1331891795664746705746105)
                    ·
                      rfl

theorem cell22_3890775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_3890775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890775 prefixEnd_3890775 := by exact prefixLift 3890775
  have htrace : WordTrace (prefixWord ++ tailWord_3890775) baseStart_3890775 baseEnd_3890775 := by
    simpa [prefixWord, tailWord_3890775, baseEnd_3890775] using wordTrace_append hprefix tailTrace_3890775
  have hstable : (prefixWord ++ tailWord_3890775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890775).length < 2 ^ (prefixWord ++ tailWord_3890775).sum := by decide
  have hdescent : baseEnd_3890775 < baseStart_3890775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890781 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3890781 : Nat := 118140960795 + 3890781 * 2 ^ 59
def prefixEnd_3890781 : Nat := 4983230072969 + 3 ^ 40 * 3890781 * 2
def baseEnd_3890781 : Nat := 1331893849587364690096087

theorem tailTrace_3890781 : CollatzResearch.WordTrace tailWord_3890781 prefixEnd_3890781 1331893849587364690096087 := by
  unfold tailWord_3890781
  simp only [CollatzResearch.WordTrace]
  refine ⟨141908441317372404336960197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94605627544914936224640131 141908441317372404336960197)
  ·
    refine ⟨26607832747007325813180037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141908441317372404336960197 26607832747007325813180037)
    ·
      refine ⟨4988968640063873589971257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26607832747007325813180037 4988968640063873589971257)
      ·
        refine ⟨3741726480047905192478443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4988968640063873589971257 3741726480047905192478443)
        ·
          refine ⟨5612589720071857788717665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741726480047905192478443 5612589720071857788717665)
          ·
            refine ⟨4209442290053893341538249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612589720071857788717665 4209442290053893341538249)
            ·
              refine ⟨3157081717540420006153687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209442290053893341538249 3157081717540420006153687)
              ·
                refine ⟨4735622576310630009230531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157081717540420006153687 4735622576310630009230531)
                ·
                  refine ⟨7103433864465945013845797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735622576310630009230531 7103433864465945013845797)
                  ·
                    refine ⟨1331893849587364690096087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103433864465945013845797 1331893849587364690096087)
                    ·
                      rfl

theorem cell22_3890781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3890781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890781 prefixEnd_3890781 := by exact prefixLift 3890781
  have htrace : WordTrace (prefixWord ++ tailWord_3890781) baseStart_3890781 baseEnd_3890781 := by
    simpa [prefixWord, tailWord_3890781, baseEnd_3890781] using wordTrace_append hprefix tailTrace_3890781
  have hstable : (prefixWord ++ tailWord_3890781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890781).length < 2 ^ (prefixWord ++ tailWord_3890781).sum := by decide
  have hdescent : baseEnd_3890781 < baseStart_3890781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890824 : List Nat := [2, 1, 3, 5, 2, 1, 2, 6]
def baseStart_3890824 : Nat := 118140960795 + 3890824 * 2 ^ 59
def prefixEnd_3890824 : Nat := 4983230072969 + 3 ^ 40 * 3890824 * 2
def baseEnd_3890824 : Nat := 147989841040680767918995

theorem tailTrace_3890824 : CollatzResearch.WordTrace tailWord_3890824 prefixEnd_3890824 147989841040680767918995 := by
  unfold tailWord_3890824
  simp only [CollatzResearch.WordTrace]
  refine ⟨70955004828108311340387763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94606673104144415120517017 70955004828108311340387763)
  ·
    refine ⟨106432507242162467010581645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70955004828108311340387763 106432507242162467010581645)
    ·
      refine ⟨39912190215810925128968117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106432507242162467010581645 39912190215810925128968117)
      ·
        refine ⟨3741767832732274230840761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39912190215810925128968117 3741767832732274230840761)
        ·
          refine ⟨2806325874549205673130571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3741767832732274230840761 2806325874549205673130571)
          ·
            refine ⟨4209488811823808509695857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806325874549205673130571 4209488811823808509695857)
            ·
              refine ⟨3157116608867856382271893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209488811823808509695857 3157116608867856382271893)
              ·
                refine ⟨147989841040680767918995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3157116608867856382271893 147989841040680767918995)
                ·
                  rfl

theorem cell22_3890824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_3890824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890824 prefixEnd_3890824 := by exact prefixLift 3890824
  have htrace : WordTrace (prefixWord ++ tailWord_3890824) baseStart_3890824 baseEnd_3890824 := by
    simpa [prefixWord, tailWord_3890824, baseEnd_3890824] using wordTrace_append hprefix tailTrace_3890824
  have hstable : (prefixWord ++ tailWord_3890824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890824).length < 2 ^ (prefixWord ++ tailWord_3890824).sum := by decide
  have hdescent : baseEnd_3890824 < baseStart_3890824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890839 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 1, 3]
def baseStart_3890839 : Nat := 118140960795 + 3890839 * 2 ^ 59
def prefixEnd_3890839 : Nat := 4983230072969 + 3 ^ 40 * 3890839 * 2
def baseEnd_3890839 : Nat := 1331913704172671872145909

theorem tailTrace_3890839 : CollatzResearch.WordTrace tailWord_3890839 prefixEnd_3890839 1331913704172671872145909 := by
  unfold tailWord_3890839
  simp only [CollatzResearch.WordTrace]
  refine ⟨141910556751162280242571571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94607037834108186828381047 141910556751162280242571571)
  ·
    refine ⟨212865835126743420363857357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141910556751162280242571571 212865835126743420363857357)
    ·
      refine ⟨79824688172528782636446509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212865835126743420363857357 79824688172528782636446509)
      ·
        refine ⟨29934258064698293488667441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79824688172528782636446509 29934258064698293488667441)
        ·
          refine ⟨22450693548523720116500581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29934258064698293488667441 22450693548523720116500581)
          ·
            refine ⟨4209505040348197521843859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22450693548523720116500581 4209505040348197521843859)
            ·
              refine ⟨6314257560522296282765789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209505040348197521843859 6314257560522296282765789)
              ·
                refine ⟨2367846585195861106037171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314257560522296282765789 2367846585195861106037171)
                ·
                  refine ⟨3551769877793791659055757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2367846585195861106037171 3551769877793791659055757)
                  ·
                    refine ⟨1331913704172671872145909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3551769877793791659055757 1331913704172671872145909)
                    ·
                      rfl

theorem cell22_3890839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_3890839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890839 prefixEnd_3890839 := by exact prefixLift 3890839
  have htrace : WordTrace (prefixWord ++ tailWord_3890839) baseStart_3890839 baseEnd_3890839 := by
    simpa [prefixWord, tailWord_3890839, baseEnd_3890839] using wordTrace_append hprefix tailTrace_3890839
  have hstable : (prefixWord ++ tailWord_3890839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890839).length < 2 ^ (prefixWord ++ tailWord_3890839).sum := by decide
  have hdescent : baseEnd_3890839 < baseStart_3890839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890869 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 5]
def baseStart_3890869 : Nat := 118140960795 + 3890869 * 2 ^ 59
def prefixEnd_3890869 : Nat := 4983230072969 + 3 ^ 40 * 3890869 * 2
def baseEnd_3890869 : Nat := 443974657928587264631939

theorem tailTrace_3890869 : CollatzResearch.WordTrace tailWord_3890869 prefixEnd_3890869 443974657928587264631939 := by
  unfold tailWord_3890869
  simp only [CollatzResearch.WordTrace]
  refine ⟨141911650941053595366163661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94607767294035730244109107 141911650941053595366163661)
  ·
    refine ⟨53216869102895098262311373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141911650941053595366163661 53216869102895098262311373)
    ·
      refine ⟨19956325913585661848366765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53216869102895098262311373 19956325913585661848366765)
      ·
        refine ⟨7483622217594623193137537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19956325913585661848366765 7483622217594623193137537)
        ·
          refine ⟨5612716663195967394853153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7483622217594623193137537 5612716663195967394853153)
          ·
            refine ⟨4209537497396975546139865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5612716663195967394853153 4209537497396975546139865)
            ·
              refine ⟨3157153123047731659604899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209537497396975546139865 3157153123047731659604899)
              ·
                refine ⟨4735729684571597489407349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157153123047731659604899 4735729684571597489407349)
                ·
                  refine ⟨443974657928587264631939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4735729684571597489407349 443974657928587264631939)
                  ·
                    rfl

theorem cell22_3890869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_3890869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890869 prefixEnd_3890869 := by exact prefixLift 3890869
  have htrace : WordTrace (prefixWord ++ tailWord_3890869) baseStart_3890869 baseEnd_3890869 := by
    simpa [prefixWord, tailWord_3890869, baseEnd_3890869] using wordTrace_append hprefix tailTrace_3890869
  have hstable : (prefixWord ++ tailWord_3890869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890869).length < 2 ^ (prefixWord ++ tailWord_3890869).sum := by decide
  have hdescent : baseEnd_3890869 < baseStart_3890869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890925 : List Nat := [1, 5, 1, 2, 1, 2, 3, 7]
def baseStart_3890925 : Nat := 118140960795 + 3890925 * 2 ^ 59
def prefixEnd_3890925 : Nat := 4983230072969 + 3 ^ 40 * 3890925 * 2
def baseEnd_3890925 : Nat := 147993682636688479388405

theorem tailTrace_3890925 : CollatzResearch.WordTrace tailWord_3890925 prefixEnd_3890925 147993682636688479388405 := by
  unfold tailWord_3890925
  simp only [CollatzResearch.WordTrace]
  refine ⟨141913693428850716930202229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94609128952567144620134819 141913693428850716930202229)
  ·
    refine ⟨13304408758954754712206459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141913693428850716930202229 13304408758954754712206459)
    ·
      refine ⟨19956613138432132068309689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13304408758954754712206459 19956613138432132068309689)
      ·
        refine ⟨14967459853824099051232267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19956613138432132068309689 14967459853824099051232267)
        ·
          refine ⟨22451189780736148576848401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14967459853824099051232267 22451189780736148576848401)
          ·
            refine ⟨16838392335552111432636301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22451189780736148576848401 16838392335552111432636301)
            ·
              refine ⟨6314397125832041787238613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16838392335552111432636301 6314397125832041787238613)
              ·
                refine ⟨147993682636688479388405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6314397125832041787238613 147993682636688479388405)
                ·
                  rfl

theorem cell22_3890925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 7].length) (baseStart_3890925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890925 prefixEnd_3890925 := by exact prefixLift 3890925
  have htrace : WordTrace (prefixWord ++ tailWord_3890925) baseStart_3890925 baseEnd_3890925 := by
    simpa [prefixWord, tailWord_3890925, baseEnd_3890925] using wordTrace_append hprefix tailTrace_3890925
  have hstable : (prefixWord ++ tailWord_3890925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890925).length < 2 ^ (prefixWord ++ tailWord_3890925).sum := by decide
  have hdescent : baseEnd_3890925 < baseStart_3890925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890938 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3890938 : Nat := 118140960795 + 3890938 * 2 ^ 59
def prefixEnd_3890938 : Nat := 4983230072969 + 3 ^ 40 * 3890938 * 2
def baseEnd_3890938 : Nat := 1331947593895868613920605

theorem tailTrace_3890938 : CollatzResearch.WordTrace tailWord_3890938 prefixEnd_3890938 1331947593895868613920605 := by
  unfold tailWord_3890938
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478541894450905037606367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94609445051869080100283645 35478541894450905037606367)
  ·
    refine ⟨53217812841676357556409551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35478541894450905037606367 53217812841676357556409551)
    ·
      refine ⟨79826719262514536334614327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53217812841676357556409551 79826719262514536334614327)
      ·
        refine ⟨119740078893771804501921491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79826719262514536334614327 119740078893771804501921491)
        ·
          refine ⟨179610118340657706752882237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119740078893771804501921491 179610118340657706752882237)
          ·
            refine ⟨67353794377746640032330839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179610118340657706752882237 67353794377746640032330839)
            ·
              refine ⟨101030691566619960048496259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67353794377746640032330839 101030691566619960048496259)
              ·
                refine ⟨151546037349929940072744389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101030691566619960048496259 151546037349929940072744389)
                ·
                  refine ⟨28414882003111863763639573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151546037349929940072744389 28414882003111863763639573)
                  ·
                    refine ⟨1331947593895868613920605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28414882003111863763639573 1331947593895868613920605)
                    ·
                      rfl

theorem cell22_3890938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3890938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890938 prefixEnd_3890938 := by exact prefixLift 3890938
  have htrace : WordTrace (prefixWord ++ tailWord_3890938) baseStart_3890938 baseEnd_3890938 := by
    simpa [prefixWord, tailWord_3890938, baseEnd_3890938] using wordTrace_append hprefix tailTrace_3890938
  have hstable : (prefixWord ++ tailWord_3890938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890938).length < 2 ^ (prefixWord ++ tailWord_3890938).sum := by decide
  have hdescent : baseEnd_3890938 < baseStart_3890938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890950 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3890950 : Nat := 118140960795 + 3890950 * 2 ^ 59
def prefixEnd_3890950 : Nat := 4983230072969 + 3 ^ 40 * 3890950 * 2
def baseEnd_3890950 : Nat := 1331951701741104582620569

theorem tailTrace_3890950 : CollatzResearch.WordTrace tailWord_3890950 prefixEnd_3890950 1331951701741104582620569 := by
  unfold tailWord_3890950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434831414180004568745697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94609736835840097466574869 4434831414180004568745697)
  ·
    refine ⟨3326123560635003426559273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4434831414180004568745697 3326123560635003426559273)
    ·
      refine ⟨2494592670476252569919455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3326123560635003426559273 2494592670476252569919455)
      ·
        refine ⟨3741889005714378854879183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2494592670476252569919455 3741889005714378854879183)
        ·
          refine ⟨5612833508571568282318775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741889005714378854879183 5612833508571568282318775)
          ·
            refine ⟨8419250262857352423478163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612833508571568282318775 8419250262857352423478163)
            ·
              refine ⟨12628875394286028635217245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419250262857352423478163 12628875394286028635217245)
              ·
                refine ⟨4735828272857260738206467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12628875394286028635217245 4735828272857260738206467)
                ·
                  refine ⟨7103742409285891107309701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4735828272857260738206467 7103742409285891107309701)
                  ·
                    refine ⟨1331951701741104582620569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103742409285891107309701 1331951701741104582620569)
                    ·
                      rfl

theorem cell22_3890950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3890950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890950 prefixEnd_3890950 := by exact prefixLift 3890950
  have htrace : WordTrace (prefixWord ++ tailWord_3890950) baseStart_3890950 baseEnd_3890950 := by
    simpa [prefixWord, tailWord_3890950, baseEnd_3890950] using wordTrace_append hprefix tailTrace_3890950
  have hstable : (prefixWord ++ tailWord_3890950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890950).length < 2 ^ (prefixWord ++ tailWord_3890950).sum := by decide
  have hdescent : baseEnd_3890950 < baseStart_3890950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890953 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 7]
def baseStart_3890953 : Nat := 118140960795 + 3890953 * 2 ^ 59
def prefixEnd_3890953 : Nat := 4983230072969 + 3 ^ 40 * 3890953 * 2
def baseEnd_3890953 : Nat := 443984242900804524931853

theorem tailTrace_3890953 : CollatzResearch.WordTrace tailWord_3890953 prefixEnd_3890953 443984242900804524931853 := by
  unfold tailWord_3890953
  simp only [CollatzResearch.WordTrace]
  refine ⟨141914714672749277712221513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94609809781832851808147675 141914714672749277712221513)
  ·
    refine ⟨106436036004561958284166135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141914714672749277712221513 106436036004561958284166135)
    ·
      refine ⟨159654054006842937426249203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106436036004561958284166135 159654054006842937426249203)
      ·
        refine ⟨239481081010264406139373805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159654054006842937426249203 239481081010264406139373805)
        ·
          refine ⟨89805405378849152302265177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239481081010264406139373805 89805405378849152302265177)
          ·
            refine ⟨67354054034136864226698883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89805405378849152302265177 67354054034136864226698883)
            ·
              refine ⟨101031081051205296340048325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67354054034136864226698883 101031081051205296340048325)
              ·
                refine ⟨18943327697100993063759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101031081051205296340048325 18943327697100993063759061)
                ·
                  refine ⟨443984242900804524931853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18943327697100993063759061 443984242900804524931853)
                  ·
                    rfl

theorem cell22_3890953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_3890953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890953 prefixEnd_3890953 := by exact prefixLift 3890953
  have htrace : WordTrace (prefixWord ++ tailWord_3890953) baseStart_3890953 baseEnd_3890953 := by
    simpa [prefixWord, tailWord_3890953, baseEnd_3890953] using wordTrace_append hprefix tailTrace_3890953
  have hstable : (prefixWord ++ tailWord_3890953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890953).length < 2 ^ (prefixWord ++ tailWord_3890953).sum := by decide
  have hdescent : baseEnd_3890953 < baseStart_3890953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3890970 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_3890970 : Nat := 118140960795 + 3890970 * 2 ^ 59
def prefixEnd_3890970 : Nat := 4983230072969 + 3 ^ 40 * 3890970 * 2
def baseEnd_3890970 : Nat := 443986182716610399040169

theorem tailTrace_3890970 : CollatzResearch.WordTrace tailWord_3890970 prefixEnd_3890970 443986182716610399040169 := by
  unfold tailWord_3890970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35478833678421922403897591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94610223142458459743726909 35478833678421922403897591)
  ·
    refine ⟨53218250517632883605846387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35478833678421922403897591 53218250517632883605846387)
    ·
      refine ⟨79827375776449325408769581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53218250517632883605846387 79827375776449325408769581)
      ·
        refine ⟨29935265916168497028288593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79827375776449325408769581 29935265916168497028288593)
        ·
          refine ⟨22451449437126372771216445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29935265916168497028288593 22451449437126372771216445)
          ·
            refine ⟨8419293538922389789206167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22451449437126372771216445 8419293538922389789206167)
            ·
              refine ⟨12628940308383584683809251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8419293538922389789206167 12628940308383584683809251)
              ·
                refine ⟨18943410462575377025713877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12628940308383584683809251 18943410462575377025713877)
                ·
                  refine ⟨443986182716610399040169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18943410462575377025713877 443986182716610399040169)
                  ·
                    rfl

theorem cell22_3890970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_3890970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3890970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3890970 prefixEnd_3890970 := by exact prefixLift 3890970
  have htrace : WordTrace (prefixWord ++ tailWord_3890970) baseStart_3890970 baseEnd_3890970 := by
    simpa [prefixWord, tailWord_3890970, baseEnd_3890970] using wordTrace_append hprefix tailTrace_3890970
  have hstable : (prefixWord ++ tailWord_3890970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3890970).length < 2 ^ (prefixWord ++ tailWord_3890970).sum := by decide
  have hdescent : baseEnd_3890970 < baseStart_3890970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3890970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891045 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3891045 : Nat := 118140960795 + 3891045 * 2 ^ 59
def prefixEnd_3891045 : Nat := 4983230072969 + 3 ^ 40 * 3891045 * 2
def baseEnd_3891045 : Nat := 1331984222182556001495277

theorem tailTrace_3891045 : CollatzResearch.WordTrace tailWord_3891045 prefixEnd_3891045 1331984222182556001495277 := by
  unfold tailWord_3891045
  simp only [CollatzResearch.WordTrace]
  refine ⟨141918070188415977424570589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94612046792277318283047059 141918070188415977424570589)
  ·
    refine ⟨53219276320655991534213971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141918070188415977424570589 53219276320655991534213971)
    ·
      refine ⟨79828914480983987301320957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53219276320655991534213971 79828914480983987301320957)
      ·
        refine ⟨29935842930368995237995359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79828914480983987301320957 29935842930368995237995359)
        ·
          refine ⟨44903764395553492856993039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29935842930368995237995359 44903764395553492856993039)
          ·
            refine ⟨67355646593330239285489559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44903764395553492856993039 67355646593330239285489559)
            ·
              refine ⟨101033469889995358928234339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67355646593330239285489559 101033469889995358928234339)
              ·
                refine ⟨151550204834993038392351509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101033469889995358928234339 151550204834993038392351509)
                ·
                  refine ⟨7103915851640298674641477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 151550204834993038392351509 7103915851640298674641477)
                  ·
                    refine ⟨1331984222182556001495277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7103915851640298674641477 1331984222182556001495277)
                    ·
                      rfl

theorem cell22_3891045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3891045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891045 prefixEnd_3891045 := by exact prefixLift 3891045
  have htrace : WordTrace (prefixWord ++ tailWord_3891045) baseStart_3891045 baseEnd_3891045 := by
    simpa [prefixWord, tailWord_3891045, baseEnd_3891045] using wordTrace_append hprefix tailTrace_3891045
  have hstable : (prefixWord ++ tailWord_3891045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891045).length < 2 ^ (prefixWord ++ tailWord_3891045).sum := by decide
  have hdescent : baseEnd_3891045 < baseStart_3891045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891167 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 6]
def baseStart_3891167 : Nat := 118140960795 + 3891167 * 2 ^ 59
def prefixEnd_3891167 : Nat := 4983230072969 + 3 ^ 40 * 3891167 * 2
def baseEnd_3891167 : Nat := 444008661758596116648301

theorem tailTrace_3891167 : CollatzResearch.WordTrace tailWord_3891167 prefixEnd_3891167 444008661758596116648301 := by
  unfold tailWord_3891167
  simp only [CollatzResearch.WordTrace]
  refine ⟨141922519893973992260511755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94615013262649328173674503 141922519893973992260511755)
  ·
    refine ⟨212883779840960988390767633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141922519893973992260511755 212883779840960988390767633)
    ·
      refine ⟨159662834880720741293075725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212883779840960988390767633 159662834880720741293075725)
      ·
        refine ⟨59873563080270277984903397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159662834880720741293075725 59873563080270277984903397)
        ·
          refine ⟨11226293077550677122169387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59873563080270277984903397 11226293077550677122169387)
          ·
            refine ⟨16839439616326015683254081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11226293077550677122169387 16839439616326015683254081)
            ·
              refine ⟨12629579712244511762440561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16839439616326015683254081 12629579712244511762440561)
              ·
                refine ⟨9472184784183383821830421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12629579712244511762440561 9472184784183383821830421)
                ·
                  refine ⟨444008661758596116648301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9472184784183383821830421 444008661758596116648301)
                  ·
                    rfl

theorem cell22_3891167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_3891167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891167 prefixEnd_3891167 := by exact prefixLift 3891167
  have htrace : WordTrace (prefixWord ++ tailWord_3891167) baseStart_3891167 baseEnd_3891167 := by
    simpa [prefixWord, tailWord_3891167, baseEnd_3891167] using wordTrace_append hprefix tailTrace_3891167
  have hstable : (prefixWord ++ tailWord_3891167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891167).length < 2 ^ (prefixWord ++ tailWord_3891167).sum := by decide
  have hdescent : baseEnd_3891167 < baseStart_3891167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891184 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_3891184 : Nat := 118140960795 + 3891184 * 2 ^ 59
def prefixEnd_3891184 : Nat := 4983230072969 + 3 ^ 40 * 3891184 * 2
def baseEnd_3891184 : Nat := 444010601574401990756617

theorem tailTrace_3891184 : CollatzResearch.WordTrace tailWord_3891184 prefixEnd_3891184 444010601574401990756617 := by
  unfold tailWord_3891184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70961569967456202081940303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94615426623274936109253737 70961569967456202081940303)
  ·
    refine ⟨106442354951184303122910455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70961569967456202081940303 106442354951184303122910455)
    ·
      refine ⟨159663532426776454684365683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106442354951184303122910455 159663532426776454684365683)
      ·
        refine ⟨239495298640164682026548525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159663532426776454684365683 239495298640164682026548525)
        ·
          refine ⟨89810736990061755759955697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239495298640164682026548525 89810736990061755759955697)
          ·
            refine ⟨67358052742546316819966773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89810736990061755759955697 67358052742546316819966773)
            ·
              refine ⟨6314817444613717201871885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67358052742546316819966773 6314817444613717201871885)
              ·
                refine ⟨2368056541730143950701957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6314817444613717201871885 2368056541730143950701957)
                ·
                  refine ⟨444010601574401990756617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368056541730143950701957 444010601574401990756617)
                  ·
                    rfl

theorem cell22_3891184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_3891184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891184 prefixEnd_3891184 := by exact prefixLift 3891184
  have htrace : WordTrace (prefixWord ++ tailWord_3891184) baseStart_3891184 baseEnd_3891184 := by
    simpa [prefixWord, tailWord_3891184, baseEnd_3891184] using wordTrace_append hprefix tailTrace_3891184
  have hstable : (prefixWord ++ tailWord_3891184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891184).length < 2 ^ (prefixWord ++ tailWord_3891184).sum := by decide
  have hdescent : baseEnd_3891184 < baseStart_3891184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891195 : List Nat := [1, 1, 1, 1, 1, 3, 14]
def baseStart_3891195 : Nat := 118140960795 + 3891195 * 2 ^ 59
def prefixEnd_3891195 : Nat := 4983230072969 + 3 ^ 40 * 3891195 * 2
def baseEnd_3891195 : Nat := 49334650749926133712771

theorem tailTrace_3891195 : CollatzResearch.WordTrace tailWord_3891195 prefixEnd_3891195 49334650749926133712771 := by
  unfold tailWord_3891195
  simp only [CollatzResearch.WordTrace]
  refine ⟨141923541137872553042531039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94615694091915035361687359 141923541137872553042531039)
  ·
    refine ⟨212885311706808829563796559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141923541137872553042531039 212885311706808829563796559)
    ·
      refine ⟨319327967560213244345694839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212885311706808829563796559 319327967560213244345694839)
      ·
        refine ⟨478991951340319866518542259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319327967560213244345694839 478991951340319866518542259)
        ·
          refine ⟨718487927010479799777813389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478991951340319866518542259 718487927010479799777813389)
          ·
            refine ⟨269432972628929924916680021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 718487927010479799777813389 269432972628929924916680021)
            ·
              refine ⟨49334650749926133712771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 269432972628929924916680021 49334650749926133712771)
              ·
                rfl

theorem cell22_3891195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 14].length) (baseStart_3891195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891195 prefixEnd_3891195 := by exact prefixLift 3891195
  have htrace : WordTrace (prefixWord ++ tailWord_3891195) baseStart_3891195 baseEnd_3891195 := by
    simpa [prefixWord, tailWord_3891195, baseEnd_3891195] using wordTrace_append hprefix tailTrace_3891195
  have hstable : (prefixWord ++ tailWord_3891195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891195).length < 2 ^ (prefixWord ++ tailWord_3891195).sum := by decide
  have hdescent : baseEnd_3891195 < baseStart_3891195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891197 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3891197 : Nat := 118140960795 + 3891197 * 2 ^ 59
def prefixEnd_3891197 : Nat := 4983230072969 + 3 ^ 40 * 3891197 * 2
def baseEnd_3891197 : Nat := 1332036254888878271694811

theorem tailTrace_3891197 : CollatzResearch.WordTrace tailWord_3891197 prefixEnd_3891197 1332036254888878271694811 := by
  unfold tailWord_3891197
  simp only [CollatzResearch.WordTrace]
  refine ⟨141923614083865307384103845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94615742722576871589402563 141923614083865307384103845)
  ·
    refine ⟨26610677640724745134519471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141923614083865307384103845 26610677640724745134519471)
    ·
      refine ⟨39916016461087117701779207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26610677640724745134519471 39916016461087117701779207)
      ·
        refine ⟨59874024691630676552668811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39916016461087117701779207 59874024691630676552668811)
        ·
          refine ⟨89811037037446014829003217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59874024691630676552668811 89811037037446014829003217)
          ·
            refine ⟨67358277778084511121752413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89811037037446014829003217 67358277778084511121752413)
            ·
              refine ⟨25259354166781691670657155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67358277778084511121752413 25259354166781691670657155)
              ·
                refine ⟨37889031250172537505985733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25259354166781691670657155 37889031250172537505985733)
                ·
                  refine ⟨7104193359407350782372325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37889031250172537505985733 7104193359407350782372325)
                  ·
                    refine ⟨1332036254888878271694811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104193359407350782372325 1332036254888878271694811)
                    ·
                      rfl

theorem cell22_3891197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3891197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891197 prefixEnd_3891197 := by exact prefixLift 3891197
  have htrace : WordTrace (prefixWord ++ tailWord_3891197) baseStart_3891197 baseEnd_3891197 := by
    simpa [prefixWord, tailWord_3891197, baseEnd_3891197] using wordTrace_append hprefix tailTrace_3891197
  have hstable : (prefixWord ++ tailWord_3891197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891197).length < 2 ^ (prefixWord ++ tailWord_3891197).sum := by decide
  have hdescent : baseEnd_3891197 < baseStart_3891197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891201 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 4]
def baseStart_3891201 : Nat := 118140960795 + 3891201 * 2 ^ 59
def prefixEnd_3891201 : Nat := 4983230072969 + 3 ^ 40 * 3891201 * 2
def baseEnd_3891201 : Nat := 444012541390207864864933

theorem tailTrace_3891201 : CollatzResearch.WordTrace tailWord_3891201 prefixEnd_3891201 444012541390207864864933 := by
  unfold tailWord_3891201
  simp only [CollatzResearch.WordTrace]
  refine ⟨141923759975850816067249457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94615839983900544044832971 141923759975850816067249457)
  ·
    refine ⟨106442819981888112050437093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141923759975850816067249457 106442819981888112050437093)
    ·
      refine ⟨19958028746604021009456955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106442819981888112050437093 19958028746604021009456955)
      ·
        refine ⟨29937043119906031514185433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19958028746604021009456955 29937043119906031514185433)
        ·
          refine ⟨22452782339929523635639075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29937043119906031514185433 22452782339929523635639075)
          ·
            refine ⟨33679173509894285453458613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22452782339929523635639075 33679173509894285453458613)
            ·
              refine ⟨3157422516552589261261745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33679173509894285453458613 3157422516552589261261745)
              ·
                refine ⟨2368066887414441945946309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157422516552589261261745 2368066887414441945946309)
                ·
                  refine ⟨444012541390207864864933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368066887414441945946309 444012541390207864864933)
                  ·
                    rfl

theorem cell22_3891201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 4].length) (baseStart_3891201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891201 prefixEnd_3891201 := by exact prefixLift 3891201
  have htrace : WordTrace (prefixWord ++ tailWord_3891201) baseStart_3891201 baseEnd_3891201 := by
    simpa [prefixWord, tailWord_3891201, baseEnd_3891201] using wordTrace_append hprefix tailTrace_3891201
  have hstable : (prefixWord ++ tailWord_3891201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891201).length < 2 ^ (prefixWord ++ tailWord_3891201).sum := by decide
  have hdescent : baseEnd_3891201 < baseStart_3891201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891212 : List Nat := [2, 2, 1, 2, 3, 1, 4, 7]
def baseStart_3891212 : Nat := 118140960795 + 3891212 * 2 ^ 59
def prefixEnd_3891212 : Nat := 4983230072969 + 3 ^ 40 * 3891212 * 2
def baseEnd_3891212 : Nat := 148004598855047025841085

theorem tailTrace_3891212 : CollatzResearch.WordTrace tailWord_3891212 prefixEnd_3891212 148004598855047025841085 := by
  unfold tailWord_3891212
  simp only [CollatzResearch.WordTrace]
  refine ⟨70962080589405482472949945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94616107452540643297266593 70962080589405482472949945)
  ·
    refine ⟨53221560442054111854712459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70962080589405482472949945 53221560442054111854712459)
    ·
      refine ⟨79832340663081167782068689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53221560442054111854712459 79832340663081167782068689)
      ·
        refine ⟨59874255497310875836551517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79832340663081167782068689 59874255497310875836551517)
        ·
          refine ⟨22452845811491578438706819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59874255497310875836551517 22452845811491578438706819)
          ·
            refine ⟨33679268717237367658060229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22452845811491578438706819 33679268717237367658060229)
            ·
              refine ⟨6314862884482006435886293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33679268717237367658060229 6314862884482006435886293)
              ·
                refine ⟨148004598855047025841085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6314862884482006435886293 148004598855047025841085)
                ·
                  rfl

theorem cell22_3891212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_3891212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891212 prefixEnd_3891212 := by exact prefixLift 3891212
  have htrace : WordTrace (prefixWord ++ tailWord_3891212) baseStart_3891212 baseEnd_3891212 := by
    simpa [prefixWord, tailWord_3891212, baseEnd_3891212] using wordTrace_append hprefix tailTrace_3891212
  have hstable : (prefixWord ++ tailWord_3891212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891212).length < 2 ^ (prefixWord ++ tailWord_3891212).sum := by decide
  have hdescent : baseEnd_3891212 < baseStart_3891212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891220 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3891220 : Nat := 118140960795 + 3891220 * 2 ^ 59
def prefixEnd_3891220 : Nat := 4983230072969 + 3 ^ 40 * 3891220 * 2
def baseEnd_3891220 : Nat := 1332044128258913878369741

theorem tailTrace_3891220 : CollatzResearch.WordTrace tailWord_3891220 prefixEnd_3891220 1332044128258913878369741 := by
  unfold tailWord_3891220
  simp only [CollatzResearch.WordTrace]
  refine ⟨70962226481390991156095557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94616301975187988208127409 70962226481390991156095557)
  ·
    refine ⟨13305417465260810841767917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70962226481390991156095557 13305417465260810841767917)
    ·
      refine ⟨4989531549472804065662969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13305417465260810841767917 4989531549472804065662969)
      ·
        refine ⟨3742148662104603049247227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4989531549472804065662969 3742148662104603049247227)
        ·
          refine ⟨5613222993156904573870841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742148662104603049247227 5613222993156904573870841)
          ·
            refine ⟨4209917244867678430403131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5613222993156904573870841 4209917244867678430403131)
            ·
              refine ⟨6314875867301517645604697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4209917244867678430403131 6314875867301517645604697)
              ·
                refine ⟨4736156900476138234203523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6314875867301517645604697 4736156900476138234203523)
                ·
                  refine ⟨7104235350714207351305285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736156900476138234203523 7104235350714207351305285)
                  ·
                    refine ⟨1332044128258913878369741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104235350714207351305285 1332044128258913878369741)
                    ·
                      rfl

theorem cell22_3891220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3891220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891220 prefixEnd_3891220 := by exact prefixLift 3891220
  have htrace : WordTrace (prefixWord ++ tailWord_3891220) baseStart_3891220 baseEnd_3891220 := by
    simpa [prefixWord, tailWord_3891220, baseEnd_3891220] using wordTrace_append hprefix tailTrace_3891220
  have hstable : (prefixWord ++ tailWord_3891220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891220).length < 2 ^ (prefixWord ++ tailWord_3891220).sum := by decide
  have hdescent : baseEnd_3891220 < baseStart_3891220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891252 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3891252 : Nat := 118140960795 + 3891252 * 2 ^ 59
def prefixEnd_3891252 : Nat := 4983230072969 + 3 ^ 40 * 3891252 * 2
def baseEnd_3891252 : Nat := 444018360837625487189881

theorem tailTrace_3891252 : CollatzResearch.WordTrace tailWord_3891252 prefixEnd_3891252 444018360837625487189881 := by
  unfold tailWord_3891252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70962810049333025888678005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94617080065777367851570673 70962810049333025888678005)
  ·
    refine ⟨6652763442124971177063563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70962810049333025888678005 6652763442124971177063563)
    ·
      refine ⟨9979145163187456765595345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6652763442124971177063563 9979145163187456765595345)
      ·
        refine ⟨7484358872390592574196509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9979145163187456765595345 7484358872390592574196509)
        ·
          refine ⟨2806634577146472215323691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7484358872390592574196509 2806634577146472215323691)
          ·
            refine ⟨4209951865719708322985537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806634577146472215323691 4209951865719708322985537)
            ·
              refine ⟨3157463899289781242239153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4209951865719708322985537 3157463899289781242239153)
              ·
                refine ⟨2368097924467335931679365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3157463899289781242239153 2368097924467335931679365)
                ·
                  refine ⟨444018360837625487189881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368097924467335931679365 444018360837625487189881)
                  ·
                    rfl

theorem cell22_3891252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3891252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891252 prefixEnd_3891252 := by exact prefixLift 3891252
  have htrace : WordTrace (prefixWord ++ tailWord_3891252) baseStart_3891252 baseEnd_3891252 := by
    simpa [prefixWord, tailWord_3891252, baseEnd_3891252] using wordTrace_append hprefix tailTrace_3891252
  have hstable : (prefixWord ++ tailWord_3891252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891252).length < 2 ^ (prefixWord ++ tailWord_3891252).sum := by decide
  have hdescent : baseEnd_3891252 < baseStart_3891252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891319 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 6]
def baseStart_3891319 : Nat := 118140960795 + 3891319 * 2 ^ 59
def prefixEnd_3891319 : Nat := 4983230072969 + 3 ^ 40 * 3891319 * 2
def baseEnd_3891319 : Nat := 444026005994036873381479

theorem tailTrace_3891319 : CollatzResearch.WordTrace tailWord_3891319 prefixEnd_3891319 444026005994036873381479 := by
  unfold tailWord_3891319
  simp only [CollatzResearch.WordTrace]
  refine ⟨141928063789423322220045011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94618709192948881480030007 141928063789423322220045011)
  ·
    refine ⟨212892095684134983330067517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141928063789423322220045011 212892095684134983330067517)
    ·
      refine ⟨79834535881550618748775319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212892095684134983330067517 79834535881550618748775319)
      ·
        refine ⟨119751803822325928123162979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79834535881550618748775319 119751803822325928123162979)
        ·
          refine ⟨179627705733488892184744469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119751803822325928123162979 179627705733488892184744469)
          ·
            refine ⟨8420048706257291821159897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 179627705733488892184744469 8420048706257291821159897)
            ·
              refine ⟨6315036529692968865869923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8420048706257291821159897 6315036529692968865869923)
              ·
                refine ⟨9472554794539453298804885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315036529692968865869923 9472554794539453298804885)
                ·
                  refine ⟨444026005994036873381479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9472554794539453298804885 444026005994036873381479)
                  ·
                    rfl

theorem cell22_3891319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 6].length) (baseStart_3891319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891319 prefixEnd_3891319 := by exact prefixLift 3891319
  have htrace : WordTrace (prefixWord ++ tailWord_3891319) baseStart_3891319 baseEnd_3891319 := by
    simpa [prefixWord, tailWord_3891319, baseEnd_3891319] using wordTrace_append hprefix tailTrace_3891319
  have hstable : (prefixWord ++ tailWord_3891319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891319).length < 2 ^ (prefixWord ++ tailWord_3891319).sum := by decide
  have hdescent : baseEnd_3891319 < baseStart_3891319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891349 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3891349 : Nat := 118140960795 + 3891349 * 2 ^ 59
def prefixEnd_3891349 : Nat := 4983230072969 + 3 ^ 40 * 3891349 * 2
def baseEnd_3891349 : Nat := 1332088287595200541894345

theorem tailTrace_3891349 : CollatzResearch.WordTrace tailWord_3891349 prefixEnd_3891349 1332088287595200541894345 := by
  unfold tailWord_3891349
  simp only [CollatzResearch.WordTrace]
  refine ⟨141929157979314637343637101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94619438652876424895758067 141929157979314637343637101)
  ·
    refine ⟨53223434242242989003863913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141929157979314637343637101 53223434242242989003863913)
    ·
      refine ⟨39917575681682241752897935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53223434242242989003863913 39917575681682241752897935)
      ·
        refine ⟨59876363522523362629346903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39917575681682241752897935 59876363522523362629346903)
        ·
          refine ⟨89814545283785043944020355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59876363522523362629346903 89814545283785043944020355)
          ·
            refine ⟨134721817925677565916030533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89814545283785043944020355 134721817925677565916030533)
            ·
              refine ⟨25260340861064543609255725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134721817925677565916030533 25260340861064543609255725)
              ·
                refine ⟨9472627822899203853470897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25260340861064543609255725 9472627822899203853470897)
                ·
                  refine ⟨7104470867174402890103173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9472627822899203853470897 7104470867174402890103173)
                  ·
                    refine ⟨1332088287595200541894345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104470867174402890103173 1332088287595200541894345)
                    ·
                      rfl

theorem cell22_3891349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3891349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891349 prefixEnd_3891349 := by exact prefixLift 3891349
  have htrace : WordTrace (prefixWord ++ tailWord_3891349) baseStart_3891349 baseEnd_3891349 := by
    simpa [prefixWord, tailWord_3891349, baseEnd_3891349] using wordTrace_append hprefix tailTrace_3891349
  have hstable : (prefixWord ++ tailWord_3891349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891349).length < 2 ^ (prefixWord ++ tailWord_3891349).sum := by decide
  have hdescent : baseEnd_3891349 < baseStart_3891349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891370 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_3891370 : Nat := 118140960795 + 3891370 * 2 ^ 59
def prefixEnd_3891370 : Nat := 4983230072969 + 3 ^ 40 * 3891370 * 2
def baseEnd_3891370 : Nat := 444031825441454495706427

theorem tailTrace_3891370 : CollatzResearch.WordTrace tailWord_3891370 prefixEnd_3891370 444031825441454495706427 := by
  unfold tailWord_3891370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35482480978059639482537891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94619949274825705286767709 35482480978059639482537891)
  ·
    refine ⟨53223721467089459223806837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35482480978059639482537891 53223721467089459223806837)
    ·
      refine ⟨4989723887539636802231891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53223721467089459223806837 4989723887539636802231891)
      ·
        refine ⟨7484585831309455203347837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4989723887539636802231891 7484585831309455203347837)
        ·
          refine ⟨2806719686741045701255439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7484585831309455203347837 2806719686741045701255439)
          ·
            refine ⟨4210079530111568551883159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2806719686741045701255439 4210079530111568551883159)
            ·
              refine ⟨6315119295167352827824739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210079530111568551883159 6315119295167352827824739)
              ·
                refine ⟨9472678942751029241737109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315119295167352827824739 9472678942751029241737109)
                ·
                  refine ⟨444031825441454495706427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9472678942751029241737109 444031825441454495706427)
                  ·
                    rfl

theorem cell22_3891370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_3891370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891370 prefixEnd_3891370 := by exact prefixLift 3891370
  have htrace : WordTrace (prefixWord ++ tailWord_3891370) baseStart_3891370 baseEnd_3891370 := by
    simpa [prefixWord, tailWord_3891370, baseEnd_3891370] using wordTrace_append hprefix tailTrace_3891370
  have hstable : (prefixWord ++ tailWord_3891370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891370).length < 2 ^ (prefixWord ++ tailWord_3891370).sum := by decide
  have hdescent : baseEnd_3891370 < baseStart_3891370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891424 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_3891424 : Nat := 118140960795 + 3891424 * 2 ^ 59
def prefixEnd_3891424 : Nat := 4983230072969 + 3 ^ 40 * 3891424 * 2
def baseEnd_3891424 : Nat := 1332113961627925346269115

theorem tailTrace_3891424 : CollatzResearch.WordTrace tailWord_3891424 prefixEnd_3891424 1332113961627925346269115 := by
  unfold tailWord_3891424
  simp only [CollatzResearch.WordTrace]
  refine ⟨70965946727021462576308663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94621262302695283435078217 70965946727021462576308663)
  ·
    refine ⟨106448920090532193864462995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70965946727021462576308663 106448920090532193864462995)
    ·
      refine ⟨159673380135798290796694493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106448920090532193864462995 159673380135798290796694493)
      ·
        refine ⟨59877517550924359048760435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159673380135798290796694493 59877517550924359048760435)
        ·
          refine ⟨89816276326386538573140653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59877517550924359048760435 89816276326386538573140653)
          ·
            refine ⟨33681103622394951964927745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89816276326386538573140653 33681103622394951964927745)
            ·
              refine ⟨25260827716796213973695809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33681103622394951964927745 25260827716796213973695809)
              ·
                refine ⟨18945620787597160480271857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25260827716796213973695809 18945620787597160480271857)
                ·
                  refine ⟨14209215590697870360203893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18945620787597160480271857 14209215590697870360203893)
                  ·
                    refine ⟨1332113961627925346269115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14209215590697870360203893 1332113961627925346269115)
                    ·
                      rfl

theorem cell22_3891424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_3891424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891424 prefixEnd_3891424 := by exact prefixLift 3891424
  have htrace : WordTrace (prefixWord ++ tailWord_3891424) baseStart_3891424 baseEnd_3891424 := by
    simpa [prefixWord, tailWord_3891424, baseEnd_3891424] using wordTrace_append hprefix tailTrace_3891424
  have hstable : (prefixWord ++ tailWord_3891424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891424).length < 2 ^ (prefixWord ++ tailWord_3891424).sum := by decide
  have hdescent : baseEnd_3891424 < baseStart_3891424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891473 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_3891473 : Nat := 118140960795 + 3891473 * 2 ^ 59
def prefixEnd_3891473 : Nat := 4983230072969 + 3 ^ 40 * 3891473 * 2
def baseEnd_3891473 : Nat := 1332130735329305551793965

theorem tailTrace_3891473 : CollatzResearch.WordTrace tailWord_3891473 prefixEnd_3891473 1332130735329305551793965 := by
  unfold tailWord_3891473
  simp only [CollatzResearch.WordTrace]
  refine ⟨141933680630865406521151073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94622453753910271014100715 141933680630865406521151073)
  ·
    refine ⟨106450260473149054890863305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141933680630865406521151073 106450260473149054890863305)
    ·
      refine ⟨79837695354861791168147479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106450260473149054890863305 79837695354861791168147479)
      ·
        refine ⟨119756543032292686752221219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79837695354861791168147479 119756543032292686752221219)
        ·
          refine ⟨179634814548439030128331829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119756543032292686752221219 179634814548439030128331829)
          ·
            refine ⟨16840763863916159074531109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 179634814548439030128331829 16840763863916159074531109)
            ·
              refine ⟨3157643224484279826474583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16840763863916159074531109 3157643224484279826474583)
              ·
                refine ⟨4736464836726419739711875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3157643224484279826474583 4736464836726419739711875)
                ·
                  refine ⟨7104697255089629609567813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736464836726419739711875 7104697255089629609567813)
                  ·
                    refine ⟨1332130735329305551793965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104697255089629609567813 1332130735329305551793965)
                    ·
                      rfl

theorem cell22_3891473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_3891473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891473 prefixEnd_3891473 := by exact prefixLift 3891473
  have htrace : WordTrace (prefixWord ++ tailWord_3891473) baseStart_3891473 baseEnd_3891473 := by
    simpa [prefixWord, tailWord_3891473, baseEnd_3891473] using wordTrace_append hprefix tailTrace_3891473
  have hstable : (prefixWord ++ tailWord_3891473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891473).length < 2 ^ (prefixWord ++ tailWord_3891473).sum := by decide
  have hdescent : baseEnd_3891473 < baseStart_3891473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891488 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_3891488 : Nat := 118140960795 + 3891488 * 2 ^ 59
def prefixEnd_3891488 : Nat := 4983230072969 + 3 ^ 40 * 3891488 * 2
def baseEnd_3891488 : Nat := 444045290045283504222973

theorem tailTrace_3891488 : CollatzResearch.WordTrace tailWord_3891488 prefixEnd_3891488 444045290045283504222973 := by
  unfold tailWord_3891488
  simp only [CollatzResearch.WordTrace]
  refine ⟨70967113862905532041473559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94622818483874042721964745 70967113862905532041473559)
  ·
    refine ⟨106450670794358298062210339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70967113862905532041473559 106450670794358298062210339)
    ·
      refine ⟨159676006191537447093315509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106450670794358298062210339 159676006191537447093315509)
      ·
        refine ⟨14969625580456635664998329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159676006191537447093315509 14969625580456635664998329)
        ·
          refine ⟨11227219185342476748748747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14969625580456635664998329 11227219185342476748748747)
          ·
            refine ⟨16840828778013715123123121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227219185342476748748747 16840828778013715123123121)
            ·
              refine ⟨12630621583510286342342341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16840828778013715123123121 12630621583510286342342341)
              ·
                refine ⟨2368241546908178689189189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12630621583510286342342341 2368241546908178689189189)
                ·
                  refine ⟨444045290045283504222973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368241546908178689189189 444045290045283504222973)
                  ·
                    rfl

theorem cell22_3891488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_3891488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891488 prefixEnd_3891488 := by exact prefixLift 3891488
  have htrace : WordTrace (prefixWord ++ tailWord_3891488) baseStart_3891488 baseEnd_3891488 := by
    simpa [prefixWord, tailWord_3891488, baseEnd_3891488] using wordTrace_append hprefix tailTrace_3891488
  have hstable : (prefixWord ++ tailWord_3891488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891488).length < 2 ^ (prefixWord ++ tailWord_3891488).sum := by decide
  have hdescent : baseEnd_3891488 < baseStart_3891488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891529 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_3891529 : Nat := 118140960795 + 3891529 * 2 ^ 59
def prefixEnd_3891529 : Nat := 4983230072969 + 3 ^ 40 * 3891529 * 2
def baseEnd_3891529 : Nat := 1332149905273740072393793

theorem tailTrace_3891529 : CollatzResearch.WordTrace tailWord_3891529 prefixEnd_3891529 1332149905273740072393793 := by
  unfold tailWord_3891529
  simp only [CollatzResearch.WordTrace]
  refine ⟨141935723118662528085189641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94623815412441685390126427 141935723118662528085189641)
  ·
    refine ⟨106451792338996896063892231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141935723118662528085189641 106451792338996896063892231)
    ·
      refine ⟨159677688508495344095838347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106451792338996896063892231 159677688508495344095838347)
      ·
        refine ⟨239516532762743016143757521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159677688508495344095838347 239516532762743016143757521)
        ·
          refine ⟨179637399572057262107818141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239516532762743016143757521 179637399572057262107818141)
          ·
            refine ⟨67364024839521473290431803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179637399572057262107818141 67364024839521473290431803)
            ·
              refine ⟨101046037259282209935647705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67364024839521473290431803 101046037259282209935647705)
              ·
                refine ⟨75784527944461657451735779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101046037259282209935647705 75784527944461657451735779)
                ·
                  refine ⟨113676791916692486177603669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75784527944461657451735779 113676791916692486177603669)
                  ·
                    refine ⟨1332149905273740072393793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113676791916692486177603669 1332149905273740072393793)
                    ·
                      rfl

theorem cell22_3891529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_3891529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891529 prefixEnd_3891529 := by exact prefixLift 3891529
  have htrace : WordTrace (prefixWord ++ tailWord_3891529) baseStart_3891529 baseEnd_3891529 := by
    simpa [prefixWord, tailWord_3891529, baseEnd_3891529] using wordTrace_append hprefix tailTrace_3891529
  have hstable : (prefixWord ++ tailWord_3891529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891529).length < 2 ^ (prefixWord ++ tailWord_3891529).sum := by decide
  have hdescent : baseEnd_3891529 < baseStart_3891529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891561 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 5]
def baseStart_3891561 : Nat := 118140960795 + 3891561 * 2 ^ 59
def prefixEnd_3891561 : Nat := 4983230072969 + 3 ^ 40 * 3891561 * 2
def baseEnd_3891561 : Nat := 444053619842567551864565

theorem tailTrace_3891561 : CollatzResearch.WordTrace tailWord_3891561 prefixEnd_3891561 444053619842567551864565 := by
  unfold tailWord_3891561
  simp only [CollatzResearch.WordTrace]
  refine ⟨141936890254546597550354537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94624593503031065033569691 141936890254546597550354537)
  ·
    refine ⟨106452667690909948162765903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141936890254546597550354537 106452667690909948162765903)
    ·
      refine ⟨159679001536364922244148855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106452667690909948162765903 159679001536364922244148855)
      ·
        refine ⟨239518502304547383366223283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159679001536364922244148855 239518502304547383366223283)
        ·
          refine ⟨359277753456821075049334925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239518502304547383366223283 359277753456821075049334925)
          ·
            refine ⟨134729157546307903143500597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359277753456821075049334925 134729157546307903143500597)
            ·
              refine ⟨12630858519966365919703181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134729157546307903143500597 12630858519966365919703181)
              ·
                refine ⟨4736571944987387219888693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12630858519966365919703181 4736571944987387219888693)
                ·
                  refine ⟨444053619842567551864565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4736571944987387219888693 444053619842567551864565)
                  ·
                    rfl

theorem cell22_3891561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_3891561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891561 prefixEnd_3891561 := by exact prefixLift 3891561
  have htrace : WordTrace (prefixWord ++ tailWord_3891561) baseStart_3891561 baseEnd_3891561 := by
    simpa [prefixWord, tailWord_3891561, baseEnd_3891561] using wordTrace_append hprefix tailTrace_3891561
  have hstable : (prefixWord ++ tailWord_3891561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891561).length < 2 ^ (prefixWord ++ tailWord_3891561).sum := by decide
  have hdescent : baseEnd_3891561 < baseStart_3891561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891608 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_3891608 : Nat := 118140960795 + 3891608 * 2 ^ 59
def prefixEnd_3891608 : Nat := 4983230072969 + 3 ^ 40 * 3891608 * 2
def baseEnd_3891608 : Nat := 1332176948588210199668551

theorem tailTrace_3891608 : CollatzResearch.WordTrace tailWord_3891608 prefixEnd_3891608 1332176948588210199668551 := by
  unfold tailWord_3891608
  simp only [CollatzResearch.WordTrace]
  refine ⟨70969302242688162288657739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94625736323584216384876985 70969302242688162288657739)
  ·
    refine ⟨106453953364032243432986609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70969302242688162288657739 106453953364032243432986609)
    ·
      refine ⟨79840465023024182574739957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106453953364032243432986609 79840465023024182574739957)
      ·
        refine ⟨7485043595908517116381871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79840465023024182574739957 7485043595908517116381871)
        ·
          refine ⟨11227565393862775674572807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485043595908517116381871 11227565393862775674572807)
          ·
            refine ⟨16841348090794163511859211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227565393862775674572807 16841348090794163511859211)
            ·
              refine ⟨25262022136191245267788817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16841348090794163511859211 25262022136191245267788817)
              ·
                refine ⟨18946516602143433950841613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25262022136191245267788817 18946516602143433950841613)
                ·
                  refine ⟨7104943725803787731565605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18946516602143433950841613 7104943725803787731565605)
                  ·
                    refine ⟨1332176948588210199668551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7104943725803787731565605 1332176948588210199668551)
                    ·
                      rfl

theorem cell22_3891608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_3891608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891608 prefixEnd_3891608 := by exact prefixLift 3891608
  have htrace : WordTrace (prefixWord ++ tailWord_3891608) baseStart_3891608 baseEnd_3891608 := by
    simpa [prefixWord, tailWord_3891608, baseEnd_3891608] using wordTrace_append hprefix tailTrace_3891608
  have hstable : (prefixWord ++ tailWord_3891608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891608).length < 2 ^ (prefixWord ++ tailWord_3891608).sum := by decide
  have hdescent : baseEnd_3891608 < baseStart_3891608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891623 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 6]
def baseStart_3891623 : Nat := 118140960795 + 3891623 * 2 ^ 59
def prefixEnd_3891623 : Nat := 4983230072969 + 3 ^ 40 * 3891623 * 2
def baseEnd_3891623 : Nat := 444060694464918386847835

theorem tailTrace_3891623 : CollatzResearch.WordTrace tailWord_3891623 prefixEnd_3891623 444060694464918386847835 := by
  unfold tailWord_3891623
  simp only [CollatzResearch.WordTrace]
  refine ⟨141939151580321982139111523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94626101053547988092741015 141939151580321982139111523)
  ·
    refine ⟨212908727370482973208667285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141939151580321982139111523 212908727370482973208667285)
    ·
      refine ⟨9980096595491389369156279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 212908727370482973208667285 9980096595491389369156279)
      ·
        refine ⟨14970144893237084053734419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9980096595491389369156279 14970144893237084053734419)
        ·
          refine ⟨22455217339855626080601629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14970144893237084053734419 22455217339855626080601629)
          ·
            refine ⟨8420706502445859780225611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22455217339855626080601629 8420706502445859780225611)
            ·
              refine ⟨12631059753668789670338417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8420706502445859780225611 12631059753668789670338417)
              ·
                refine ⟨9473294815251592252753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12631059753668789670338417 9473294815251592252753813)
                ·
                  refine ⟨444060694464918386847835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9473294815251592252753813 444060694464918386847835)
                  ·
                    rfl

theorem cell22_3891623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_3891623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891623 prefixEnd_3891623 := by exact prefixLift 3891623
  have htrace : WordTrace (prefixWord ++ tailWord_3891623) baseStart_3891623 baseEnd_3891623 := by
    simpa [prefixWord, tailWord_3891623, baseEnd_3891623] using wordTrace_append hprefix tailTrace_3891623
  have hstable : (prefixWord ++ tailWord_3891623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891623).length < 2 ^ (prefixWord ++ tailWord_3891623).sum := by decide
  have hdescent : baseEnd_3891623 < baseStart_3891623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891655 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3891655 : Nat := 118140960795 + 3891655 * 2 ^ 59
def prefixEnd_3891655 : Nat := 4983230072969 + 3 ^ 40 * 3891655 * 2
def baseEnd_3891655 : Nat := 1332193037648717743743407

theorem tailTrace_3891655 : CollatzResearch.WordTrace tailWord_3891655 prefixEnd_3891655 1332193037648717743743407 := by
  unfold tailWord_3891655
  simp only [CollatzResearch.WordTrace]
  refine ⟨141940318716206051604276419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94626879144137367736184279 141940318716206051604276419)
  ·
    refine ⟨212910478074309077406414629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141940318716206051604276419 212910478074309077406414629)
    ·
      refine ⟨39920714638932952013702743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212910478074309077406414629 39920714638932952013702743)
      ·
        refine ⟨59881071958399428020554115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39920714638932952013702743 59881071958399428020554115)
        ·
          refine ⟨89821607937599142030831173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59881071958399428020554115 89821607937599142030831173)
          ·
            refine ⟨16841551488299839130780845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89821607937599142030831173 16841551488299839130780845)
            ·
              refine ⟨6315581808112439674042817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16841551488299839130780845 6315581808112439674042817)
              ·
                refine ⟨4736686356084329755532113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315581808112439674042817 4736686356084329755532113)
                ·
                  refine ⟨3552514767063247316649085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4736686356084329755532113 3552514767063247316649085)
                  ·
                    refine ⟨1332193037648717743743407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3552514767063247316649085 1332193037648717743743407)
                    ·
                      rfl

theorem cell22_3891655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3891655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891655 prefixEnd_3891655 := by exact prefixLift 3891655
  have htrace : WordTrace (prefixWord ++ tailWord_3891655) baseStart_3891655 baseEnd_3891655 := by
    simpa [prefixWord, tailWord_3891655, baseEnd_3891655] using wordTrace_append hprefix tailTrace_3891655
  have hstable : (prefixWord ++ tailWord_3891655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891655).length < 2 ^ (prefixWord ++ tailWord_3891655).sum := by decide
  have hdescent : baseEnd_3891655 < baseStart_3891655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891696 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_3891696 : Nat := 118140960795 + 3891696 * 2 ^ 59
def prefixEnd_3891696 : Nat := 4983230072969 + 3 ^ 40 * 3891696 * 2
def baseEnd_3891696 : Nat := 444069024262202434489427

theorem tailTrace_3891696 : CollatzResearch.WordTrace tailWord_3891696 prefixEnd_3891696 444069024262202434489427 := by
  unfold tailWord_3891696
  simp only [CollatzResearch.WordTrace]
  refine ⟨70970907054528757803259471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94627876072705010404345961 70970907054528757803259471)
  ·
    refine ⟨106456360581793136704889207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70970907054528757803259471 106456360581793136704889207)
    ·
      refine ⟨159684540872689705057333811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106456360581793136704889207 159684540872689705057333811)
      ·
        refine ⟨239526811309034557586000717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159684540872689705057333811 239526811309034557586000717)
        ·
          refine ⟨89822554240887959094750269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239526811309034557586000717 89822554240887959094750269)
          ·
            refine ⟨33683457840332984660531351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89822554240887959094750269 33683457840332984660531351)
            ·
              refine ⟨50525186760499476990797027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33683457840332984660531351 50525186760499476990797027)
              ·
                refine ⟨75787780140749215486195541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50525186760499476990797027 75787780140749215486195541)
                ·
                  refine ⟨444069024262202434489427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75787780140749215486195541 444069024262202434489427)
                  ·
                    rfl

theorem cell22_3891696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_3891696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891696 prefixEnd_3891696 := by exact prefixLift 3891696
  have htrace : WordTrace (prefixWord ++ tailWord_3891696) baseStart_3891696 baseEnd_3891696 := by
    simpa [prefixWord, tailWord_3891696, baseEnd_3891696] using wordTrace_append hprefix tailTrace_3891696
  have hstable : (prefixWord ++ tailWord_3891696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891696).length < 2 ^ (prefixWord ++ tailWord_3891696).sum := by decide
  have hdescent : baseEnd_3891696 < baseStart_3891696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891713 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 7]
def baseStart_3891713 : Nat := 118140960795 + 3891713 * 2 ^ 59
def prefixEnd_3891713 : Nat := 4983230072969 + 3 ^ 40 * 3891713 * 2
def baseEnd_3891713 : Nat := 444070964078008308597743

theorem tailTrace_3891713 : CollatzResearch.WordTrace tailWord_3891713 prefixEnd_3891713 444070964078008308597743 := by
  unfold tailWord_3891713
  simp only [CollatzResearch.WordTrace]
  refine ⟨141942434149995927509887793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94628289433330618339925195 141942434149995927509887793)
  ·
    refine ⟨106456825612496945632415845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141942434149995927509887793 106456825612496945632415845)
    ·
      refine ⟨19960654802343177306077971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106456825612496945632415845 19960654802343177306077971)
      ·
        refine ⟨29940982203514765959116957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19960654802343177306077971 29940982203514765959116957)
        ·
          refine ⟨11227868326318037234668859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29940982203514765959116957 11227868326318037234668859)
          ·
            refine ⟨16841802489477055852003289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11227868326318037234668859 16841802489477055852003289)
            ·
              refine ⟨12631351867107791889002467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16841802489477055852003289 12631351867107791889002467)
              ·
                refine ⟨18947027800661687833503701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12631351867107791889002467 18947027800661687833503701)
                ·
                  refine ⟨444070964078008308597743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18947027800661687833503701 444070964078008308597743)
                  ·
                    rfl

theorem cell22_3891713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_3891713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891713 prefixEnd_3891713 := by exact prefixLift 3891713
  have htrace : WordTrace (prefixWord ++ tailWord_3891713) baseStart_3891713 baseEnd_3891713 := by
    simpa [prefixWord, tailWord_3891713, baseEnd_3891713] using wordTrace_append hprefix tailTrace_3891713
  have hstable : (prefixWord ++ tailWord_3891713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891713).length < 2 ^ (prefixWord ++ tailWord_3891713).sum := by decide
  have hdescent : baseEnd_3891713 < baseStart_3891713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891764 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3891764 : Nat := 118140960795 + 3891764 * 2 ^ 59
def prefixEnd_3891764 : Nat := 4983230072969 + 3 ^ 40 * 3891764 * 2
def baseEnd_3891764 : Nat := 444076783525425930922691

theorem tailTrace_3891764 : CollatzResearch.WordTrace tailWord_3891764 prefixEnd_3891764 444076783525425930922691 := by
  unfold tailWord_3891764
  simp only [CollatzResearch.WordTrace]
  refine ⟨70972147136405581609997173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94629529515207442146662897 70972147136405581609997173)
  ·
    refine ⟨6653638794038023275937235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70972147136405581609997173 6653638794038023275937235)
    ·
      refine ⟨9980458191057034913905853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6653638794038023275937235 9980458191057034913905853)
      ·
        refine ⟨3742671821646388092714695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9980458191057034913905853 3742671821646388092714695)
        ·
          refine ⟨5614007732469582139072043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3742671821646388092714695 5614007732469582139072043)
          ·
            refine ⟨8421011598704373208608065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614007732469582139072043 8421011598704373208608065)
            ·
              refine ⟨6315758699028279906456049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8421011598704373208608065 6315758699028279906456049)
              ·
                refine ⟨4736819024271209929842037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315758699028279906456049 4736819024271209929842037)
                ·
                  refine ⟨444076783525425930922691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4736819024271209929842037 444076783525425930922691)
                  ·
                    rfl

theorem cell22_3891764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3891764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891764 prefixEnd_3891764 := by exact prefixLift 3891764
  have htrace : WordTrace (prefixWord ++ tailWord_3891764) baseStart_3891764 baseEnd_3891764 := by
    simpa [prefixWord, tailWord_3891764, baseEnd_3891764] using wordTrace_append hprefix tailTrace_3891764
  have hstable : (prefixWord ++ tailWord_3891764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891764).length < 2 ^ (prefixWord ++ tailWord_3891764).sum := by decide
  have hdescent : baseEnd_3891764 < baseStart_3891764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891775 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 4]
def baseStart_3891775 : Nat := 118140960795 + 3891775 * 2 ^ 59
def prefixEnd_3891775 : Nat := 4983230072969 + 3 ^ 40 * 3891775 * 2
def baseEnd_3891775 : Nat := 444078038700359143581013

theorem tailTrace_3891775 : CollatzResearch.WordTrace tailWord_3891775 prefixEnd_3891775 444078038700359143581013 := by
  unfold tailWord_3891775
  simp only [CollatzResearch.WordTrace]
  refine ⟨141944695475771312098644779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94629796983847541399096519 141944695475771312098644779)
  ·
    refine ⟨212917043213656968147967169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141944695475771312098644779 212917043213656968147967169)
    ·
      refine ⟨159687782410242726110975377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212917043213656968147967169 159687782410242726110975377)
      ·
        refine ⟨119765836807682044583231533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159687782410242726110975377 119765836807682044583231533)
        ·
          refine ⟨44912188802880766718711825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119765836807682044583231533 44912188802880766718711825)
          ·
            refine ⟨33684141602160575039033869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44912188802880766718711825 33684141602160575039033869)
            ·
              refine ⟨12631553100810215639637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33684141602160575039033869 12631553100810215639637701)
              ·
                refine ⟨2368416206401915432432069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12631553100810215639637701 2368416206401915432432069)
                ·
                  refine ⟨444078038700359143581013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368416206401915432432069 444078038700359143581013)
                  ·
                    rfl

theorem cell22_3891775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 4].length) (baseStart_3891775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891775 prefixEnd_3891775 := by exact prefixLift 3891775
  have htrace : WordTrace (prefixWord ++ tailWord_3891775) baseStart_3891775 baseEnd_3891775 := by
    simpa [prefixWord, tailWord_3891775, baseEnd_3891775] using wordTrace_append hprefix tailTrace_3891775
  have hstable : (prefixWord ++ tailWord_3891775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891775).length < 2 ^ (prefixWord ++ tailWord_3891775).sum := by decide
  have hdescent : baseEnd_3891775 < baseStart_3891775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891788 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_3891788 : Nat := 118140960795 + 3891788 * 2 ^ 59
def prefixEnd_3891788 : Nat := 4983230072969 + 3 ^ 40 * 3891788 * 2
def baseEnd_3891788 : Nat := 1332238566266749730167999

theorem tailTrace_3891788 : CollatzResearch.WordTrace tailWord_3891788 prefixEnd_3891788 1332238566266749730167999 := by
  unfold tailWord_3891788
  simp only [CollatzResearch.WordTrace]
  refine ⟨70972584812362107659434009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94630113083149476879245345 70972584812362107659434009)
  ·
    refine ⟨53229438609271580744575507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70972584812362107659434009 53229438609271580744575507)
    ·
      refine ⟨79844157913907371116863261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53229438609271580744575507 79844157913907371116863261)
      ·
        refine ⟨29941559217715264168823723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79844157913907371116863261 29941559217715264168823723)
        ·
          refine ⟨44912338826572896253235585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29941559217715264168823723 44912338826572896253235585)
          ·
            refine ⟨33684254119929672189926689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44912338826572896253235585 33684254119929672189926689)
            ·
              refine ⟨25263190589947254142445017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33684254119929672189926689 25263190589947254142445017)
              ·
                refine ⟨18947392942460440606833763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25263190589947254142445017 18947392942460440606833763)
                ·
                  refine ⟨28421089413690660910250645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18947392942460440606833763 28421089413690660910250645)
                  ·
                    refine ⟨1332238566266749730167999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28421089413690660910250645 1332238566266749730167999)
                    ·
                      rfl

theorem cell22_3891788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_3891788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891788 prefixEnd_3891788 := by exact prefixLift 3891788
  have htrace : WordTrace (prefixWord ++ tailWord_3891788) baseStart_3891788 baseEnd_3891788 := by
    simpa [prefixWord, tailWord_3891788, baseEnd_3891788] using wordTrace_append hprefix tailTrace_3891788
  have hstable : (prefixWord ++ tailWord_3891788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891788).length < 2 ^ (prefixWord ++ tailWord_3891788).sum := by decide
  have hdescent : baseEnd_3891788 < baseStart_3891788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891824 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_3891824 : Nat := 118140960795 + 3891824 * 2 ^ 59
def prefixEnd_3891824 : Nat := 4983230072969 + 3 ^ 40 * 3891824 * 2
def baseEnd_3891824 : Nat := 1332250889802457636267889

theorem tailTrace_3891824 : CollatzResearch.WordTrace tailWord_3891824 prefixEnd_3891824 1332250889802457636267889 := by
  unfold tailWord_3891824
  simp only [CollatzResearch.WordTrace]
  refine ⟨70973241326296896733589263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94630988435062528978119017 70973241326296896733589263)
  ·
    refine ⟨106459861989445345100383895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70973241326296896733589263 106459861989445345100383895)
    ·
      refine ⟨159689792984168017650575843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106459861989445345100383895 159689792984168017650575843)
      ·
        refine ⟨239534689476252026475863765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159689792984168017650575843 239534689476252026475863765)
        ·
          refine ⟨5614094284599656870528057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 239534689476252026475863765 5614094284599656870528057)
          ·
            refine ⟨4210570713449742652896043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5614094284599656870528057 4210570713449742652896043)
            ·
              refine ⟨6315856070174613979344065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210570713449742652896043 6315856070174613979344065)
              ·
                refine ⟨4736892052630960484508049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315856070174613979344065 4736892052630960484508049)
                ·
                  refine ⟨3552669039473220363381037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4736892052630960484508049 3552669039473220363381037)
                  ·
                    refine ⟨1332250889802457636267889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3552669039473220363381037 1332250889802457636267889)
                    ·
                      rfl

theorem cell22_3891824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_3891824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891824 prefixEnd_3891824 := by exact prefixLift 3891824
  have htrace : WordTrace (prefixWord ++ tailWord_3891824) baseStart_3891824 baseEnd_3891824 := by
    simpa [prefixWord, tailWord_3891824, baseEnd_3891824] using wordTrace_append hprefix tailTrace_3891824
  have hstable : (prefixWord ++ tailWord_3891824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891824).length < 2 ^ (prefixWord ++ tailWord_3891824).sum := by decide
  have hdescent : baseEnd_3891824 < baseStart_3891824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891869 : List Nat := [1, 4, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3891869 : Nat := 118140960795 + 3891869 * 2 ^ 59
def prefixEnd_3891869 : Nat := 4983230072969 + 3 ^ 40 * 3891869 * 2
def baseEnd_3891869 : Nat := 1332266294222092518892751

theorem tailTrace_3891869 : CollatzResearch.WordTrace tailWord_3891869 prefixEnd_3891869 1332266294222092518892751 := by
  unfold tailWord_3891869
  simp only [CollatzResearch.WordTrace]
  refine ⟨141948123937430766152566661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94632082624953844101711107 141948123937430766152566661)
  ·
    refine ⟨26615273238268268653606249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141948123937430766152566661 26615273238268268653606249)
    ·
      refine ⟨19961454928701201490204687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26615273238268268653606249 19961454928701201490204687)
      ·
        refine ⟨29942182393051802235307031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19961454928701201490204687 29942182393051802235307031)
        ·
          refine ⟨44913273589577703352960547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29942182393051802235307031 44913273589577703352960547)
          ·
            refine ⟨67369910384366555029440821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44913273589577703352960547 67369910384366555029440821)
            ·
              refine ⟨6315929098534364534010077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67369910384366555029440821 6315929098534364534010077)
              ·
                refine ⟨2368473411950386700253779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6315929098534364534010077 2368473411950386700253779)
                ·
                  refine ⟨3552710117925580050380669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368473411950386700253779 3552710117925580050380669)
                  ·
                    refine ⟨1332266294222092518892751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3552710117925580050380669 1332266294222092518892751)
                    ·
                      rfl

theorem cell22_3891869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3891869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891869 prefixEnd_3891869 := by exact prefixLift 3891869
  have htrace : WordTrace (prefixWord ++ tailWord_3891869) baseStart_3891869 baseEnd_3891869 := by
    simpa [prefixWord, tailWord_3891869, baseEnd_3891869] using wordTrace_append hprefix tailTrace_3891869
  have hstable : (prefixWord ++ tailWord_3891869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891869).length < 2 ^ (prefixWord ++ tailWord_3891869).sum := by decide
  have hdescent : baseEnd_3891869 < baseStart_3891869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891886 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3891886 : Nat := 118140960795 + 3891886 * 2 ^ 59
def prefixEnd_3891886 : Nat := 4983230072969 + 3 ^ 40 * 3891886 * 2
def baseEnd_3891886 : Nat := 1332272113669510141217699

theorem tailTrace_3891886 : CollatzResearch.WordTrace tailWord_3891886 prefixEnd_3891886 1332272113669510141217699 := by
  unfold tailWord_3891886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17743592997296147256991939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94632495985579452037290341 17743592997296147256991939)
  ·
    refine ⟨26615389495944220885487909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17743592997296147256991939 26615389495944220885487909)
    ·
      refine ⟨4990385530489541416028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26615389495944220885487909 4990385530489541416028983)
      ·
        refine ⟨7485578295734312124043475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990385530489541416028983 7485578295734312124043475)
        ·
          refine ⟨11228367443601468186065213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7485578295734312124043475 11228367443601468186065213)
          ·
            refine ⟨4210637791350550569774455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11228367443601468186065213 4210637791350550569774455)
            ·
              refine ⟨6315956687025825854661683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4210637791350550569774455 6315956687025825854661683)
              ·
                refine ⟨9473935030538738781992525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6315956687025825854661683 9473935030538738781992525)
                ·
                  refine ⟨3552725636452027043247197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9473935030538738781992525 3552725636452027043247197)
                  ·
                    refine ⟨1332272113669510141217699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3552725636452027043247197 1332272113669510141217699)
                    ·
                      rfl

theorem cell22_3891886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3891886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891886 prefixEnd_3891886 := by exact prefixLift 3891886
  have htrace : WordTrace (prefixWord ++ tailWord_3891886) baseStart_3891886 baseEnd_3891886 := by
    simpa [prefixWord, tailWord_3891886, baseEnd_3891886] using wordTrace_append hprefix tailTrace_3891886
  have hstable : (prefixWord ++ tailWord_3891886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891886).length < 2 ^ (prefixWord ++ tailWord_3891886).sum := by decide
  have hdescent : baseEnd_3891886 < baseStart_3891886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891912 : List Nat := [2, 1, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_3891912 : Nat := 118140960795 + 3891912 * 2 ^ 59
def prefixEnd_3891912 : Nat := 4983230072969 + 3 ^ 40 * 3891912 * 2
def baseEnd_3891912 : Nat := 1332281014000854740067619

theorem tailTrace_3891912 : CollatzResearch.WordTrace tailWord_3891912 prefixEnd_3891912 1332281014000854740067619 := by
  unfold tailWord_3891912
  simp only [CollatzResearch.WordTrace]
  refine ⟨70974846138137492248190995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94633128184183322997587993 70974846138137492248190995)
  ·
    refine ⟨106462269207206238372286493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70974846138137492248190995 106462269207206238372286493)
    ·
      refine ⟨39923350952702339389607435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106462269207206238372286493 39923350952702339389607435)
      ·
        refine ⟨59885026429053509084411153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39923350952702339389607435 59885026429053509084411153)
        ·
          refine ⟨44913769821790131813308365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59885026429053509084411153 44913769821790131813308365)
          ·
            refine ⟨16842663683171299429990637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44913769821790131813308365 16842663683171299429990637)
            ·
              refine ⟨6315998881189237286246489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16842663683171299429990637 6315998881189237286246489)
              ·
                refine ⟨4736999160891927964684867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6315998881189237286246489 4736999160891927964684867)
                ·
                  refine ⟨7105498741337891947027301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4736999160891927964684867 7105498741337891947027301)
                  ·
                    refine ⟨1332281014000854740067619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7105498741337891947027301 1332281014000854740067619)
                    ·
                      rfl

theorem cell22_3891912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_3891912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891912 prefixEnd_3891912 := by exact prefixLift 3891912
  have htrace : WordTrace (prefixWord ++ tailWord_3891912) baseStart_3891912 baseEnd_3891912 := by
    simpa [prefixWord, tailWord_3891912, baseEnd_3891912] using wordTrace_append hprefix tailTrace_3891912
  have hstable : (prefixWord ++ tailWord_3891912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891912).length < 2 ^ (prefixWord ++ tailWord_3891912).sum := by decide
  have hdescent : baseEnd_3891912 < baseStart_3891912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891944 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_3891944 : Nat := 118140960795 + 3891944 * 2 ^ 59
def prefixEnd_3891944 : Nat := 4983230072969 + 3 ^ 40 * 3891944 * 2
def baseEnd_3891944 : Nat := 444097322751605774422507

theorem tailTrace_3891944 : CollatzResearch.WordTrace tailWord_3891944 prefixEnd_3891944 444097322751605774422507 := by
  unfold tailWord_3891944
  simp only [CollatzResearch.WordTrace]
  refine ⟨70975429706079526980773443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94633906274772702641031257 70975429706079526980773443)
  ·
    refine ⟨106463144559119290471160165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70975429706079526980773443 106463144559119290471160165)
    ·
      refine ⟨19961839604834866963342531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106463144559119290471160165 19961839604834866963342531)
      ·
        refine ⟨29942759407252300445013797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19961839604834866963342531 29942759407252300445013797)
        ·
          refine ⟨5614267388859806333440087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29942759407252300445013797 5614267388859806333440087)
          ·
            refine ⟨8421401083289709500160131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614267388859806333440087 8421401083289709500160131)
            ·
              refine ⟨12632101624934564250240197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8421401083289709500160131 12632101624934564250240197)
              ·
                refine ⟨2368519054675230796920037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12632101624934564250240197 2368519054675230796920037)
                ·
                  refine ⟨444097322751605774422507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2368519054675230796920037 444097322751605774422507)
                  ·
                    rfl

theorem cell22_3891944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_3891944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891944 prefixEnd_3891944 := by exact prefixLift 3891944
  have htrace : WordTrace (prefixWord ++ tailWord_3891944) baseStart_3891944 baseEnd_3891944 := by
    simpa [prefixWord, tailWord_3891944, baseEnd_3891944] using wordTrace_append hprefix tailTrace_3891944
  have hstable : (prefixWord ++ tailWord_3891944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891944).length < 2 ^ (prefixWord ++ tailWord_3891944).sum := by decide
  have hdescent : baseEnd_3891944 < baseStart_3891944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3891972 : List Nat := [2, 3, 2, 2, 1, 1, 5, 6]
def baseStart_3891972 : Nat := 118140960795 + 3891972 * 2 ^ 59
def prefixEnd_3891972 : Nat := 4983230072969 + 3 ^ 40 * 3891972 * 2
def baseEnd_3891972 : Nat := 148033505914114953729715

theorem tailTrace_3891972 : CollatzResearch.WordTrace tailWord_3891972 prefixEnd_3891972 148033505914114953729715 := by
  unfold tailWord_3891972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70975940328028807371783085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94634587104038409829044113 70975940328028807371783085)
  ·
    refine ⟨26615977623010802764418657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70975940328028807371783085 26615977623010802764418657)
    ·
      refine ⟨19961983217258102073313993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26615977623010802764418657 19961983217258102073313993)
      ·
        refine ⟨14971487412943576554985495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19961983217258102073313993 14971487412943576554985495)
        ·
          refine ⟨22457231119415364832478243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971487412943576554985495 22457231119415364832478243)
          ·
            refine ⟨33685846679123047248717365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22457231119415364832478243 33685846679123047248717365)
            ·
              refine ⟨3158048126167785679567253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33685846679123047248717365 3158048126167785679567253)
              ·
                refine ⟨148033505914114953729715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3158048126167785679567253 148033505914114953729715)
                ·
                  rfl

theorem cell22_3891972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 6].length) (baseStart_3891972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3891972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3891972 prefixEnd_3891972 := by exact prefixLift 3891972
  have htrace : WordTrace (prefixWord ++ tailWord_3891972) baseStart_3891972 baseEnd_3891972 := by
    simpa [prefixWord, tailWord_3891972, baseEnd_3891972] using wordTrace_append hprefix tailTrace_3891972
  have hstable : (prefixWord ++ tailWord_3891972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3891972).length < 2 ^ (prefixWord ++ tailWord_3891972).sum := by decide
  have hdescent : baseEnd_3891972 < baseStart_3891972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3891972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892075 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_3892075 : Nat := 118140960795 + 3892075 * 2 ^ 59
def prefixEnd_3892075 : Nat := 4983230072969 + 3 ^ 40 * 3892075 * 2
def baseEnd_3892075 : Nat := 1332336812231976648242119

theorem tailTrace_3892075 : CollatzResearch.WordTrace tailWord_3892075 prefixEnd_3892075 1332336812231976648242119 := by
  unfold tailWord_3892075
  simp only [CollatzResearch.WordTrace]
  refine ⟨141955637374684463334565679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94637091583122975556377119 141955637374684463334565679)
  ·
    refine ⟨212933456062026695001848519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141955637374684463334565679 212933456062026695001848519)
    ·
      refine ⟨319400184093040042502772779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212933456062026695001848519 319400184093040042502772779)
      ·
        refine ⟨479100276139560063754159169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319400184093040042502772779 479100276139560063754159169)
        ·
          refine ⟨359325207104670047815619377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479100276139560063754159169 359325207104670047815619377)
          ·
            refine ⟨269493905328502535861714533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359325207104670047815619377 269493905328502535861714533)
            ·
              refine ⟨50530107249094225474071475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 269493905328502535861714533 50530107249094225474071475)
              ·
                refine ⟨75795160873641338211107213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50530107249094225474071475 75795160873641338211107213)
                ·
                  refine ⟨28423185327615501829165205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75795160873641338211107213 28423185327615501829165205)
                  ·
                    refine ⟨1332336812231976648242119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28423185327615501829165205 1332336812231976648242119)
                    ·
                      rfl

theorem cell22_3892075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_3892075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892075 prefixEnd_3892075 := by exact prefixLift 3892075
  have htrace : WordTrace (prefixWord ++ tailWord_3892075) baseStart_3892075 baseEnd_3892075 := by
    simpa [prefixWord, tailWord_3892075, baseEnd_3892075] using wordTrace_append hprefix tailTrace_3892075
  have hstable : (prefixWord ++ tailWord_3892075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892075).length < 2 ^ (prefixWord ++ tailWord_3892075).sum := by decide
  have hdescent : baseEnd_3892075 < baseStart_3892075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892077 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3892077 : Nat := 118140960795 + 3892077 * 2 ^ 59
def prefixEnd_3892077 : Nat := 4983230072969 + 3 ^ 40 * 3892077 * 2
def baseEnd_3892077 : Nat := 1332337496872849309692113

theorem tailTrace_3892077 : CollatzResearch.WordTrace tailWord_3892077 prefixEnd_3892077 1332337496872849309692113 := by
  unfold tailWord_3892077
  simp only [CollatzResearch.WordTrace]
  refine ⟨141955710320677217676138485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94637140213784811784092323 141955710320677217676138485)
  ·
    refine ⟨13308347842563489157137983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141955710320677217676138485 13308347842563489157137983)
    ·
      refine ⟨19962521763845233735706975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13308347842563489157137983 19962521763845233735706975)
      ·
        refine ⟨29943782645767850603560463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19962521763845233735706975 29943782645767850603560463)
        ·
          refine ⟨44915673968651775905340695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29943782645767850603560463 44915673968651775905340695)
          ·
            refine ⟨67373510952977663858011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44915673968651775905340695 67373510952977663858011043)
            ·
              refine ⟨101060266429466495787016565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67373510952977663858011043 101060266429466495787016565)
              ·
                refine ⟨9474399977762483980032803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101060266429466495787016565 9474399977762483980032803)
                ·
                  refine ⟨14211599966643725970049205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9474399977762483980032803 14211599966643725970049205)
                  ·
                    refine ⟨1332337496872849309692113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14211599966643725970049205 1332337496872849309692113)
                    ·
                      rfl

theorem cell22_3892077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3892077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892077 prefixEnd_3892077 := by exact prefixLift 3892077
  have htrace : WordTrace (prefixWord ++ tailWord_3892077) baseStart_3892077 baseEnd_3892077 := by
    simpa [prefixWord, tailWord_3892077, baseEnd_3892077] using wordTrace_append hprefix tailTrace_3892077
  have hstable : (prefixWord ++ tailWord_3892077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892077).length < 2 ^ (prefixWord ++ tailWord_3892077).sum := by decide
  have hdescent : baseEnd_3892077 < baseStart_3892077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892167 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_3892167 : Nat := 118140960795 + 3892167 * 2 ^ 59
def prefixEnd_3892167 : Nat := 4983230072969 + 3 ^ 40 * 3892167 * 2
def baseEnd_3892167 : Nat := 1332368305712119074941837

theorem tailTrace_3892167 : CollatzResearch.WordTrace tailWord_3892167 prefixEnd_3892167 1332368305712119074941837 := by
  unfold tailWord_3892167
  simp only [CollatzResearch.WordTrace]
  refine ⟨141958992890351163046914755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94639328593567442031276503 141958992890351163046914755)
  ·
    refine ⟨212938489335526744570372133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141958992890351163046914755 212938489335526744570372133)
    ·
      refine ⟨39925966750411264606944775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212938489335526744570372133 39925966750411264606944775)
      ·
        refine ⟨59888950125616896910417163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39925966750411264606944775 59888950125616896910417163)
        ·
          refine ⟨89833425188425345365625745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59888950125616896910417163 89833425188425345365625745)
          ·
            refine ⟨67375068891319009024219309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89833425188425345365625745 67375068891319009024219309)
            ·
              refine ⟨25265650834244628384082241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67375068891319009024219309 25265650834244628384082241)
              ·
                refine ⟨18949238125683471288061681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25265650834244628384082241 18949238125683471288061681)
                ·
                  refine ⟨14211928594262603466046261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18949238125683471288061681 14211928594262603466046261)
                  ·
                    refine ⟨1332368305712119074941837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14211928594262603466046261 1332368305712119074941837)
                    ·
                      rfl

theorem cell22_3892167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_3892167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892167 prefixEnd_3892167 := by exact prefixLift 3892167
  have htrace : WordTrace (prefixWord ++ tailWord_3892167) baseStart_3892167 baseEnd_3892167 := by
    simpa [prefixWord, tailWord_3892167, baseEnd_3892167] using wordTrace_append hprefix tailTrace_3892167
  have hstable : (prefixWord ++ tailWord_3892167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892167).length < 2 ^ (prefixWord ++ tailWord_3892167).sum := by decide
  have hdescent : baseEnd_3892167 < baseStart_3892167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892186 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_3892186 : Nat := 118140960795 + 3892186 * 2 ^ 59
def prefixEnd_3892186 : Nat := 4983230072969 + 3 ^ 40 * 3892186 * 2
def baseEnd_3892186 : Nat := 444124936600136452905593

theorem tailTrace_3892186 : CollatzResearch.WordTrace tailWord_3892186 prefixEnd_3892186 444124936600136452905593 := by
  unfold tailWord_3892186
  simp only [CollatzResearch.WordTrace]
  refine ⟨35489921469320582322964103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94639790584854886194570941 35489921469320582322964103)
  ·
    refine ⟨53234882203980873484446155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35489921469320582322964103 53234882203980873484446155)
    ·
      refine ⟨79852323305971310226669233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53234882203980873484446155 79852323305971310226669233)
      ·
        refine ⟨59889242479478482670001925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79852323305971310226669233 59889242479478482670001925)
        ·
          refine ⟨11229232964902215500625361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59889242479478482670001925 11229232964902215500625361)
          ·
            refine ⟨8421924723676661625469021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11229232964902215500625361 8421924723676661625469021)
            ·
              refine ⟨3158221771378748109550883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8421924723676661625469021 3158221771378748109550883)
              ·
                refine ⟨4737332657068122164326325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158221771378748109550883 4737332657068122164326325)
                ·
                  refine ⟨444124936600136452905593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4737332657068122164326325 444124936600136452905593)
                  ·
                    rfl

theorem cell22_3892186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_3892186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892186 prefixEnd_3892186 := by exact prefixLift 3892186
  have htrace : WordTrace (prefixWord ++ tailWord_3892186) baseStart_3892186 baseEnd_3892186 := by
    simpa [prefixWord, tailWord_3892186, baseEnd_3892186] using wordTrace_append hprefix tailTrace_3892186
  have hstable : (prefixWord ++ tailWord_3892186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892186).length < 2 ^ (prefixWord ++ tailWord_3892186).sum := by decide
  have hdescent : baseEnd_3892186 < baseStart_3892186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892229 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_3892229 : Nat := 118140960795 + 3892229 * 2 ^ 59
def prefixEnd_3892229 : Nat := 4983230072969 + 3 ^ 40 * 3892229 * 2
def baseEnd_3892229 : Nat := 1332389529579171579891647

theorem tailTrace_3892229 : CollatzResearch.WordTrace tailWord_3892229 prefixEnd_3892229 1332389529579171579891647 := by
  unfold tailWord_3892229
  simp only [CollatzResearch.WordTrace]
  refine ⟨141961254216126547635671741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94640836144084365090447827 141961254216126547635671741)
  ·
    refine ⟨53235470331047455363376903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141961254216126547635671741 53235470331047455363376903)
    ·
      refine ⟨79853205496571183045065355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53235470331047455363376903 79853205496571183045065355)
      ·
        refine ⟨119779808244856774567598033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79853205496571183045065355 119779808244856774567598033)
        ·
          refine ⟨89834856183642580925698525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119779808244856774567598033 89834856183642580925698525)
          ·
            refine ⟨33688071068865967847136947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89834856183642580925698525 33688071068865967847136947)
            ·
              refine ⟨50532106603298951770705421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33688071068865967847136947 50532106603298951770705421)
              ·
                refine ⟨18949539976237106914014533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50532106603298951770705421 18949539976237106914014533)
                ·
                  refine ⟨3553038745544457546377725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18949539976237106914014533 3553038745544457546377725)
                  ·
                    refine ⟨1332389529579171579891647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553038745544457546377725 1332389529579171579891647)
                    ·
                      rfl

theorem cell22_3892229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_3892229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892229 prefixEnd_3892229 := by exact prefixLift 3892229
  have htrace : WordTrace (prefixWord ++ tailWord_3892229) baseStart_3892229 baseEnd_3892229 := by
    simpa [prefixWord, tailWord_3892229, baseEnd_3892229] using wordTrace_append hprefix tailTrace_3892229
  have hstable : (prefixWord ++ tailWord_3892229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892229).length < 2 ^ (prefixWord ++ tailWord_3892229).sum := by decide
  have hdescent : baseEnd_3892229 < baseStart_3892229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892310 : List Nat := [5, 2, 2, 1, 2, 1, 3, 6]
def baseStart_3892310 : Nat := 118140960795 + 3892310 * 2 ^ 59
def prefixEnd_3892310 : Nat := 4983230072969 + 3 ^ 40 * 3892310 * 2
def baseEnd_3892310 : Nat := 148046361948279374290711

theorem tailTrace_3892310 : CollatzResearch.WordTrace tailWord_3892310 prefixEnd_3892310 148046361948279374290711 := by
  unfold tailWord_3892310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872763033052068654335649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94642805685888732312913589 8872763033052068654335649)
  ·
    refine ⟨6654572274789051490751737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8872763033052068654335649 6654572274789051490751737)
    ·
      refine ⟨4990929206091788618063803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6654572274789051490751737 4990929206091788618063803)
      ·
        refine ⟨7486393809137682927095705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4990929206091788618063803 7486393809137682927095705)
        ·
          refine ⟨5614795356853262195321779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7486393809137682927095705 5614795356853262195321779)
          ·
            refine ⟨8422193035279893292982669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5614795356853262195321779 8422193035279893292982669)
            ·
              refine ⟨3158322388229959984868501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8422193035279893292982669 3158322388229959984868501)
              ·
                refine ⟨148046361948279374290711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3158322388229959984868501 148046361948279374290711)
                ·
                  rfl

theorem cell22_3892310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_3892310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892310 prefixEnd_3892310 := by exact prefixLift 3892310
  have htrace : WordTrace (prefixWord ++ tailWord_3892310) baseStart_3892310 baseEnd_3892310 := by
    simpa [prefixWord, tailWord_3892310, baseEnd_3892310] using wordTrace_append hprefix tailTrace_3892310
  have hstable : (prefixWord ++ tailWord_3892310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892310).length < 2 ^ (prefixWord ++ tailWord_3892310).sum := by decide
  have hdescent : baseEnd_3892310 < baseStart_3892310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892366 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3892366 : Nat := 118140960795 + 3892366 * 2 ^ 59
def prefixEnd_3892366 : Nat := 4983230072969 + 3 ^ 40 * 3892366 * 2
def baseEnd_3892366 : Nat := 444145475826316296405409

theorem tailTrace_3892366 : CollatzResearch.WordTrace tailWord_3892366 prefixEnd_3892366 444145475826316296405409 := by
  unfold tailWord_3892366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17745781377078777504176119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94644167344420146688939301 17745781377078777504176119)
  ·
    refine ⟨26618672065618166256264179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17745781377078777504176119 26618672065618166256264179)
    ·
      refine ⟨39928008098427249384396269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26618672065618166256264179 39928008098427249384396269)
      ·
        refine ⟨14973003036910218519148601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39928008098427249384396269 14973003036910218519148601)
        ·
          refine ⟨11229752277682663889361451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14973003036910218519148601 11229752277682663889361451)
          ·
            refine ⟨16844628416523995834042177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11229752277682663889361451 16844628416523995834042177)
            ·
              refine ⟨12633471312392996875531633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16844628416523995834042177 12633471312392996875531633)
              ·
                refine ⟨9475103484294747656648725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12633471312392996875531633 9475103484294747656648725)
                ·
                  refine ⟨444145475826316296405409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9475103484294747656648725 444145475826316296405409)
                  ·
                    rfl

theorem cell22_3892366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3892366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892366 prefixEnd_3892366 := by exact prefixLift 3892366
  have htrace : WordTrace (prefixWord ++ tailWord_3892366) baseStart_3892366 baseEnd_3892366 := by
    simpa [prefixWord, tailWord_3892366, baseEnd_3892366] using wordTrace_append hprefix tailTrace_3892366
  have hstable : (prefixWord ++ tailWord_3892366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892366).length < 2 ^ (prefixWord ++ tailWord_3892366).sum := by decide
  have hdescent : baseEnd_3892366 < baseStart_3892366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892381 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3892381 : Nat := 118140960795 + 3892381 * 2 ^ 59
def prefixEnd_3892381 : Nat := 4983230072969 + 3 ^ 40 * 3892381 * 2
def baseEnd_3892381 : Nat := 1332441562285493850091181

theorem tailTrace_3892381 : CollatzResearch.WordTrace tailWord_3892381 prefixEnd_3892381 1332441562285493850091181 := by
  unfold tailWord_3892381
  simp only [CollatzResearch.WordTrace]
  refine ⟨141966798111575877595204997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94644532074383918396803331 141966798111575877595204997)
  ·
    refine ⟨26618774645920477049100937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141966798111575877595204997 26618774645920477049100937)
    ·
      refine ⟨19964080984440357786825703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26618774645920477049100937 19964080984440357786825703)
      ·
        refine ⟨29946121476660536680238555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19964080984440357786825703 29946121476660536680238555)
        ·
          refine ⟨44919182214990805020357833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29946121476660536680238555 44919182214990805020357833)
          ·
            refine ⟨33689386661243103765268375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44919182214990805020357833 33689386661243103765268375)
            ·
              refine ⟨50534079991864655647902563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33689386661243103765268375 50534079991864655647902563)
              ·
                refine ⟨75801119987796983471853845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50534079991864655647902563 75801119987796983471853845)
                ·
                  refine ⟨3553177499427983600243149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75801119987796983471853845 3553177499427983600243149)
                  ·
                    refine ⟨1332441562285493850091181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553177499427983600243149 1332441562285493850091181)
                    ·
                      rfl

theorem cell22_3892381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3892381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892381 prefixEnd_3892381 := by exact prefixLift 3892381
  have htrace : WordTrace (prefixWord ++ tailWord_3892381) baseStart_3892381 baseEnd_3892381 := by
    simpa [prefixWord, tailWord_3892381, baseEnd_3892381] using wordTrace_append hprefix tailTrace_3892381
  have hstable : (prefixWord ++ tailWord_3892381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892381).length < 2 ^ (prefixWord ++ tailWord_3892381).sum := by decide
  have hdescent : baseEnd_3892381 < baseStart_3892381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892439 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 9]
def baseStart_3892439 : Nat := 118140960795 + 3892439 * 2 ^ 59
def prefixEnd_3892439 : Nat := 4983230072969 + 3 ^ 40 * 3892439 * 2
def baseEnd_3892439 : Nat := 444153805623600344047001

theorem tailTrace_3892439 : CollatzResearch.WordTrace tailWord_3892439 prefixEnd_3892439 444153805623600344047001 := by
  unfold tailWord_3892439
  simp only [CollatzResearch.WordTrace]
  refine ⟨141968913545365753500816371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94645942363577169000544247 141968913545365753500816371)
  ·
    refine ⟨212953370318048630251224557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141968913545365753500816371 212953370318048630251224557)
    ·
      refine ⟨79857513869268236344209209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212953370318048630251224557 79857513869268236344209209)
      ·
        refine ⟨59893135401951177258156907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79857513869268236344209209 59893135401951177258156907)
        ·
          refine ⟨89839703102926765887235361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59893135401951177258156907 89839703102926765887235361)
          ·
            refine ⟨67379777327195074415426521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89839703102926765887235361 67379777327195074415426521)
            ·
              refine ⟨50534832995396305811569891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67379777327195074415426521 50534832995396305811569891)
              ·
                refine ⟨75802249493094458717354837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50534832995396305811569891 75802249493094458717354837)
                ·
                  refine ⟨444153805623600344047001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 75802249493094458717354837 444153805623600344047001)
                  ·
                    rfl

theorem cell22_3892439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_3892439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892439 prefixEnd_3892439 := by exact prefixLift 3892439
  have htrace : WordTrace (prefixWord ++ tailWord_3892439) baseStart_3892439 baseEnd_3892439 := by
    simpa [prefixWord, tailWord_3892439, baseEnd_3892439] using wordTrace_append hprefix tailTrace_3892439
  have hstable : (prefixWord ++ tailWord_3892439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892439).length < 2 ^ (prefixWord ++ tailWord_3892439).sum := by decide
  have hdescent : baseEnd_3892439 < baseStart_3892439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892460 : List Nat := [2, 2, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_3892460 : Nat := 118140960795 + 3892460 * 2 ^ 59
def prefixEnd_3892460 : Nat := 4983230072969 + 3 ^ 40 * 3892460 * 2
def baseEnd_3892460 : Nat := 1332468605599963977365939

theorem tailTrace_3892460 : CollatzResearch.WordTrace tailWord_3892460 prefixEnd_3892460 1332468605599963977365939 := by
  unfold tailWord_3892460
  simp only [CollatzResearch.WordTrace]
  refine ⟨70984839739144837043665417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94646452985526449391553889 70984839739144837043665417)
  ·
    refine ⟨53238629804358627782749063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70984839739144837043665417 53238629804358627782749063)
    ·
      refine ⟨79857944706537941674123595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53238629804358627782749063 79857944706537941674123595)
      ·
        refine ⟨119786917059806912511185393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79857944706537941674123595 119786917059806912511185393)
        ·
          refine ⟨89840187794855184383389045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119786917059806912511185393 89840187794855184383389045)
          ·
            refine ⟨8422517605767673535942723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89840187794855184383389045 8422517605767673535942723)
            ·
              refine ⟨12633776408651510303914085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422517605767673535942723 12633776408651510303914085)
              ·
                refine ⟨2368833076622158181983891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12633776408651510303914085 2368833076622158181983891)
                ·
                  refine ⟨3553249614933237272975837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2368833076622158181983891 3553249614933237272975837)
                  ·
                    refine ⟨1332468605599963977365939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553249614933237272975837 1332468605599963977365939)
                    ·
                      rfl

theorem cell22_3892460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_3892460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892460 prefixEnd_3892460 := by exact prefixLift 3892460
  have htrace : WordTrace (prefixWord ++ tailWord_3892460) baseStart_3892460 baseEnd_3892460 := by
    simpa [prefixWord, tailWord_3892460, baseEnd_3892460] using wordTrace_append hprefix tailTrace_3892460
  have hstable : (prefixWord ++ tailWord_3892460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892460).length < 2 ^ (prefixWord ++ tailWord_3892460).sum := by decide
  have hdescent : baseEnd_3892460 < baseStart_3892460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892503 : List Nat := [1, 1, 3, 4, 1, 1, 3, 3, 1, 4]
def baseStart_3892503 : Nat := 118140960795 + 3892503 * 2 ^ 59
def prefixEnd_3892503 : Nat := 4983230072969 + 3 ^ 40 * 3892503 * 2
def baseEnd_3892503 : Nat := 1332483325378726198540807

theorem tailTrace_3892503 : CollatzResearch.WordTrace tailWord_3892503 prefixEnd_3892503 1332483325378726198540807 := by
  unfold tailWord_3892503
  simp only [CollatzResearch.WordTrace]
  refine ⟨141971247817133892431146163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94647498544755928287430775 141971247817133892431146163)
  ·
    refine ⟨212956871725700838646719245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141971247817133892431146163 212956871725700838646719245)
    ·
      refine ⟨79858826897137814492519717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212956871725700838646719245 79858826897137814492519717)
      ·
        refine ⟨14973530043213340217347447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79858826897137814492519717 14973530043213340217347447)
        ·
          refine ⟨22460295064820010326021171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14973530043213340217347447 22460295064820010326021171)
          ·
            refine ⟨33690442597230015489031757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22460295064820010326021171 33690442597230015489031757)
            ·
              refine ⟨12633915973961255808386909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33690442597230015489031757 12633915973961255808386909)
              ·
                refine ⟨4737718490235470928145091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12633915973961255808386909 4737718490235470928145091)
                ·
                  refine ⟨7106577735353206392217637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4737718490235470928145091 7106577735353206392217637)
                  ·
                    refine ⟨1332483325378726198540807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106577735353206392217637 1332483325378726198540807)
                    ·
                      rfl

theorem cell22_3892503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_3892503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892503 prefixEnd_3892503 := by exact prefixLift 3892503
  have htrace : WordTrace (prefixWord ++ tailWord_3892503) baseStart_3892503 baseEnd_3892503 := by
    simpa [prefixWord, tailWord_3892503, baseEnd_3892503] using wordTrace_append hprefix tailTrace_3892503
  have hstable : (prefixWord ++ tailWord_3892503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892503).length < 2 ^ (prefixWord ++ tailWord_3892503).sum := by decide
  have hdescent : baseEnd_3892503 < baseStart_3892503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892531 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_3892531 : Nat := 118140960795 + 3892531 * 2 ^ 59
def prefixEnd_3892531 : Nat := 4983230072969 + 3 ^ 40 * 3892531 * 2
def baseEnd_3892531 : Nat := 1332492910350943458840721

theorem tailTrace_3892531 : CollatzResearch.WordTrace tailWord_3892531 prefixEnd_3892531 1332492910350943458840721 := by
  unfold tailWord_3892531
  simp only [CollatzResearch.WordTrace]
  refine ⟨141972269061032453213165447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94648179374021635475443631 141972269061032453213165447)
  ·
    refine ⟨212958403591548679819748171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141972269061032453213165447 212958403591548679819748171)
    ·
      refine ⟨319437605387323019729622257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212958403591548679819748171 319437605387323019729622257)
      ·
        refine ⟨239578204040492264797216693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319437605387323019729622257 239578204040492264797216693)
        ·
          refine ⟨22460456628796149824739065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 239578204040492264797216693 22460456628796149824739065)
          ·
            refine ⟨16845342471597112368554299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22460456628796149824739065 16845342471597112368554299)
            ·
              refine ⟨25268013707395668552831449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16845342471597112368554299 25268013707395668552831449)
              ·
                refine ⟨18951010280546751414623587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25268013707395668552831449 18951010280546751414623587)
                ·
                  refine ⟨28426515420820127121935381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18951010280546751414623587 28426515420820127121935381)
                  ·
                    refine ⟨1332492910350943458840721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28426515420820127121935381 1332492910350943458840721)
                    ·
                      rfl

theorem cell22_3892531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_3892531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892531 prefixEnd_3892531 := by exact prefixLift 3892531
  have htrace : WordTrace (prefixWord ++ tailWord_3892531) baseStart_3892531 baseEnd_3892531 := by
    simpa [prefixWord, tailWord_3892531, baseEnd_3892531] using wordTrace_append hprefix tailTrace_3892531
  have hstable : (prefixWord ++ tailWord_3892531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892531).length < 2 ^ (prefixWord ++ tailWord_3892531).sum := by decide
  have hdescent : baseEnd_3892531 < baseStart_3892531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892533 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3892533 : Nat := 118140960795 + 3892533 * 2 ^ 59
def prefixEnd_3892533 : Nat := 4983230072969 + 3 ^ 40 * 3892533 * 2
def baseEnd_3892533 : Nat := 1332493594991816120290715

theorem tailTrace_3892533 : CollatzResearch.WordTrace tailWord_3892533 prefixEnd_3892533 1332493594991816120290715 := by
  unfold tailWord_3892533
  simp only [CollatzResearch.WordTrace]
  refine ⟨141972342007025207554738253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94648228004683471703158835 141972342007025207554738253)
  ·
    refine ⟨53239628252634452833026845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141972342007025207554738253 53239628252634452833026845)
    ·
      refine ⟨19964860594737919812385067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53239628252634452833026845 19964860594737919812385067)
      ·
        refine ⟨29947290892106879718577601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19964860594737919812385067 29947290892106879718577601)
        ·
          refine ⟨22460468169080159788933201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29947290892106879718577601 22460468169080159788933201)
          ·
            refine ⟨16845351126810119841699901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22460468169080159788933201 16845351126810119841699901)
            ·
              refine ⟨6317006672553794940637463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16845351126810119841699901 6317006672553794940637463)
              ·
                refine ⟨9475510008830692410956195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6317006672553794940637463 9475510008830692410956195)
                ·
                  refine ⟨14213265013246038616434293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9475510008830692410956195 14213265013246038616434293)
                  ·
                    refine ⟨1332493594991816120290715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14213265013246038616434293 1332493594991816120290715)
                    ·
                      rfl

theorem cell22_3892533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3892533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892533 prefixEnd_3892533 := by exact prefixLift 3892533
  have htrace : WordTrace (prefixWord ++ tailWord_3892533) baseStart_3892533 baseEnd_3892533 := by
    simpa [prefixWord, tailWord_3892533, baseEnd_3892533] using wordTrace_append hprefix tailTrace_3892533
  have hstable : (prefixWord ++ tailWord_3892533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892533).length < 2 ^ (prefixWord ++ tailWord_3892533).sum := by decide
  have hdescent : baseEnd_3892533 < baseStart_3892533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892584 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 2, 3]
def baseStart_3892584 : Nat := 118140960795 + 3892584 * 2 ^ 59
def prefixEnd_3892584 : Nat := 4983230072969 + 3 ^ 40 * 3892584 * 2
def baseEnd_3892584 : Nat := 1332511053334068987265559

theorem tailTrace_3892584 : CollatzResearch.WordTrace tailWord_3892584 prefixEnd_3892584 1332511053334068987265559 := by
  unfold tailWord_3892584
  simp only [CollatzResearch.WordTrace]
  refine ⟨70987101064920221632422403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94649468086560295509896537 70987101064920221632422403)
  ·
    refine ⟨106480651597380332448633605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70987101064920221632422403 106480651597380332448633605)
    ·
      refine ⟨19965122174508812334118801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106480651597380332448633605 19965122174508812334118801)
      ·
        refine ⟨14973841630881609250589101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19965122174508812334118801 14973841630881609250589101)
        ·
          refine ⟨5615190611580603468970913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14973841630881609250589101 5615190611580603468970913)
          ·
            refine ⟨4211392958685452601728185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5615190611580603468970913 4211392958685452601728185)
            ·
              refine ⟨3158544719014089451296139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211392958685452601728185 3158544719014089451296139)
              ·
                refine ⟨4737817078521134176944209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158544719014089451296139 4737817078521134176944209)
                ·
                  refine ⟨3553362808890850632708157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4737817078521134176944209 3553362808890850632708157)
                  ·
                    refine ⟨1332511053334068987265559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553362808890850632708157 1332511053334068987265559)
                    ·
                      rfl

theorem cell22_3892584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_3892584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892584 prefixEnd_3892584 := by exact prefixLift 3892584
  have htrace : WordTrace (prefixWord ++ tailWord_3892584) baseStart_3892584 baseEnd_3892584 := by
    simpa [prefixWord, tailWord_3892584, baseEnd_3892584] using wordTrace_append hprefix tailTrace_3892584
  have hstable : (prefixWord ++ tailWord_3892584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892584).length < 2 ^ (prefixWord ++ tailWord_3892584).sum := by decide
  have hdescent : baseEnd_3892584 < baseStart_3892584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892683 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_3892683 : Nat := 118140960795 + 3892683 * 2 ^ 59
def prefixEnd_3892683 : Nat := 4983230072969 + 3 ^ 40 * 3892683 * 2
def baseEnd_3892683 : Nat := 1332544943057265729040255

theorem tailTrace_3892683 : CollatzResearch.WordTrace tailWord_3892683 prefixEnd_3892683 1332544943057265729040255 := by
  unfold tailWord_3892683
  simp only [CollatzResearch.WordTrace]
  refine ⟨141977812956481783172698703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94651875304321188781799135 141977812956481783172698703)
  ·
    refine ⟨212966719434722674759048055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141977812956481783172698703 212966719434722674759048055)
    ·
      refine ⟨319450079152084012138572083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212966719434722674759048055 319450079152084012138572083)
      ·
        refine ⟨479175118728126018207858125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319450079152084012138572083 479175118728126018207858125)
        ·
          refine ⟨179690669523047256827946797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479175118728126018207858125 179690669523047256827946797)
          ·
            refine ⟨67384001071142721310480049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179690669523047256827946797 67384001071142721310480049)
            ·
              refine ⟨50538000803357040982860037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67384001071142721310480049 50538000803357040982860037)
              ·
                refine ⟨9475875150629445184286257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50538000803357040982860037 9475875150629445184286257)
                ·
                  refine ⟨7106906362972083888214693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9475875150629445184286257 7106906362972083888214693)
                  ·
                    refine ⟨1332544943057265729040255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106906362972083888214693 1332544943057265729040255)
                    ·
                      rfl

theorem cell22_3892683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_3892683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892683 prefixEnd_3892683 := by exact prefixLift 3892683
  have htrace : WordTrace (prefixWord ++ tailWord_3892683) baseStart_3892683 baseEnd_3892683 := by
    simpa [prefixWord, tailWord_3892683, baseEnd_3892683] using wordTrace_append hprefix tailTrace_3892683
  have hstable : (prefixWord ++ tailWord_3892683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892683).length < 2 ^ (prefixWord ++ tailWord_3892683).sum := by decide
  have hdescent : baseEnd_3892683 < baseStart_3892683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892734 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3892734 : Nat := 118140960795 + 3892734 * 2 ^ 59
def prefixEnd_3892734 : Nat := 4983230072969 + 3 ^ 40 * 3892734 * 2
def baseEnd_3892734 : Nat := 1332562401399518596015099

theorem tailTrace_3892734 : CollatzResearch.WordTrace tailWord_3892734 prefixEnd_3892734 1332562401399518596015099 := by
  unfold tailWord_3892734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17747459134912127360350657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94653115386198012588536837 17747459134912127360350657)
  ·
    refine ⟨13310594351184095520262993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17747459134912127360350657 13310594351184095520262993)
    ·
      refine ⟨9982945763388071640197245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13310594351184095520262993 9982945763388071640197245)
      ·
        refine ⟨3743604661270526865073967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9982945763388071640197245 3743604661270526865073967)
        ·
          refine ⟨5615406991905790297610951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3743604661270526865073967 5615406991905790297610951)
          ·
            refine ⟨8423110487858685446416427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615406991905790297610951 8423110487858685446416427)
            ·
              refine ⟨12634665731788028169624641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423110487858685446416427 12634665731788028169624641)
              ·
                refine ⟨9475999298841021127218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12634665731788028169624641 9475999298841021127218481)
                ·
                  refine ⟨7106999474130765845413861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9475999298841021127218481 7106999474130765845413861)
                  ·
                    refine ⟨1332562401399518596015099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7106999474130765845413861 1332562401399518596015099)
                    ·
                      rfl

theorem cell22_3892734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3892734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892734 prefixEnd_3892734 := by exact prefixLift 3892734
  have htrace : WordTrace (prefixWord ++ tailWord_3892734) baseStart_3892734 baseEnd_3892734 := by
    simpa [prefixWord, tailWord_3892734, baseEnd_3892734] using wordTrace_append hprefix tailTrace_3892734
  have hstable : (prefixWord ++ tailWord_3892734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892734).length < 2 ^ (prefixWord ++ tailWord_3892734).sum := by decide
  have hdescent : baseEnd_3892734 < baseStart_3892734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892749 : List Nat := [1, 7, 1, 1, 2, 1, 2, 7]
def baseStart_3892749 : Nat := 118140960795 + 3892749 * 2 ^ 59
def prefixEnd_3892749 : Nat := 4983230072969 + 3 ^ 40 * 3892749 * 2
def baseEnd_3892749 : Nat := 148063059578451506321117

theorem tailTrace_3892749 : CollatzResearch.WordTrace tailWord_3892749 prefixEnd_3892749 148063059578451506321117 := by
  unfold tailWord_3892749
  simp only [CollatzResearch.WordTrace]
  refine ⟨141980220174242676444601301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94653480116161784296400867 141980220174242676444601301)
  ·
    refine ⟨3327661410333812729170343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141980220174242676444601301 3327661410333812729170343)
    ·
      refine ⟨4991492115500719093755515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3327661410333812729170343 4991492115500719093755515)
      ·
        refine ⟨7487238173251078640633273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4991492115500719093755515 7487238173251078640633273)
        ·
          refine ⟨5615428629938308980474955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7487238173251078640633273 5615428629938308980474955)
          ·
            refine ⟨8423142944907463470712433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615428629938308980474955 8423142944907463470712433)
            ·
              refine ⟨6317357208680597603034325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8423142944907463470712433 6317357208680597603034325)
              ·
                refine ⟨148063059578451506321117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6317357208680597603034325 148063059578451506321117)
                ·
                  rfl

theorem cell22_3892749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 7].length) (baseStart_3892749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892749 prefixEnd_3892749 := by exact prefixLift 3892749
  have htrace : WordTrace (prefixWord ++ tailWord_3892749) baseStart_3892749 baseEnd_3892749 := by
    simpa [prefixWord, tailWord_3892749, baseEnd_3892749] using wordTrace_append hprefix tailTrace_3892749
  have hstable : (prefixWord ++ tailWord_3892749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892749).length < 2 ^ (prefixWord ++ tailWord_3892749).sum := by decide
  have hdescent : baseEnd_3892749 < baseStart_3892749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892835 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_3892835 : Nat := 118140960795 + 3892835 * 2 ^ 59
def prefixEnd_3892835 : Nat := 4983230072969 + 3 ^ 40 * 3892835 * 2
def baseEnd_3892835 : Nat := 1332596975763587999239789

theorem tailTrace_3892835 : CollatzResearch.WordTrace tailWord_3892835 prefixEnd_3892835 1332596975763587999239789 := by
  unfold tailWord_3892835
  simp only [CollatzResearch.WordTrace]
  refine ⟨141983356851931113132231959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94655571234620742088154639 141983356851931113132231959)
  ·
    refine ⟨212975035277896669698347939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141983356851931113132231959 212975035277896669698347939)
    ·
      refine ⟨319462552916845004547521909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212975035277896669698347939 319462552916845004547521909)
      ·
        refine ⟨29949614335954219176330179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319462552916845004547521909 29949614335954219176330179)
        ·
          refine ⟨44924421503931328764495269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29949614335954219176330179 44924421503931328764495269)
          ·
            refine ⟨8423329031987124143342863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44924421503931328764495269 8423329031987124143342863)
            ·
              refine ⟨12634993547980686215014295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423329031987124143342863 12634993547980686215014295)
              ·
                refine ⟨18952490321971029322521443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12634993547980686215014295 18952490321971029322521443)
                ·
                  refine ⟨28428735482956543983782165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18952490321971029322521443 28428735482956543983782165)
                  ·
                    refine ⟨1332596975763587999239789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28428735482956543983782165 1332596975763587999239789)
                    ·
                      rfl

theorem cell22_3892835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_3892835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892835 prefixEnd_3892835 := by exact prefixLift 3892835
  have htrace : WordTrace (prefixWord ++ tailWord_3892835) baseStart_3892835 baseEnd_3892835 := by
    simpa [prefixWord, tailWord_3892835, baseEnd_3892835] using wordTrace_append hprefix tailTrace_3892835
  have hstable : (prefixWord ++ tailWord_3892835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892835).length < 2 ^ (prefixWord ++ tailWord_3892835).sum := by decide
  have hdescent : baseEnd_3892835 < baseStart_3892835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892850 : List Nat := [3, 2, 1, 2, 3, 2, 9]
def baseStart_3892850 : Nat := 118140960795 + 3892850 * 2 ^ 59
def prefixEnd_3892850 : Nat := 4983230072969 + 3 ^ 40 * 3892850 * 2
def baseEnd_3892850 : Nat := 49355633724819739263509

theorem tailTrace_3892850 : CollatzResearch.WordTrace tailWord_3892850 prefixEnd_3892850 49355633724819739263509 := by
  unfold tailWord_3892850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35495975986719192673507001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94655935964584513796018669 35495975986719192673507001)
  ·
    refine ⟨26621981990039394505130251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35495975986719192673507001 26621981990039394505130251)
    ·
      refine ⟨39932972985059091757695377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26621981990039394505130251 39932972985059091757695377)
      ·
        refine ⟨29949729738794318818271533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39932972985059091757695377 29949729738794318818271533)
        ·
          refine ⟨11231148652047869556851825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29949729738794318818271533 11231148652047869556851825)
          ·
            refine ⟨8423361489035902167638869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11231148652047869556851825 8423361489035902167638869)
            ·
              refine ⟨49355633724819739263509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8423361489035902167638869 49355633724819739263509)
              ·
                rfl

theorem cell22_3892850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 9].length) (baseStart_3892850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892850 prefixEnd_3892850 := by exact prefixLift 3892850
  have htrace : WordTrace (prefixWord ++ tailWord_3892850) baseStart_3892850 baseEnd_3892850 := by
    simpa [prefixWord, tailWord_3892850, baseEnd_3892850] using wordTrace_append hprefix tailTrace_3892850
  have hstable : (prefixWord ++ tailWord_3892850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892850).length < 2 ^ (prefixWord ++ tailWord_3892850).sum := by decide
  have hdescent : baseEnd_3892850 < baseStart_3892850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892854 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_3892854 : Nat := 118140960795 + 3892854 * 2 ^ 59
def prefixEnd_3892854 : Nat := 4983230072969 + 3 ^ 40 * 3892854 * 2
def baseEnd_3892854 : Nat := 1332603479851878283014731

theorem tailTrace_3892854 : CollatzResearch.WordTrace tailWord_3892854 prefixEnd_3892854 1332603479851878283014731 := by
  unfold tailWord_3892854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8874003114928892461073351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94656033225908186251449077 8874003114928892461073351)
  ·
    refine ⟨13311004672393338691610027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8874003114928892461073351 13311004672393338691610027)
    ·
      refine ⟨19966507008590008037415041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13311004672393338691610027 19966507008590008037415041)
      ·
        refine ⟨14974880256442506028061281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19966507008590008037415041 14974880256442506028061281)
        ·
          refine ⟨11231160192331879521045961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14974880256442506028061281 11231160192331879521045961)
          ·
            refine ⟨8423370144248909640784471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11231160192331879521045961 8423370144248909640784471)
            ·
              refine ⟨12635055216373364461176707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8423370144248909640784471 12635055216373364461176707)
              ·
                refine ⟨18952582824560046691765061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635055216373364461176707 18952582824560046691765061)
                ·
                  refine ⟨3553609279605008754705949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18952582824560046691765061 3553609279605008754705949)
                  ·
                    refine ⟨1332603479851878283014731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553609279605008754705949 1332603479851878283014731)
                    ·
                      rfl

theorem cell22_3892854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_3892854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892854 prefixEnd_3892854 := by exact prefixLift 3892854
  have htrace : WordTrace (prefixWord ++ tailWord_3892854) baseStart_3892854 baseEnd_3892854 := by
    simpa [prefixWord, tailWord_3892854, baseEnd_3892854] using wordTrace_append hprefix tailTrace_3892854
  have hstable : (prefixWord ++ tailWord_3892854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892854).length < 2 ^ (prefixWord ++ tailWord_3892854).sum := by decide
  have hdescent : baseEnd_3892854 < baseStart_3892854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892942 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_3892942 : Nat := 118140960795 + 3892942 * 2 ^ 59
def prefixEnd_3892942 : Nat := 4983230072969 + 3 ^ 40 * 3892942 * 2
def baseEnd_3892942 : Nat := 1332633604050275386814461

theorem tailTrace_3892942 : CollatzResearch.WordTrace tailWord_3892942 prefixEnd_3892942 1332633604050275386814461 := by
  unfold tailWord_3892942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748407432817933800797135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94658172975028980270918053 17748407432817933800797135)
  ·
    refine ⟨26622611149226900701195703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17748407432817933800797135 26622611149226900701195703)
    ·
      refine ⟨39933916723840351051793555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26622611149226900701195703 39933916723840351051793555)
      ·
        refine ⟨59900875085760526577690333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39933916723840351051793555 59900875085760526577690333)
        ·
          refine ⟨22462828157160197466633875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59900875085760526577690333 22462828157160197466633875)
          ·
            refine ⟨33694242235740296199950813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22462828157160197466633875 33694242235740296199950813)
            ·
              refine ⟨12635340838402611074981555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33694242235740296199950813 12635340838402611074981555)
              ·
                refine ⟨18953011257603916612472333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12635340838402611074981555 18953011257603916612472333)
                ·
                  refine ⟨7107379221601468729677125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18953011257603916612472333 7107379221601468729677125)
                  ·
                    refine ⟨1332633604050275386814461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107379221601468729677125 1332633604050275386814461)
                    ·
                      rfl

theorem cell22_3892942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_3892942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892942 prefixEnd_3892942 := by exact prefixLift 3892942
  have htrace : WordTrace (prefixWord ++ tailWord_3892942) baseStart_3892942 baseEnd_3892942 := by
    simpa [prefixWord, tailWord_3892942, baseEnd_3892942] using wordTrace_append hprefix tailTrace_3892942
  have hstable : (prefixWord ++ tailWord_3892942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892942).length < 2 ^ (prefixWord ++ tailWord_3892942).sum := by decide
  have hdescent : baseEnd_3892942 < baseStart_3892942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892959 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 1, 4]
def baseStart_3892959 : Nat := 118140960795 + 3892959 * 2 ^ 59
def prefixEnd_3892959 : Nat := 4983230072969 + 3 ^ 40 * 3892959 * 2
def baseEnd_3892959 : Nat := 1332639423497693009139409

theorem tailTrace_3892959 : CollatzResearch.WordTrace tailWord_3892959 prefixEnd_3892959 1332639423497693009139409 := by
  unfold tailWord_3892959
  simp only [CollatzResearch.WordTrace]
  refine ⟨141987879503481882309745931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94658586335654588206497287 141987879503481882309745931)
  ·
    refine ⟨212981819255222823464618897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141987879503481882309745931 212981819255222823464618897)
    ·
      refine ⟨159736364441417117598464173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212981819255222823464618897 159736364441417117598464173)
      ·
        refine ⟨59901136665531419099424065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159736364441417117598464173 59901136665531419099424065)
        ·
          refine ⟨44925852499148564324568049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59901136665531419099424065 44925852499148564324568049)
          ·
            refine ⟨33694389374361423243426037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44925852499148564324568049 33694389374361423243426037)
            ·
              refine ⟨3158849003846383429071191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33694389374361423243426037 3158849003846383429071191)
              ·
                refine ⟨4738273505769575143606787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158849003846383429071191 4738273505769575143606787)
                ·
                  refine ⟨7107410258654362715410181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738273505769575143606787 7107410258654362715410181)
                  ·
                    refine ⟨1332639423497693009139409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107410258654362715410181 1332639423497693009139409)
                    ·
                      rfl

theorem cell22_3892959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_3892959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892959 prefixEnd_3892959 := by exact prefixLift 3892959
  have htrace : WordTrace (prefixWord ++ tailWord_3892959) baseStart_3892959 baseEnd_3892959 := by
    simpa [prefixWord, tailWord_3892959, baseEnd_3892959] using wordTrace_append hprefix tailTrace_3892959
  have hstable : (prefixWord ++ tailWord_3892959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892959).length < 2 ^ (prefixWord ++ tailWord_3892959).sum := by decide
  have hdescent : baseEnd_3892959 < baseStart_3892959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892967 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3892967 : Nat := 118140960795 + 3892967 * 2 ^ 59
def prefixEnd_3892967 : Nat := 4983230072969 + 3 ^ 40 * 3892967 * 2
def baseEnd_3892967 : Nat := 1332642162061183654939385

theorem tailTrace_3892967 : CollatzResearch.WordTrace tailWord_3892967 prefixEnd_3892967 1332642162061183654939385 := by
  unfold tailWord_3892967
  simp only [CollatzResearch.WordTrace]
  refine ⟨141988171287452899676037155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94658780858301933117358103 141988171287452899676037155)
  ·
    refine ⟨212982256931179349514055733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141988171287452899676037155 212982256931179349514055733)
    ·
      refine ⟨19967086587298064016942725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212982256931179349514055733 19967086587298064016942725)
      ·
        refine ⟨3743828735118387003176761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19967086587298064016942725 3743828735118387003176761)
        ·
          refine ⟨2807871551338790252382571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3743828735118387003176761 2807871551338790252382571)
          ·
            refine ⟨4211807327008185378573857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2807871551338790252382571 4211807327008185378573857)
            ·
              refine ⟨3158855495256139033930393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211807327008185378573857 3158855495256139033930393)
              ·
                refine ⟨2369141621442104275447795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158855495256139033930393 2369141621442104275447795)
                ·
                  refine ⟨3553712432163156413171693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369141621442104275447795 3553712432163156413171693)
                  ·
                    refine ⟨1332642162061183654939385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553712432163156413171693 1332642162061183654939385)
                    ·
                      rfl

theorem cell22_3892967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3892967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892967 prefixEnd_3892967 := by exact prefixLift 3892967
  have htrace : WordTrace (prefixWord ++ tailWord_3892967) baseStart_3892967 baseEnd_3892967 := by
    simpa [prefixWord, tailWord_3892967, baseEnd_3892967] using wordTrace_append hprefix tailTrace_3892967
  have hstable : (prefixWord ++ tailWord_3892967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892967).length < 2 ^ (prefixWord ++ tailWord_3892967).sum := by decide
  have hdescent : baseEnd_3892967 < baseStart_3892967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892972 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 4, 3]
def baseStart_3892972 : Nat := 118140960795 + 3892972 * 2 ^ 59
def prefixEnd_3892972 : Nat := 4983230072969 + 3 ^ 40 * 3892972 * 2
def baseEnd_3892972 : Nat := 1332643873663365308564369

theorem tailTrace_3892972 : CollatzResearch.WordTrace tailWord_3892972 prefixEnd_3892972 1332643873663365308564369 := by
  unfold tailWord_3892972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70994176826217392764984585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94658902434956523686646113 70994176826217392764984585)
  ·
    refine ⟨53245632619663044573738439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70994176826217392764984585 53245632619663044573738439)
    ·
      refine ⟨79868448929494566860607659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53245632619663044573738439 79868448929494566860607659)
      ·
        refine ⟨119802673394241850290911489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79868448929494566860607659 119802673394241850290911489)
        ·
          refine ⟨89852005045681387718183617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119802673394241850290911489 89852005045681387718183617)
          ·
            refine ⟨67389003784261040788637713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89852005045681387718183617 67389003784261040788637713)
            ·
              refine ⟨50541752838195780591478285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67389003784261040788637713 50541752838195780591478285)
              ·
                refine ⟨18953157314323417721804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50541752838195780591478285 18953157314323417721804357)
                ·
                  refine ⟨3553716996435640822838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18953157314323417721804357 3553716996435640822838317)
                  ·
                    refine ⟨1332643873663365308564369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553716996435640822838317 1332643873663365308564369)
                    ·
                      rfl

theorem cell22_3892972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_3892972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892972 prefixEnd_3892972 := by exact prefixLift 3892972
  have htrace : WordTrace (prefixWord ++ tailWord_3892972) baseStart_3892972 baseEnd_3892972 := by
    simpa [prefixWord, tailWord_3892972, baseEnd_3892972] using wordTrace_append hprefix tailTrace_3892972
  have hstable : (prefixWord ++ tailWord_3892972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892972).length < 2 ^ (prefixWord ++ tailWord_3892972).sum := by decide
  have hdescent : baseEnd_3892972 < baseStart_3892972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3892974 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_3892974 : Nat := 118140960795 + 3892974 * 2 ^ 59
def prefixEnd_3892974 : Nat := 4983230072969 + 3 ^ 40 * 3892974 * 2
def baseEnd_3892974 : Nat := 444214852768079323338121

theorem tailTrace_3892974 : CollatzResearch.WordTrace tailWord_3892974 prefixEnd_3892974 444214852768079323338121 := by
  unfold tailWord_3892974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17748553324803442483942747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94658951065618359914361317 17748553324803442483942747)
  ·
    refine ⟨26622829987205163725914121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17748553324803442483942747 26622829987205163725914121)
    ·
      refine ⟨19967122490403872794435591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26622829987205163725914121 19967122490403872794435591)
      ·
        refine ⟨29950683735605809191653387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19967122490403872794435591 29950683735605809191653387)
        ·
          refine ⟨44926025603408713787480081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29950683735605809191653387 44926025603408713787480081)
          ·
            refine ⟨33694519202556535340610061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44926025603408713787480081 33694519202556535340610061)
            ·
              refine ⟨12635444700958700752728773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33694519202556535340610061 12635444700958700752728773)
              ·
                refine ⟨2369145881429756391136645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12635444700958700752728773 2369145881429756391136645)
                ·
                  refine ⟨444214852768079323338121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369145881429756391136645 444214852768079323338121)
                  ·
                    rfl

theorem cell22_3892974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_3892974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3892974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3892974 prefixEnd_3892974 := by exact prefixLift 3892974
  have htrace : WordTrace (prefixWord ++ tailWord_3892974) baseStart_3892974 baseEnd_3892974 := by
    simpa [prefixWord, tailWord_3892974, baseEnd_3892974] using wordTrace_append hprefix tailTrace_3892974
  have hstable : (prefixWord ++ tailWord_3892974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3892974).length < 2 ^ (prefixWord ++ tailWord_3892974).sum := by decide
  have hdescent : baseEnd_3892974 < baseStart_3892974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3892974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893107 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_3893107 : Nat := 118140960795 + 3893107 * 2 ^ 59
def prefixEnd_3893107 : Nat := 4983230072969 + 3 ^ 40 * 3893107 * 2
def baseEnd_3893107 : Nat := 1332690086922269956438955

theorem tailTrace_3893107 : CollatzResearch.WordTrace tailWord_3893107 prefixEnd_3893107 1332690086922269956438955 := by
  unfold tailWord_3893107
  simp only [CollatzResearch.WordTrace]
  refine ⟨141993277506945703586133575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94662185004630469057422383 141993277506945703586133575)
  ·
    refine ⟨212989916260418555379200363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141993277506945703586133575 212989916260418555379200363)
    ·
      refine ⟨319484874390627833068800545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212989916260418555379200363 319484874390627833068800545)
      ·
        refine ⟨239613655792970874801600409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 319484874390627833068800545 239613655792970874801600409)
        ·
          refine ⟨179710241844728156101200307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239613655792970874801600409 179710241844728156101200307)
          ·
            refine ⟨269565362767092234151800461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179710241844728156101200307 269565362767092234151800461)
            ·
              refine ⟨101087011037659587806925173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269565362767092234151800461 101087011037659587806925173)
              ·
                refine ⟨9476907284780586356899235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101087011037659587806925173 9476907284780586356899235)
                ·
                  refine ⟨14215360927170879535348853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9476907284780586356899235 14215360927170879535348853)
                  ·
                    refine ⟨1332690086922269956438955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14215360927170879535348853 1332690086922269956438955)
                    ·
                      rfl

theorem cell22_3893107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_3893107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893107 prefixEnd_3893107 := by exact prefixLift 3893107
  have htrace : WordTrace (prefixWord ++ tailWord_3893107) baseStart_3893107 baseEnd_3893107 := by
    simpa [prefixWord, tailWord_3893107, baseEnd_3893107] using wordTrace_append hprefix tailTrace_3893107
  have hstable : (prefixWord ++ tailWord_3893107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893107).length < 2 ^ (prefixWord ++ tailWord_3893107).sum := by decide
  have hdescent : baseEnd_3893107 < baseStart_3893107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893124 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3893124 : Nat := 118140960795 + 3893124 * 2 ^ 59
def prefixEnd_3893124 : Nat := 4983230072969 + 3 ^ 40 * 3893124 * 2
def baseEnd_3893124 : Nat := 1332695906369687578763903

theorem tailTrace_3893124 : CollatzResearch.WordTrace tailWord_3893124 prefixEnd_3893124 1332695906369687578763903 := by
  unfold tailWord_3893124
  simp only [CollatzResearch.WordTrace]
  refine ⟨70996948773942057744751213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94662598365256076993001617 70996948773942057744751213)
  ·
    refine ⟨26623855790228271654281705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70996948773942057744751213 26623855790228271654281705)
    ·
      refine ⟨19967891842671203740711279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26623855790228271654281705 19967891842671203740711279)
      ·
        refine ⟨29951837764006805611066919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19967891842671203740711279 29951837764006805611066919)
        ·
          refine ⟨44927756646010208416600379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29951837764006805611066919 44927756646010208416600379)
          ·
            refine ⟨67391634969015312624900569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44927756646010208416600379 67391634969015312624900569)
            ·
              refine ⟨50543726226761484468675427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67391634969015312624900569 50543726226761484468675427)
              ·
                refine ⟨75815589340142226703013141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50543726226761484468675427 75815589340142226703013141)
                ·
                  refine ⟨3553855750319166876703741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75815589340142226703013141 3553855750319166876703741)
                  ·
                    refine ⟨1332695906369687578763903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553855750319166876703741 1332695906369687578763903)
                    ·
                      rfl

theorem cell22_3893124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3893124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893124 prefixEnd_3893124 := by exact prefixLift 3893124
  have htrace : WordTrace (prefixWord ++ tailWord_3893124) baseStart_3893124 baseEnd_3893124 := by
    simpa [prefixWord, tailWord_3893124, baseEnd_3893124] using wordTrace_append hprefix tailTrace_3893124
  have hstable : (prefixWord ++ tailWord_3893124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893124).length < 2 ^ (prefixWord ++ tailWord_3893124).sum := by decide
  have hdescent : baseEnd_3893124 < baseStart_3893124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893128 : List Nat := [2, 1, 3, 3, 3, 1, 3, 1, 1, 4]
def baseStart_3893128 : Nat := 118140960795 + 3893128 * 2 ^ 59
def prefixEnd_3893128 : Nat := 4983230072969 + 3 ^ 40 * 3893128 * 2
def baseEnd_3893128 : Nat := 1332697275651432901663891

theorem tailTrace_3893128 : CollatzResearch.WordTrace tailWord_3893128 prefixEnd_3893128 1332697275651432901663891 := by
  unfold tailWord_3893128
  simp only [CollatzResearch.WordTrace]
  refine ⟨70997021719934812086324019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94662695626579749448432025 70997021719934812086324019)
  ·
    refine ⟨106495532579902218129486029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70997021719934812086324019 106495532579902218129486029)
    ·
      refine ⟨39935824717463331798557261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106495532579902218129486029 39935824717463331798557261)
      ·
        refine ⟨14975934269048749424458973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39935824717463331798557261 14975934269048749424458973)
        ·
          refine ⟨5615975350893281034172115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14975934269048749424458973 5615975350893281034172115)
          ·
            refine ⟨8423963026339921551258173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615975350893281034172115 8423963026339921551258173)
            ·
              refine ⟨3158986134877470581721815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8423963026339921551258173 3158986134877470581721815)
              ·
                refine ⟨4738479202316205872582723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3158986134877470581721815 4738479202316205872582723)
                ·
                  refine ⟨7107718803474308808874085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4738479202316205872582723 7107718803474308808874085)
                  ·
                    refine ⟨1332697275651432901663891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7107718803474308808874085 1332697275651432901663891)
                    ·
                      rfl

theorem cell22_3893128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_3893128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893128 prefixEnd_3893128 := by exact prefixLift 3893128
  have htrace : WordTrace (prefixWord ++ tailWord_3893128) baseStart_3893128 baseEnd_3893128 := by
    simpa [prefixWord, tailWord_3893128, baseEnd_3893128] using wordTrace_append hprefix tailTrace_3893128
  have hstable : (prefixWord ++ tailWord_3893128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893128).length < 2 ^ (prefixWord ++ tailWord_3893128).sum := by decide
  have hdescent : baseEnd_3893128 < baseStart_3893128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893141 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_3893141 : Nat := 118140960795 + 3893141 * 2 ^ 59
def prefixEnd_3893141 : Nat := 4983230072969 + 3 ^ 40 * 3893141 * 2
def baseEnd_3893141 : Nat := 1332701725817105201088851

theorem tailTrace_3893141 : CollatzResearch.WordTrace tailWord_3893141 prefixEnd_3893141 1332701725817105201088851 := by
  unfold tailWord_3893141
  simp only [CollatzResearch.WordTrace]
  refine ⟨141994517588822527392871277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94663011725881684928580851 141994517588822527392871277)
  ·
    refine ⟨53247944095808447772326729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141994517588822527392871277 53247944095808447772326729)
    ·
      refine ⟨39935958071856335829245047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53247944095808447772326729 39935958071856335829245047)
      ·
        refine ⟨59903937107784503743867571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39935958071856335829245047 59903937107784503743867571)
        ·
          refine ⟨89855905661676755615801357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59903937107784503743867571 89855905661676755615801357)
          ·
            refine ⟨33695964623128783355925509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89855905661676755615801357 33695964623128783355925509)
            ·
              refine ⟨6317993366836646879236033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33695964623128783355925509 6317993366836646879236033)
              ·
                refine ⟨4738495025127485159427025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6317993366836646879236033 4738495025127485159427025)
                ·
                  refine ⟨3553871268845613869570269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738495025127485159427025 3553871268845613869570269)
                  ·
                    refine ⟨1332701725817105201088851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3553871268845613869570269 1332701725817105201088851)
                    ·
                      rfl

theorem cell22_3893141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_3893141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893141 prefixEnd_3893141 := by exact prefixLift 3893141
  have htrace : WordTrace (prefixWord ++ tailWord_3893141) baseStart_3893141 baseEnd_3893141 := by
    simpa [prefixWord, tailWord_3893141, baseEnd_3893141] using wordTrace_append hprefix tailTrace_3893141
  have hstable : (prefixWord ++ tailWord_3893141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893141).length < 2 ^ (prefixWord ++ tailWord_3893141).sum := by decide
  have hdescent : baseEnd_3893141 < baseStart_3893141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893143 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 4]
def baseStart_3893143 : Nat := 118140960795 + 3893143 * 2 ^ 59
def prefixEnd_3893143 : Nat := 4983230072969 + 3 ^ 40 * 3893143 * 2
def baseEnd_3893143 : Nat := 444234136819325954179615

theorem tailTrace_3893143 : CollatzResearch.WordTrace tailWord_3893143 prefixEnd_3893143 444234136819325954179615 := by
  unfold tailWord_3893143
  simp only [CollatzResearch.WordTrace]
  refine ⟨141994590534815281734444083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94663060356543521156296055 141994590534815281734444083)
  ·
    refine ⟨212991885802222922601666125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141994590534815281734444083 212991885802222922601666125)
    ·
      refine ⟨79871957175833595975624797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212991885802222922601666125 79871957175833595975624797)
      ·
        refine ⟨29951983940937598490859299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79871957175833595975624797 29951983940937598490859299)
        ·
          refine ⟨44927975911406397736288949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29951983940937598490859299 44927975911406397736288949)
          ·
            refine ⟨4211997741694349787777089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44927975911406397736288949 4211997741694349787777089)
            ·
              refine ⟨3158998306270762340832817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4211997741694349787777089 3158998306270762340832817)
              ·
                refine ⟨2369248729703071755624613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3158998306270762340832817 2369248729703071755624613)
                ·
                  refine ⟨444234136819325954179615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369248729703071755624613 444234136819325954179615)
                  ·
                    rfl

theorem cell22_3893143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 4].length) (baseStart_3893143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893143 prefixEnd_3893143 := by exact prefixLift 3893143
  have htrace : WordTrace (prefixWord ++ tailWord_3893143) baseStart_3893143 baseEnd_3893143 := by
    simpa [prefixWord, tailWord_3893143, baseEnd_3893143] using wordTrace_append hprefix tailTrace_3893143
  have hstable : (prefixWord ++ tailWord_3893143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893143).length < 2 ^ (prefixWord ++ tailWord_3893143).sum := by decide
  have hdescent : baseEnd_3893143 < baseStart_3893143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893152 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 7]
def baseStart_3893152 : Nat := 118140960795 + 3893152 * 2 ^ 59
def prefixEnd_3893152 : Nat := 4983230072969 + 3 ^ 40 * 3893152 * 2
def baseEnd_3893152 : Nat := 1332705491341904839063817

theorem tailTrace_3893152 : CollatzResearch.WordTrace tailWord_3893152 prefixEnd_3893152 1332705491341904839063817 := by
  unfold tailWord_3893152
  simp only [CollatzResearch.WordTrace]
  refine ⟨70997459395891338135760855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94663279194521784181014473 70997459395891338135760855)
  ·
    refine ⟨106496189093837007203641283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70997459395891338135760855 106496189093837007203641283)
    ·
      refine ⟨159744283640755510805461925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106496189093837007203641283 159744283640755510805461925)
      ·
        refine ⟨29952053182641658276024111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159744283640755510805461925 29952053182641658276024111)
        ·
          refine ⟨44928079773962487414036167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29952053182641658276024111 44928079773962487414036167)
          ·
            refine ⟨67392119660943731121054251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44928079773962487414036167 67392119660943731121054251)
            ·
              refine ⟨101088179491415596681581377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67392119660943731121054251 101088179491415596681581377)
              ·
                refine ⟨75816134618561697511186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101088179491415596681581377 75816134618561697511186033)
                ·
                  refine ⟨56862100963921273133389525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75816134618561697511186033 56862100963921273133389525)
                  ·
                    refine ⟨1332705491341904839063817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56862100963921273133389525 1332705491341904839063817)
                    ·
                      rfl

theorem cell22_3893152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_3893152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893152 prefixEnd_3893152 := by exact prefixLift 3893152
  have htrace : WordTrace (prefixWord ++ tailWord_3893152) baseStart_3893152 baseEnd_3893152 := by
    simpa [prefixWord, tailWord_3893152, baseEnd_3893152] using wordTrace_append hprefix tailTrace_3893152
  have hstable : (prefixWord ++ tailWord_3893152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893152).length < 2 ^ (prefixWord ++ tailWord_3893152).sum := by decide
  have hdescent : baseEnd_3893152 < baseStart_3893152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893167 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_3893167 : Nat := 118140960795 + 3893167 * 2 ^ 59
def prefixEnd_3893167 : Nat := 4983230072969 + 3 ^ 40 * 3893167 * 2
def baseEnd_3893167 : Nat := 1332710626148449799938771

theorem tailTrace_3893167 : CollatzResearch.WordTrace tailWord_3893167 prefixEnd_3893167 1332710626148449799938771 := by
  unfold tailWord_3893167
  simp only [CollatzResearch.WordTrace]
  refine ⟨141995465886728333833317755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94663643924485555888878503 141995465886728333833317755)
  ·
    refine ⟨212993198830092500749976633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141995465886728333833317755 212993198830092500749976633)
    ·
      refine ⟨159744899122569375562482475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212993198830092500749976633 159744899122569375562482475)
      ·
        refine ⟨239617348683854063343723713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159744899122569375562482475 239617348683854063343723713)
        ·
          refine ⟨179713011512890547507792785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239617348683854063343723713 179713011512890547507792785)
          ·
            refine ⟨134784758634667910630844589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179713011512890547507792785 134784758634667910630844589)
            ·
              refine ⟨50544284488000466486566721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134784758634667910630844589 50544284488000466486566721)
              ·
                refine ⟨37908213366000349864925041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50544284488000466486566721 37908213366000349864925041)
                ·
                  refine ⟨28431160024500262398693781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37908213366000349864925041 28431160024500262398693781)
                  ·
                    refine ⟨1332710626148449799938771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28431160024500262398693781 1332710626148449799938771)
                    ·
                      rfl

theorem cell22_3893167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_3893167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893167 prefixEnd_3893167 := by exact prefixLift 3893167
  have htrace : WordTrace (prefixWord ++ tailWord_3893167) baseStart_3893167 baseEnd_3893167 := by
    simpa [prefixWord, tailWord_3893167, baseEnd_3893167] using wordTrace_append hprefix tailTrace_3893167
  have hstable : (prefixWord ++ tailWord_3893167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893167).length < 2 ^ (prefixWord ++ tailWord_3893167).sum := by decide
  have hdescent : baseEnd_3893167 < baseStart_3893167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893319 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_3893319 : Nat := 118140960795 + 3893319 * 2 ^ 59
def prefixEnd_3893319 : Nat := 4983230072969 + 3 ^ 40 * 3893319 * 2
def baseEnd_3893319 : Nat := 1332762658854772070138305

theorem tailTrace_3893319 : CollatzResearch.WordTrace tailWord_3893319 prefixEnd_3893319 1332762658854772070138305 := by
  unfold tailWord_3893319
  simp only [CollatzResearch.WordTrace]
  refine ⟨142001009782177663792851011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94667339854785109195234007 142001009782177663792851011)
  ·
    refine ⟨213001514673266495689276517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142001009782177663792851011 213001514673266495689276517)
    ·
      refine ⟨39937784001237467941739347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213001514673266495689276517 39937784001237467941739347)
      ·
        refine ⟨59906676001856201912609021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39937784001237467941739347 59906676001856201912609021)
        ·
          refine ⟨22465003500696075717228383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59906676001856201912609021 22465003500696075717228383)
          ·
            refine ⟨33697505251044113575842575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22465003500696075717228383 33697505251044113575842575)
            ·
              refine ⟨50546257876566170363763863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33697505251044113575842575 50546257876566170363763863)
              ·
                refine ⟨75819386814849255545645795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50546257876566170363763863 75819386814849255545645795)
                ·
                  refine ⟨113729080222273883318468693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75819386814849255545645795 113729080222273883318468693)
                  ·
                    refine ⟨1332762658854772070138305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113729080222273883318468693 1332762658854772070138305)
                    ·
                      rfl

theorem cell22_3893319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_3893319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893319 prefixEnd_3893319 := by exact prefixLift 3893319
  have htrace : WordTrace (prefixWord ++ tailWord_3893319) baseStart_3893319 baseEnd_3893319 := by
    simpa [prefixWord, tailWord_3893319, baseEnd_3893319] using wordTrace_append hprefix tailTrace_3893319
  have hstable : (prefixWord ++ tailWord_3893319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893319).length < 2 ^ (prefixWord ++ tailWord_3893319).sum := by decide
  have hdescent : baseEnd_3893319 < baseStart_3893319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893321 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_3893321 : Nat := 118140960795 + 3893321 * 2 ^ 59
def prefixEnd_3893321 : Nat := 4983230072969 + 3 ^ 40 * 3893321 * 2
def baseEnd_3893321 : Nat := 1332763343495644731588299

theorem tailTrace_3893321 : CollatzResearch.WordTrace tailWord_3893321 prefixEnd_3893321 1332763343495644731588299 := by
  unfold tailWord_3893321
  simp only [CollatzResearch.WordTrace]
  refine ⟨142001082728170418134423817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94667388485446945422949211 142001082728170418134423817)
  ·
    refine ⟨106500812046127813600817863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142001082728170418134423817 106500812046127813600817863)
    ·
      refine ⟨159751218069191720401226795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106500812046127813600817863 159751218069191720401226795)
      ·
        refine ⟨239626827103787580601840193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159751218069191720401226795 239626827103787580601840193)
        ·
          refine ⟨179720120327840685451380145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 239626827103787580601840193 179720120327840685451380145)
          ·
            refine ⟨134790090245880514088535109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179720120327840685451380145 134790090245880514088535109)
            ·
              refine ⟨25273141921102596391600333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134790090245880514088535109 25273141921102596391600333)
              ·
                refine ⟨9477428220413473646850125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25273141921102596391600333 9477428220413473646850125)
                ·
                  refine ⟨3554035582655052617568797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9477428220413473646850125 3554035582655052617568797)
                  ·
                    refine ⟨1332763343495644731588299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554035582655052617568797 1332763343495644731588299)
                    ·
                      rfl

theorem cell22_3893321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_3893321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893321 prefixEnd_3893321 := by exact prefixLift 3893321
  have htrace : WordTrace (prefixWord ++ tailWord_3893321) baseStart_3893321 baseEnd_3893321 := by
    simpa [prefixWord, tailWord_3893321, baseEnd_3893321] using wordTrace_append hprefix tailTrace_3893321
  have hstable : (prefixWord ++ tailWord_3893321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893321).length < 2 ^ (prefixWord ++ tailWord_3893321).sum := by decide
  have hdescent : baseEnd_3893321 < baseStart_3893321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893406 : List Nat := [4, 3, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3893406 : Nat := 118140960795 + 3893406 * 2 ^ 59
def prefixEnd_3893406 : Nat := 4983230072969 + 3 ^ 40 * 3893406 * 2
def baseEnd_3893406 : Nat := 1332792440732732843213039

theorem tailTrace_3893406 : CollatzResearch.WordTrace tailWord_3893406 prefixEnd_3893406 1332792440732732843213039 := by
  unfold tailWord_3893406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17750522866607809706408509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94669455288574985100845381 17750522866607809706408509)
  ·
    refine ⟨6656446074977928639903191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17750522866607809706408509 6656446074977928639903191)
    ·
      refine ⟨9984669112466892959854787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6656446074977928639903191 9984669112466892959854787)
      ·
        refine ⟨14977003668700339439782181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9984669112466892959854787 14977003668700339439782181)
        ·
          refine ⟨2808188187881313644959159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14977003668700339439782181 2808188187881313644959159)
          ·
            refine ⟨4212282281821970467438739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808188187881313644959159 4212282281821970467438739)
            ·
              refine ⟨6318423422732955701158109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4212282281821970467438739 6318423422732955701158109)
              ·
                refine ⟨2369408783524858387934291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6318423422732955701158109 2369408783524858387934291)
                ·
                  refine ⟨3554113175287287581901437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369408783524858387934291 3554113175287287581901437)
                  ·
                    refine ⟨1332792440732732843213039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554113175287287581901437 1332792440732732843213039)
                    ·
                      rfl

theorem cell22_3893406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3893406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893406 prefixEnd_3893406 := by exact prefixLift 3893406
  have htrace : WordTrace (prefixWord ++ tailWord_3893406) baseStart_3893406 baseEnd_3893406 := by
    simpa [prefixWord, tailWord_3893406, baseEnd_3893406] using wordTrace_append hprefix tailTrace_3893406
  have hstable : (prefixWord ++ tailWord_3893406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893406).length < 2 ^ (prefixWord ++ tailWord_3893406).sum := by decide
  have hdescent : baseEnd_3893406 < baseStart_3893406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893445 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_3893445 : Nat := 118140960795 + 3893445 * 2 ^ 59
def prefixEnd_3893445 : Nat := 4983230072969 + 3 ^ 40 * 3893445 * 2
def baseEnd_3893445 : Nat := 1332805791229749741487919

theorem tailTrace_3893445 : CollatzResearch.WordTrace tailWord_3893445 prefixEnd_3893445 1332805791229749741487919 := by
  unfold tailWord_3893445
  simp only [CollatzResearch.WordTrace]
  refine ⟨142005605379721187311937789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94670403586480791541291859 142005605379721187311937789)
  ·
    refine ⟨53252102017395445241976671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142005605379721187311937789 53252102017395445241976671)
    ·
      refine ⟨79878153026093167862965007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53252102017395445241976671 79878153026093167862965007)
      ·
        refine ⟨119817229539139751794447511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79878153026093167862965007 119817229539139751794447511)
        ·
          refine ⟨179725844308709627691671267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119817229539139751794447511 179725844308709627691671267)
          ·
            refine ⟨269588766463064441537506901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179725844308709627691671267 269588766463064441537506901)
            ·
              refine ⟨3159243356989036424267659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 269588766463064441537506901 3159243356989036424267659)
              ·
                refine ⟨4738865035483554636401489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159243356989036424267659 4738865035483554636401489)
                ·
                  refine ⟨3554148776612665977301117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4738865035483554636401489 3554148776612665977301117)
                  ·
                    refine ⟨1332805791229749741487919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554148776612665977301117 1332805791229749741487919)
                    ·
                      rfl

theorem cell22_3893445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_3893445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893445 prefixEnd_3893445 := by exact prefixLift 3893445
  have htrace : WordTrace (prefixWord ++ tailWord_3893445) baseStart_3893445 baseEnd_3893445 := by
    simpa [prefixWord, tailWord_3893445, baseEnd_3893445] using wordTrace_append hprefix tailTrace_3893445
  have hstable : (prefixWord ++ tailWord_3893445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893445).length < 2 ^ (prefixWord ++ tailWord_3893445).sum := by decide
  have hdescent : baseEnd_3893445 < baseStart_3893445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893610 : List Nat := [3, 1, 3, 3, 1, 2, 2, 7]
def baseStart_3893610 : Nat := 118140960795 + 3893610 * 2 ^ 59
def prefixEnd_3893610 : Nat := 4983230072969 + 3 ^ 40 * 3893610 * 2
def baseEnd_3893610 : Nat := 148095808233527145679157

theorem tailTrace_3893610 : CollatzResearch.WordTrace tailWord_3893610 prefixEnd_3893610 148095808233527145679157 := by
  unfold tailWord_3893610
  simp only [CollatzResearch.WordTrace]
  refine ⟨35502905856030855122923571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94674415616082280327796189 35502905856030855122923571)
  ·
    refine ⟨53254358784046282684385357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35502905856030855122923571 53254358784046282684385357)
    ·
      refine ⟨19970384544017356006644509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53254358784046282684385357 19970384544017356006644509)
      ·
        refine ⟨7488894204006508502491691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19970384544017356006644509 7488894204006508502491691)
        ·
          refine ⟨11233341306009762753737537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7488894204006508502491691 11233341306009762753737537)
          ·
            refine ⟨8425005979507322065303153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11233341306009762753737537 8425005979507322065303153)
            ·
              refine ⟨6318754484630491548977365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8425005979507322065303153 6318754484630491548977365)
              ·
                refine ⟨148095808233527145679157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6318754484630491548977365 148095808233527145679157)
                ·
                  rfl

theorem cell22_3893610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_3893610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893610 prefixEnd_3893610 := by exact prefixLift 3893610
  have htrace : WordTrace (prefixWord ++ tailWord_3893610) baseStart_3893610 baseEnd_3893610 := by
    simpa [prefixWord, tailWord_3893610, baseEnd_3893610] using wordTrace_append hprefix tailTrace_3893610
  have hstable : (prefixWord ++ tailWord_3893610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893610).length < 2 ^ (prefixWord ++ tailWord_3893610).sum := by decide
  have hdescent : baseEnd_3893610 < baseStart_3893610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893653 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3893653 : Nat := 118140960795 + 3893653 * 2 ^ 59
def prefixEnd_3893653 : Nat := 4983230072969 + 3 ^ 40 * 3893653 * 2
def baseEnd_3893653 : Nat := 1332876993880506532287281

theorem tailTrace_3893653 : CollatzResearch.WordTrace tailWord_3893653 prefixEnd_3893653 1332876993880506532287281 := by
  unfold tailWord_3893653
  simp only [CollatzResearch.WordTrace]
  refine ⟨142013191762967638835509613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94675461175311759223673075 142013191762967638835509613)
  ·
    refine ⟨53254946911112864563316105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142013191762967638835509613 53254946911112864563316105)
    ·
      refine ⟨39941210183334648422487079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53254946911112864563316105 39941210183334648422487079)
      ·
        refine ⟨59911815275001972633730619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39941210183334648422487079 59911815275001972633730619)
        ·
          refine ⟨89867722912502958950595929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59911815275001972633730619 89867722912502958950595929)
          ·
            refine ⟨67400792184377219212946947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89867722912502958950595929 67400792184377219212946947)
            ·
              refine ⟨101101188276565828819420421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67400792184377219212946947 101101188276565828819420421)
              ·
                refine ⟨18956472801856092903641329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101101188276565828819420421 18956472801856092903641329)
                ·
                  refine ⟨14217354601392069677730997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18956472801856092903641329 14217354601392069677730997)
                  ·
                    refine ⟨1332876993880506532287281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14217354601392069677730997 1332876993880506532287281)
                    ·
                      rfl

theorem cell22_3893653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3893653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893653 prefixEnd_3893653 := by exact prefixLift 3893653
  have htrace : WordTrace (prefixWord ++ tailWord_3893653) baseStart_3893653 baseEnd_3893653 := by
    simpa [prefixWord, tailWord_3893653, baseEnd_3893653] using wordTrace_append hprefix tailTrace_3893653
  have hstable : (prefixWord ++ tailWord_3893653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893653).length < 2 ^ (prefixWord ++ tailWord_3893653).sum := by decide
  have hdescent : baseEnd_3893653 < baseStart_3893653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893672 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_3893672 : Nat := 118140960795 + 3893672 * 2 ^ 59
def prefixEnd_3893672 : Nat := 4983230072969 + 3 ^ 40 * 3893672 * 2
def baseEnd_3893672 : Nat := 444294499322932272020741

theorem tailTrace_3893672 : CollatzResearch.WordTrace tailWord_3893672 prefixEnd_3893672 444294499322932272020741 := by
  unfold tailWord_3893672
  simp only [CollatzResearch.WordTrace]
  refine ⟨71006942374949402540225635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94675923166599203386967513 71006942374949402540225635)
  ·
    refine ⟨106510413562424103810338453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71006942374949402540225635 106510413562424103810338453)
    ·
      refine ⟨4992675635738629866109615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106510413562424103810338453 4992675635738629866109615)
      ·
        refine ⟨7489013453607944799164423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4992675635738629866109615 7489013453607944799164423)
        ·
          refine ⟨11233520180411917198746635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489013453607944799164423 11233520180411917198746635)
          ·
            refine ⟨16850280270617875798119953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11233520180411917198746635 16850280270617875798119953)
            ·
              refine ⟨12637710202963406848589965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16850280270617875798119953 12637710202963406848589965)
              ·
                refine ⟨4739141326111277568221237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12637710202963406848589965 4739141326111277568221237)
                ·
                  refine ⟨444294499322932272020741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4739141326111277568221237 444294499322932272020741)
                  ·
                    rfl

theorem cell22_3893672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_3893672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893672 prefixEnd_3893672 := by exact prefixLift 3893672
  have htrace : WordTrace (prefixWord ++ tailWord_3893672) baseStart_3893672 baseEnd_3893672 := by
    simpa [prefixWord, tailWord_3893672, baseEnd_3893672] using wordTrace_append hprefix tailTrace_3893672
  have hstable : (prefixWord ++ tailWord_3893672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893672).length < 2 ^ (prefixWord ++ tailWord_3893672).sum := by decide
  have hdescent : baseEnd_3893672 < baseStart_3893672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893717 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 4]
def baseStart_3893717 : Nat := 118140960795 + 3893717 * 2 ^ 59
def prefixEnd_3893717 : Nat := 4983230072969 + 3 ^ 40 * 3893717 * 2
def baseEnd_3893717 : Nat := 444299634129477232895695

theorem tailTrace_3893717 : CollatzResearch.WordTrace tailWord_3893717 prefixEnd_3893717 444299634129477232895695 := by
  unfold tailWord_3893717
  simp only [CollatzResearch.WordTrace]
  refine ⟨142015526034735777765839405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94677017356490518510559603 142015526034735777765839405)
  ·
    refine ⟨53255822263025916662189777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142015526034735777765839405 53255822263025916662189777)
    ·
      refine ⟨39941866697269437496642333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53255822263025916662189777 39941866697269437496642333)
      ·
        refine ⟨14978200011476039061240875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39941866697269437496642333 14978200011476039061240875)
        ·
          refine ⟨22467300017214058591861313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14978200011476039061240875 22467300017214058591861313)
          ·
            refine ⟨16850475012910543943895985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22467300017214058591861313 16850475012910543943895985)
            ·
              refine ⟨12637856259682907957921989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16850475012910543943895985 12637856259682907957921989)
              ·
                refine ⟨2369598048690545242110373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12637856259682907957921989 2369598048690545242110373)
                ·
                  refine ⟨444299634129477232895695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369598048690545242110373 444299634129477232895695)
                  ·
                    rfl

theorem cell22_3893717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_3893717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893717 prefixEnd_3893717 := by exact prefixLift 3893717
  have htrace : WordTrace (prefixWord ++ tailWord_3893717) baseStart_3893717 baseEnd_3893717 := by
    simpa [prefixWord, tailWord_3893717, baseEnd_3893717] using wordTrace_append hprefix tailTrace_3893717
  have hstable : (prefixWord ++ tailWord_3893717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893717).length < 2 ^ (prefixWord ++ tailWord_3893717).sum := by decide
  have hdescent : baseEnd_3893717 < baseStart_3893717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893728 : List Nat := [2, 1, 1, 3, 1, 1, 4, 9]
def baseStart_3893728 : Nat := 118140960795 + 3893728 * 2 ^ 59
def prefixEnd_3893728 : Nat := 4983230072969 + 3 ^ 40 * 3893728 * 2
def baseEnd_3893728 : Nat := 148100296434803481851339

theorem tailTrace_3893728 : CollatzResearch.WordTrace tailWord_3893728 prefixEnd_3893728 148100296434803481851339 := by
  unfold tailWord_3893728
  simp only [CollatzResearch.WordTrace]
  refine ⟨71007963618847963322244919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94677284825130617762993225 71007963618847963322244919)
  ·
    refine ⟨106511945428271944983367379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71007963618847963322244919 106511945428271944983367379)
    ·
      refine ⟨159767918142407917475051069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106511945428271944983367379 159767918142407917475051069)
      ·
        refine ⟨59912969303402969053144151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159767918142407917475051069 59912969303402969053144151)
        ·
          refine ⟨89869453955104453579716227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59912969303402969053144151 89869453955104453579716227)
          ·
            refine ⟨134804180932656680369574341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89869453955104453579716227 134804180932656680369574341)
            ·
              refine ⟨25275783924873127569295189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134804180932656680369574341 25275783924873127569295189)
              ·
                refine ⟨148100296434803481851339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25275783924873127569295189 148100296434803481851339)
                ·
                  rfl

theorem cell22_3893728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 9].length) (baseStart_3893728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893728 prefixEnd_3893728 := by exact prefixLift 3893728
  have htrace : WordTrace (prefixWord ++ tailWord_3893728) baseStart_3893728 baseEnd_3893728 := by
    simpa [prefixWord, tailWord_3893728, baseEnd_3893728] using wordTrace_append hprefix tailTrace_3893728
  have hstable : (prefixWord ++ tailWord_3893728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893728).length < 2 ^ (prefixWord ++ tailWord_3893728).sum := by decide
  have hdescent : baseEnd_3893728 < baseStart_3893728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893743 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_3893743 : Nat := 118140960795 + 3893743 * 2 ^ 59
def prefixEnd_3893743 : Nat := 4983230072969 + 3 ^ 40 * 3893743 * 2
def baseEnd_3893743 : Nat := 1332907802719776297537005

theorem tailTrace_3893743 : CollatzResearch.WordTrace tailWord_3893743 prefixEnd_3893743 1332907802719776297537005 := by
  unfold tailWord_3893743
  simp only [CollatzResearch.WordTrace]
  refine ⟨142016474332641584206285883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94677649555094389470857255 142016474332641584206285883)
  ·
    refine ⟨213024711498962376309428825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142016474332641584206285883 213024711498962376309428825)
    ·
      refine ⟨159768533624221782232071619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213024711498962376309428825 159768533624221782232071619)
      ·
        refine ⟨239652800436332673348107429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159768533624221782232071619 239652800436332673348107429)
        ·
          refine ⟨44934900081812376252770143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 239652800436332673348107429 44934900081812376252770143)
          ·
            refine ⟨67402350122718564379155215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44934900081812376252770143 67402350122718564379155215)
            ·
              refine ⟨101103525184077846568732823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67402350122718564379155215 101103525184077846568732823)
              ·
                refine ⟨151655287776116769853099235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101103525184077846568732823 151655287776116769853099235)
                ·
                  refine ⟨227482931664175154779648853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151655287776116769853099235 227482931664175154779648853)
                  ·
                    refine ⟨1332907802719776297537005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227482931664175154779648853 1332907802719776297537005)
                    ·
                      rfl

theorem cell22_3893743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_3893743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893743 prefixEnd_3893743 := by exact prefixLift 3893743
  have htrace : WordTrace (prefixWord ++ tailWord_3893743) baseStart_3893743 baseEnd_3893743 := by
    simpa [prefixWord, tailWord_3893743, baseEnd_3893743] using wordTrace_append hprefix tailTrace_3893743
  have hstable : (prefixWord ++ tailWord_3893743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893743).length < 2 ^ (prefixWord ++ tailWord_3893743).sum := by decide
  have hdescent : baseEnd_3893743 < baseStart_3893743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893783 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 2, 3]
def baseStart_3893783 : Nat := 118140960795 + 3893783 * 2 ^ 59
def prefixEnd_3893783 : Nat := 4983230072969 + 3 ^ 40 * 3893783 * 2
def baseEnd_3893783 : Nat := 1332921495537229526536883

theorem tailTrace_3893783 : CollatzResearch.WordTrace tailWord_3893783 prefixEnd_3893783 1332921495537229526536883 := by
  unfold tailWord_3893783
  simp only [CollatzResearch.WordTrace]
  refine ⟨142017933252496671037742003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94678622168331114025161335 142017933252496671037742003)
  ·
    refine ⟨213026899878745006556613005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142017933252496671037742003 213026899878745006556613005)
    ·
      refine ⟨79885087454529377458729877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213026899878745006556613005 79885087454529377458729877)
      ·
        refine ⟨3744613474431064568377963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79885087454529377458729877 3744613474431064568377963)
        ·
          refine ⟨5616920211646596852566945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744613474431064568377963 5616920211646596852566945)
          ·
            refine ⟨4212690158734947639425209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5616920211646596852566945 4212690158734947639425209)
            ·
              refine ⟨3159517619051210729568907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4212690158734947639425209 3159517619051210729568907)
              ·
                refine ⟨4739276428576816094353361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3159517619051210729568907 4739276428576816094353361)
                ·
                  refine ⟨3554457321432612070765021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739276428576816094353361 3554457321432612070765021)
                  ·
                    refine ⟨1332921495537229526536883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554457321432612070765021 1332921495537229526536883)
                    ·
                      rfl

theorem cell22_3893783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_3893783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893783 prefixEnd_3893783 := by exact prefixLift 3893783
  have htrace : WordTrace (prefixWord ++ tailWord_3893783) baseStart_3893783 baseEnd_3893783 := by
    simpa [prefixWord, tailWord_3893783, baseEnd_3893783] using wordTrace_append hprefix tailTrace_3893783
  have hstable : (prefixWord ++ tailWord_3893783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893783).length < 2 ^ (prefixWord ++ tailWord_3893783).sum := by decide
  have hdescent : baseEnd_3893783 < baseStart_3893783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893869 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 4]
def baseStart_3893869 : Nat := 118140960795 + 3893869 * 2 ^ 59
def prefixEnd_3893869 : Nat := 4983230072969 + 3 ^ 40 * 3893869 * 2
def baseEnd_3893869 : Nat := 444316978364917989628873

theorem tailTrace_3893869 : CollatzResearch.WordTrace tailWord_3893869 prefixEnd_3893869 444316978364917989628873 := by
  unfold tailWord_3893869
  simp only [CollatzResearch.WordTrace]
  refine ⟨142021069930185107725372661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94680713286790071816915107 142021069930185107725372661)
  ·
    refine ⟨13314475305954853849253687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142021069930185107725372661 13314475305954853849253687)
    ·
      refine ⟨19971712958932280773880531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13314475305954853849253687 19971712958932280773880531)
      ·
        refine ⟨29957569438398421160820797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19971712958932280773880531 29957569438398421160820797)
        ·
          refine ⟨11234088539399407935307799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29957569438398421160820797 11234088539399407935307799)
          ·
            refine ⟨16851132809099111902961699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11234088539399407935307799 16851132809099111902961699)
            ·
              refine ⟨25276699213648667854442549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16851132809099111902961699 25276699213648667854442549)
              ·
                refine ⟨2369690551279562611353989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25276699213648667854442549 2369690551279562611353989)
                ·
                  refine ⟨444316978364917989628873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369690551279562611353989 444316978364917989628873)
                  ·
                    rfl

theorem cell22_3893869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_3893869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893869 prefixEnd_3893869 := by exact prefixLift 3893869
  have htrace : WordTrace (prefixWord ++ tailWord_3893869) baseStart_3893869 baseEnd_3893869 := by
    simpa [prefixWord, tailWord_3893869, baseEnd_3893869] using wordTrace_append hprefix tailTrace_3893869
  have hstable : (prefixWord ++ tailWord_3893869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893869).length < 2 ^ (prefixWord ++ tailWord_3893869).sum := by decide
  have hdescent : baseEnd_3893869 < baseStart_3893869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893884 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 2, 3]
def baseStart_3893884 : Nat := 118140960795 + 3893884 * 2 ^ 59
def prefixEnd_3893884 : Nat := 4983230072969 + 3 ^ 40 * 3893884 * 2
def baseEnd_3893884 : Nat := 1332956069901298929761573

theorem tailTrace_3893884 : CollatzResearch.WordTrace tailWord_3893884 prefixEnd_3893884 1332956069901298929761573 := by
  unfold tailWord_3893884
  simp only [CollatzResearch.WordTrace]
  refine ⟨71010808512565382643584353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94681078016753843524779137 71010808512565382643584353)
  ·
    refine ⟨53258106384424036982688265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71010808512565382643584353 53258106384424036982688265)
    ·
      refine ⟨39943579788318027737016199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53258106384424036982688265 39943579788318027737016199)
      ·
        refine ⟨59915369682477041605524299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39943579788318027737016199 59915369682477041605524299)
        ·
          refine ⟨89873054523715562408286449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59915369682477041605524299 89873054523715562408286449)
          ·
            refine ⟨67404790892786671806214837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89873054523715562408286449 67404790892786671806214837)
            ·
              refine ⟨6319199146198750481832641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67404790892786671806214837 6319199146198750481832641)
              ·
                refine ⟨4739399359649062861374481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319199146198750481832641 4739399359649062861374481)
                ·
                  refine ⟨3554549519736797146030861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4739399359649062861374481 3554549519736797146030861)
                  ·
                    refine ⟨1332956069901298929761573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554549519736797146030861 1332956069901298929761573)
                    ·
                      rfl

theorem cell22_3893884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_3893884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893884 prefixEnd_3893884 := by exact prefixLift 3893884
  have htrace : WordTrace (prefixWord ++ tailWord_3893884) baseStart_3893884 baseEnd_3893884 := by
    simpa [prefixWord, tailWord_3893884, baseEnd_3893884] using wordTrace_append hprefix tailTrace_3893884
  have hstable : (prefixWord ++ tailWord_3893884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893884).length < 2 ^ (prefixWord ++ tailWord_3893884).sum := by decide
  have hdescent : baseEnd_3893884 < baseStart_3893884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3893914 : List Nat := [3, 1, 1, 6, 1, 1, 1, 8]
def baseStart_3893914 : Nat := 118140960795 + 3893914 * 2 ^ 59
def prefixEnd_3893914 : Nat := 4983230072969 + 3 ^ 40 * 3893914 * 2
def baseEnd_3893914 : Nat := 148107371057154316834609

theorem tailTrace_3893914 : CollatzResearch.WordTrace tailWord_3893914 prefixEnd_3893914 148107371057154316834609 := by
  unfold tailWord_3893914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35505677803755520102690199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94681807476681386940507197 35505677803755520102690199)
  ·
    refine ⟨53258516705633280154035299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35505677803755520102690199 53258516705633280154035299)
    ·
      refine ⟨79887775058449920231052949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53258516705633280154035299 79887775058449920231052949)
      ·
        refine ⟨3744739455864840010830607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79887775058449920231052949 3744739455864840010830607)
        ·
          refine ⟨5617109183797260016245911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3744739455864840010830607 5617109183797260016245911)
          ·
            refine ⟨8425663775695890024368867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617109183797260016245911 8425663775695890024368867)
            ·
              refine ⟨12638495663543835036553301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8425663775695890024368867 12638495663543835036553301)
              ·
                refine ⟨148107371057154316834609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12638495663543835036553301 148107371057154316834609)
                ·
                  rfl

theorem cell22_3893914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_3893914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3893914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3893914 prefixEnd_3893914 := by exact prefixLift 3893914
  have htrace : WordTrace (prefixWord ++ tailWord_3893914) baseStart_3893914 baseEnd_3893914 := by
    simpa [prefixWord, tailWord_3893914, baseEnd_3893914] using wordTrace_append hprefix tailTrace_3893914
  have hstable : (prefixWord ++ tailWord_3893914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3893914).length < 2 ^ (prefixWord ++ tailWord_3893914).sum := by decide
  have hdescent : baseEnd_3893914 < baseStart_3893914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3893914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894017 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3894017 : Nat := 118140960795 + 3894017 * 2 ^ 59
def prefixEnd_3894017 : Nat := 4983230072969 + 3 ^ 40 * 3894017 * 2
def baseEnd_3894017 : Nat := 1333001598519330916186165

theorem tailTrace_3894017 : CollatzResearch.WordTrace tailWord_3894017 prefixEnd_3894017 1333001598519330916186165 := by
  unfold tailWord_3894017
  simp only [CollatzResearch.WordTrace]
  refine ⟨142026467933648929001760305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94684311955765952667840203 142026467933648929001760305)
  ·
    refine ⟨106519850950236696751320229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142026467933648929001760305 106519850950236696751320229)
    ·
      refine ⟨19972472053169380640872543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106519850950236696751320229 19972472053169380640872543)
      ·
        refine ⟨29958708079754070961308815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19972472053169380640872543 29958708079754070961308815)
        ·
          refine ⟨44938062119631106441963223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29958708079754070961308815 44938062119631106441963223)
          ·
            refine ⟨67407093179446659662944835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44938062119631106441963223 67407093179446659662944835)
            ·
              refine ⟨101110639769169989494417253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67407093179446659662944835 101110639769169989494417253)
              ·
                refine ⟨18958244956719373030203235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101110639769169989494417253 18958244956719373030203235)
                ·
                  refine ⟨28437367435079059545304853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18958244956719373030203235 28437367435079059545304853)
                  ·
                    refine ⟨1333001598519330916186165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28437367435079059545304853 1333001598519330916186165)
                    ·
                      rfl

theorem cell22_3894017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3894017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894017 prefixEnd_3894017 := by exact prefixLift 3894017
  have htrace : WordTrace (prefixWord ++ tailWord_3894017) baseStart_3894017 baseEnd_3894017 := by
    simpa [prefixWord, tailWord_3894017, baseEnd_3894017] using wordTrace_append hprefix tailTrace_3894017
  have hstable : (prefixWord ++ tailWord_3894017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894017).length < 2 ^ (prefixWord ++ tailWord_3894017).sum := by decide
  have hdescent : baseEnd_3894017 < baseStart_3894017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894070 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3894070 : Nat := 118140960795 + 3894070 * 2 ^ 59
def prefixEnd_3894070 : Nat := 4983230072969 + 3 ^ 40 * 3894070 * 2
def baseEnd_3894070 : Nat := 1333019741502456444611003

theorem tailTrace_3894070 : CollatzResearch.WordTrace tailWord_3894070 prefixEnd_3894070 1333019741502456444611003 := by
  unfold tailWord_3894070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876775062653557440839979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94685600668304612702293109 8876775062653557440839979)
  ·
    refine ⟨13315162593980336161259969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8876775062653557440839979 13315162593980336161259969)
    ·
      refine ⟨9986371945485252120944977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13315162593980336161259969 9986371945485252120944977)
      ·
        refine ⟨7489778959113939090708733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9986371945485252120944977 7489778959113939090708733)
        ·
          refine ⟨2808667109667727159015775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7489778959113939090708733 2808667109667727159015775)
          ·
            refine ⟨4213000664501590738523663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2808667109667727159015775 4213000664501590738523663)
            ·
              refine ⟨6319500996752386107785495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213000664501590738523663 6319500996752386107785495)
              ·
                refine ⟨9479251495128579161678243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319500996752386107785495 9479251495128579161678243)
                ·
                  refine ⟨14218877242692868742517365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9479251495128579161678243 14218877242692868742517365)
                  ·
                    refine ⟨1333019741502456444611003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14218877242692868742517365 1333019741502456444611003)
                    ·
                      rfl

theorem cell22_3894070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3894070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894070 prefixEnd_3894070 := by exact prefixLift 3894070
  have htrace : WordTrace (prefixWord ++ tailWord_3894070) baseStart_3894070 baseEnd_3894070 := by
    simpa [prefixWord, tailWord_3894070, baseEnd_3894070] using wordTrace_append hprefix tailTrace_3894070
  have hstable : (prefixWord ++ tailWord_3894070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894070).length < 2 ^ (prefixWord ++ tailWord_3894070).sum := by decide
  have hdescent : baseEnd_3894070 < baseStart_3894070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894115 : List Nat := [1, 1, 1, 5, 3, 2, 3, 2, 1, 3]
def baseStart_3894115 : Nat := 118140960795 + 3894115 * 2 ^ 59
def prefixEnd_3894115 : Nat := 4983230072969 + 3 ^ 40 * 3894115 * 2
def baseEnd_3894115 : Nat := 1333035145922091327235865

theorem tailTrace_3894115 : CollatzResearch.WordTrace tailWord_3894115 prefixEnd_3894115 1333035145922091327235865 := by
  unfold tailWord_3894115
  simp only [CollatzResearch.WordTrace]
  refine ⟨142030042287293891738827799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94686694858195927825885199 142030042287293891738827799)
  ·
    refine ⟨213045063430940837608241699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142030042287293891738827799 213045063430940837608241699)
    ·
      refine ⟨319567595146411256412362549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213045063430940837608241699 319567595146411256412362549)
      ·
        refine ⟨29959462044976055288658989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 319567595146411256412362549 29959462044976055288658989)
        ·
          refine ⟨11234798266866020733247121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29959462044976055288658989 11234798266866020733247121)
          ·
            refine ⟨8426098700149515549935341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11234798266866020733247121 8426098700149515549935341)
            ·
              refine ⟨3159787012556068331225753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8426098700149515549935341 3159787012556068331225753)
              ·
                refine ⟨2369840259417051248419315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159787012556068331225753 2369840259417051248419315)
                ·
                  refine ⟨3554760389125576872628973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369840259417051248419315 3554760389125576872628973)
                  ·
                    refine ⟨1333035145922091327235865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554760389125576872628973 1333035145922091327235865)
                    ·
                      rfl

theorem cell22_3894115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 2, 1, 3].length) (baseStart_3894115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894115 prefixEnd_3894115 := by exact prefixLift 3894115
  have htrace : WordTrace (prefixWord ++ tailWord_3894115) baseStart_3894115 baseEnd_3894115 := by
    simpa [prefixWord, tailWord_3894115, baseEnd_3894115] using wordTrace_append hprefix tailTrace_3894115
  have hstable : (prefixWord ++ tailWord_3894115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894115).length < 2 ^ (prefixWord ++ tailWord_3894115).sum := by decide
  have hdescent : baseEnd_3894115 < baseStart_3894115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894124 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_3894124 : Nat := 118140960795 + 3894124 * 2 ^ 59
def prefixEnd_3894124 : Nat := 4983230072969 + 3 ^ 40 * 3894124 * 2
def baseEnd_3894124 : Nat := 1333038226806018303760837

theorem tailTrace_3894124 : CollatzResearch.WordTrace tailWord_3894124 prefixEnd_3894124 1333038226806018303760837 := by
  unfold tailWord_3894124
  simp only [CollatzResearch.WordTrace]
  refine ⟨71015185272130643137952713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94686913696174190850603617 71015185272130643137952713)
  ·
    refine ⟨53261388954097982353464535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71015185272130643137952713 53261388954097982353464535)
    ·
      refine ⟨79892083431146973530196803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53261388954097982353464535 79892083431146973530196803)
      ·
        refine ⟨119838125146720460295295205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79892083431146973530196803 119838125146720460295295205)
        ·
          refine ⟨22469648465010086305367851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119838125146720460295295205 22469648465010086305367851)
          ·
            refine ⟨33704472697515129458051777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22469648465010086305367851 33704472697515129458051777)
            ·
              refine ⟨25278354523136347093538833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33704472697515129458051777 25278354523136347093538833)
              ·
                refine ⟨18958765892352260320154125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25278354523136347093538833 18958765892352260320154125)
                ·
                  refine ⟨7109537209632097620057797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18958765892352260320154125 7109537209632097620057797)
                  ·
                    refine ⟨1333038226806018303760837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7109537209632097620057797 1333038226806018303760837)
                    ·
                      rfl

theorem cell22_3894124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_3894124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894124 prefixEnd_3894124 := by exact prefixLift 3894124
  have htrace : WordTrace (prefixWord ++ tailWord_3894124) baseStart_3894124 baseEnd_3894124 := by
    simpa [prefixWord, tailWord_3894124, baseEnd_3894124] using wordTrace_append hprefix tailTrace_3894124
  have hstable : (prefixWord ++ tailWord_3894124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894124).length < 2 ^ (prefixWord ++ tailWord_3894124).sum := by decide
  have hdescent : baseEnd_3894124 < baseStart_3894124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894141 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3894141 : Nat := 118140960795 + 3894141 * 2 ^ 59
def prefixEnd_3894141 : Nat := 4983230072969 + 3 ^ 40 * 3894141 * 2
def baseEnd_3894141 : Nat := 1333044046253435926085785

theorem tailTrace_3894141 : CollatzResearch.WordTrace tailWord_3894141 prefixEnd_3894141 1333044046253435926085785 := by
  unfold tailWord_3894141
  simp only [CollatzResearch.WordTrace]
  refine ⟨142030990585199698179274277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94687327056799798786182851 142030990585199698179274277)
  ·
    refine ⟨26630810734724943408613927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142030990585199698179274277 26630810734724943408613927)
    ·
      refine ⟨39946216102087415112920891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26630810734724943408613927 39946216102087415112920891)
      ·
        refine ⟨59919324153131122669381337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39946216102087415112920891 59919324153131122669381337)
        ·
          refine ⟨44939493114848342002036003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59919324153131122669381337 44939493114848342002036003)
          ·
            refine ⟨67409239672272513003054005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44939493114848342002036003 67409239672272513003054005)
            ·
              refine ⟨6319616219275548094036313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67409239672272513003054005 6319616219275548094036313)
              ·
                refine ⟨4739712164456661070527235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6319616219275548094036313 4739712164456661070527235)
                ·
                  refine ⟨7109568246684991605790853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4739712164456661070527235 7109568246684991605790853)
                  ·
                    refine ⟨1333044046253435926085785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7109568246684991605790853 1333044046253435926085785)
                    ·
                      rfl

theorem cell22_3894141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3894141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894141 prefixEnd_3894141 := by exact prefixLift 3894141
  have htrace : WordTrace (prefixWord ++ tailWord_3894141) baseStart_3894141 baseEnd_3894141 := by
    simpa [prefixWord, tailWord_3894141, baseEnd_3894141] using wordTrace_append hprefix tailTrace_3894141
  have hstable : (prefixWord ++ tailWord_3894141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894141).length < 2 ^ (prefixWord ++ tailWord_3894141).sum := by decide
  have hdescent : baseEnd_3894141 < baseStart_3894141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894166 : List Nat := [5, 3, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3894166 : Nat := 118140960795 + 3894166 * 2 ^ 59
def prefixEnd_3894166 : Nat := 4983230072969 + 3 ^ 40 * 3894166 * 2
def baseEnd_3894166 : Nat := 1333052604264344194210709

theorem tailTrace_3894166 : CollatzResearch.WordTrace tailWord_3894166 prefixEnd_3894166 1333052604264344194210709 := by
  unfold tailWord_3894166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8876993900631820465558397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94687934940072751632622901 8876993900631820465558397)
  ·
    refine ⟨3328872712736932674584399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8876993900631820465558397 3328872712736932674584399)
    ·
      refine ⟨4993309069105399011876599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3328872712736932674584399 4993309069105399011876599)
      ·
        refine ⟨7489963603658098517814899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993309069105399011876599 7489963603658098517814899)
        ·
          refine ⟨11234945405487147776722349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7489963603658098517814899 11234945405487147776722349)
          ·
            refine ⟨4213104527057680416270881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11234945405487147776722349 4213104527057680416270881)
            ·
              refine ⟨3159828395293260312203161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213104527057680416270881 3159828395293260312203161)
              ·
                refine ⟨2369871296469945234152371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3159828395293260312203161 2369871296469945234152371)
                ·
                  refine ⟨3554806944704917851228557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2369871296469945234152371 3554806944704917851228557)
                  ·
                    refine ⟨1333052604264344194210709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554806944704917851228557 1333052604264344194210709)
                    ·
                      rfl

theorem cell22_3894166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3894166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894166 prefixEnd_3894166 := by exact prefixLift 3894166
  have htrace : WordTrace (prefixWord ++ tailWord_3894166) baseStart_3894166 baseEnd_3894166 := by
    simpa [prefixWord, tailWord_3894166, baseEnd_3894166] using wordTrace_append hprefix tailTrace_3894166
  have hstable : (prefixWord ++ tailWord_3894166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894166).length < 2 ^ (prefixWord ++ tailWord_3894166).sum := by decide
  have hdescent : baseEnd_3894166 < baseStart_3894166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894201 : List Nat := [1, 2, 1, 4, 2, 3, 3, 6]
def baseStart_3894201 : Nat := 118140960795 + 3894201 * 2 ^ 59
def prefixEnd_3894201 : Nat := 4983230072969 + 3 ^ 40 * 3894201 * 2
def baseEnd_3894201 : Nat := 148118287275512863287289

theorem tailTrace_3894201 : CollatzResearch.WordTrace tailWord_3894201 prefixEnd_3894201 148118287275512863287289 := by
  unfold tailWord_3894201
  simp only [CollatzResearch.WordTrace]
  refine ⟨142033178964982328426458457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94688785976654885617638971 142033178964982328426458457)
  ·
    refine ⟨106524884223736746319843843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142033178964982328426458457 106524884223736746319843843)
    ·
      refine ⟨159787326335605119479765765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106524884223736746319843843 159787326335605119479765765)
      ·
        refine ⟨29960123687925959902456081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159787326335605119479765765 29960123687925959902456081)
        ·
          refine ⟨22470092765944469926842061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29960123687925959902456081 22470092765944469926842061)
          ·
            refine ⟨8426284787229176222565773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22470092765944469926842061 8426284787229176222565773)
            ·
              refine ⟨3159856795210941083462165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8426284787229176222565773 3159856795210941083462165)
              ·
                refine ⟨148118287275512863287289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3159856795210941083462165 148118287275512863287289)
                ·
                  rfl

theorem cell22_3894201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 6].length) (baseStart_3894201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894201 prefixEnd_3894201 := by exact prefixLift 3894201
  have htrace : WordTrace (prefixWord ++ tailWord_3894201) baseStart_3894201 baseEnd_3894201 := by
    simpa [prefixWord, tailWord_3894201, baseEnd_3894201] using wordTrace_append hprefix tailTrace_3894201
  have hstable : (prefixWord ++ tailWord_3894201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894201).length < 2 ^ (prefixWord ++ tailWord_3894201).sum := by decide
  have hdescent : baseEnd_3894201 < baseStart_3894201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894233 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_3894233 : Nat := 118140960795 + 3894233 * 2 ^ 59
def prefixEnd_3894233 : Nat := 4983230072969 + 3 ^ 40 * 3894233 * 2
def baseEnd_3894233 : Nat := 1333075539733578352785503

theorem tailTrace_3894233 : CollatzResearch.WordTrace tailWord_3894233 prefixEnd_3894233 1333075539733578352785503 := by
  unfold tailWord_3894233
  simp only [CollatzResearch.WordTrace]
  refine ⟨142034346100866397891623353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94689564067244265261082235 142034346100866397891623353)
  ·
    refine ⟨106525759575649798418717515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142034346100866397891623353 106525759575649798418717515)
    ·
      refine ⟨159788639363474697628076273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106525759575649798418717515 159788639363474697628076273)
      ·
        refine ⟨119841479522606023221057205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159788639363474697628076273 119841479522606023221057205)
        ·
          refine ⟨11235138705244314676974113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119841479522606023221057205 11235138705244314676974113)
          ·
            refine ⟨8426354028933236007730585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11235138705244314676974113 8426354028933236007730585)
            ·
              refine ⟨6319765521699927005797939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8426354028933236007730585 6319765521699927005797939)
              ·
                refine ⟨9479648282549890508696909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6319765521699927005797939 9479648282549890508696909)
                ·
                  refine ⟨3554868105956208940761341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9479648282549890508696909 3554868105956208940761341)
                  ·
                    refine ⟨1333075539733578352785503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554868105956208940761341 1333075539733578352785503)
                    ·
                      rfl

theorem cell22_3894233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_3894233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894233 prefixEnd_3894233 := by exact prefixLift 3894233
  have htrace : WordTrace (prefixWord ++ tailWord_3894233) baseStart_3894233 baseEnd_3894233 := by
    simpa [prefixWord, tailWord_3894233, baseEnd_3894233] using wordTrace_append hprefix tailTrace_3894233
  have hstable : (prefixWord ++ tailWord_3894233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894233).length < 2 ^ (prefixWord ++ tailWord_3894233).sum := by decide
  have hdescent : baseEnd_3894233 < baseStart_3894233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894244 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3894244 : Nat := 118140960795 + 3894244 * 2 ^ 59
def prefixEnd_3894244 : Nat := 4983230072969 + 3 ^ 40 * 3894244 * 2
def baseEnd_3894244 : Nat := 1333079305258377990760469

theorem tailTrace_3894244 : CollatzResearch.WordTrace tailWord_3894244 prefixEnd_3894244 1333079305258377990760469 := by
  unfold tailWord_3894244
  simp only [CollatzResearch.WordTrace]
  refine ⟨71017373651913273385136893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94689831535884364513515857 71017373651913273385136893)
  ·
    refine ⟨26631515119467477519426335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71017373651913273385136893 26631515119467477519426335)
    ·
      refine ⟨39947272679201216279139503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26631515119467477519426335 39947272679201216279139503)
      ·
        refine ⟨59920909018801824418709255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39947272679201216279139503 59920909018801824418709255)
        ·
          refine ⟨89881363528202736628063883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59920909018801824418709255 89881363528202736628063883)
          ·
            refine ⟨134822045292304104942095825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89881363528202736628063883 134822045292304104942095825)
            ·
              refine ⟨101116533969228078706571869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134822045292304104942095825 101116533969228078706571869)
              ·
                refine ⟨37918700238460529514964451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101116533969228078706571869 37918700238460529514964451)
                ·
                  refine ⟨56878050357690794272446677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37918700238460529514964451 56878050357690794272446677)
                  ·
                    refine ⟨1333079305258377990760469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56878050357690794272446677 1333079305258377990760469)
                    ·
                      rfl

theorem cell22_3894244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3894244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894244 prefixEnd_3894244 := by exact prefixLift 3894244
  have htrace : WordTrace (prefixWord ++ tailWord_3894244) baseStart_3894244 baseEnd_3894244 := by
    simpa [prefixWord, tailWord_3894244, baseEnd_3894244] using wordTrace_append hprefix tailTrace_3894244
  have hstable : (prefixWord ++ tailWord_3894244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894244).length < 2 ^ (prefixWord ++ tailWord_3894244).sum := by decide
  have hdescent : baseEnd_3894244 < baseStart_3894244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894342 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3894342 : Nat := 118140960795 + 3894342 * 2 ^ 59
def prefixEnd_3894342 : Nat := 4983230072969 + 3 ^ 40 * 3894342 * 2
def baseEnd_3894342 : Nat := 444370950887046133936723

theorem tailTrace_3894342 : CollatzResearch.WordTrace tailWord_3894342 prefixEnd_3894342 444370950887046133936723 := by
  unfold tailWord_3894342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4438697551795984672104415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94692214438314339671560853 4438697551795984672104415)
  ·
    refine ⟨6658046327693977008156623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4438697551795984672104415 6658046327693977008156623)
    ·
      refine ⟨9987069491540965512234935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658046327693977008156623 9987069491540965512234935)
      ·
        refine ⟨14980604237311448268352403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9987069491540965512234935 14980604237311448268352403)
        ·
          refine ⟨22470906355967172402528605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14980604237311448268352403 22470906355967172402528605)
          ·
            refine ⟨8426589883487689650948227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22470906355967172402528605 8426589883487689650948227)
            ·
              refine ⟨12639884825231534476422341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8426589883487689650948227 12639884825231534476422341)
              ·
                refine ⟨2369978404730912714329189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12639884825231534476422341 2369978404730912714329189)
                ·
                  refine ⟨444370950887046133936723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2369978404730912714329189 444370950887046133936723)
                  ·
                    rfl

theorem cell22_3894342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3894342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894342 prefixEnd_3894342 := by exact prefixLift 3894342
  have htrace : WordTrace (prefixWord ++ tailWord_3894342) baseStart_3894342 baseEnd_3894342 := by
    simpa [prefixWord, tailWord_3894342, baseEnd_3894342] using wordTrace_append hprefix tailTrace_3894342
  have hstable : (prefixWord ++ tailWord_3894342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894342).length < 2 ^ (prefixWord ++ tailWord_3894342).sum := by decide
  have hdescent : baseEnd_3894342 < baseStart_3894342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894368 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_3894368 : Nat := 118140960795 + 3894368 * 2 ^ 59
def prefixEnd_3894368 : Nat := 4983230072969 + 3 ^ 40 * 3894368 * 2
def baseEnd_3894368 : Nat := 1333121752992483000660089

theorem tailTrace_3894368 : CollatzResearch.WordTrace tailWord_3894368 prefixEnd_3894368 1333121752992483000660089 := by
  unfold tailWord_3894368
  simp only [CollatzResearch.WordTrace]
  refine ⟨71019634977688657973893879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94692846636918210631858505 71019634977688657973893879)
  ·
    refine ⟨106529452466532986960840819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71019634977688657973893879 106529452466532986960840819)
    ·
      refine ⟨159794178699799480441261229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106529452466532986960840819 159794178699799480441261229)
      ·
        refine ⟨59922817012424805165472961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159794178699799480441261229 59922817012424805165472961)
        ·
          refine ⟨44942112759318603874104721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59922817012424805165472961 44942112759318603874104721)
          ·
            refine ⟨33706584569488952905578541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44942112759318603874104721 33706584569488952905578541)
            ·
              refine ⟨12639969213558357339591953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33706584569488952905578541 12639969213558357339591953)
              ·
                refine ⟨9479976910168768004693965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12639969213558357339591953 9479976910168768004693965)
                ·
                  refine ⟨3554991341313288001760237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9479976910168768004693965 3554991341313288001760237)
                  ·
                    refine ⟨1333121752992483000660089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3554991341313288001760237 1333121752992483000660089)
                    ·
                      rfl

theorem cell22_3894368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_3894368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894368 prefixEnd_3894368 := by exact prefixLift 3894368
  have htrace : WordTrace (prefixWord ++ tailWord_3894368) baseStart_3894368 baseEnd_3894368 := by
    simpa [prefixWord, tailWord_3894368, baseEnd_3894368] using wordTrace_append hprefix tailTrace_3894368
  have hstable : (prefixWord ++ tailWord_3894368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894368).length < 2 ^ (prefixWord ++ tailWord_3894368).sum := by decide
  have hdescent : baseEnd_3894368 < baseStart_3894368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894370 : List Nat := [3, 3, 2, 2, 1, 2, 3, 6]
def baseStart_3894370 : Nat := 118140960795 + 3894370 * 2 ^ 59
def prefixEnd_3894370 : Nat := 4983230072969 + 3 ^ 40 * 3894370 * 2
def baseEnd_3894370 : Nat := 148124715292595073567787

theorem tailTrace_3894370 : CollatzResearch.WordTrace tailWord_3894370 prefixEnd_3894370 148124715292595073567787 := by
  unfold tailWord_3894370
  simp only [CollatzResearch.WordTrace]
  refine ⟨35509835725342517572340141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94692895267580046859573709 35509835725342517572340141)
  ·
    refine ⟨13316188397003444089627553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35509835725342517572340141 13316188397003444089627553)
    ·
      refine ⟨9987141297752583067220665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13316188397003444089627553 9987141297752583067220665)
      ·
        refine ⟨7490355973314437300415499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9987141297752583067220665 7490355973314437300415499)
        ·
          refine ⟨11235533959971655950623249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7490355973314437300415499 11235533959971655950623249)
          ·
            refine ⟨8426650469978741962967437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11235533959971655950623249 8426650469978741962967437)
            ·
              refine ⟨3159993926242028236112789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8426650469978741962967437 3159993926242028236112789)
              ·
                refine ⟨148124715292595073567787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3159993926242028236112789 148124715292595073567787)
                ·
                  rfl

theorem cell22_3894370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_3894370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894370 prefixEnd_3894370 := by exact prefixLift 3894370
  have htrace : WordTrace (prefixWord ++ tailWord_3894370) baseStart_3894370 baseEnd_3894370 := by
    simpa [prefixWord, tailWord_3894370, baseEnd_3894370] using wordTrace_append hprefix tailTrace_3894370
  have hstable : (prefixWord ++ tailWord_3894370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894370).length < 2 ^ (prefixWord ++ tailWord_3894370).sum := by decide
  have hdescent : baseEnd_3894370 < baseStart_3894370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894396 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_3894396 : Nat := 118140960795 + 3894396 * 2 ^ 59
def prefixEnd_3894396 : Nat := 4983230072969 + 3 ^ 40 * 3894396 * 2
def baseEnd_3894396 : Nat := 1333131337964700260960003

theorem tailTrace_3894396 : CollatzResearch.WordTrace tailWord_3894396 prefixEnd_3894396 1333131337964700260960003 := by
  unfold tailWord_3894396
  simp only [CollatzResearch.WordTrace]
  refine ⟨71020145599637938364903521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94693527466183917819871361 71020145599637938364903521)
  ·
    refine ⟨53265109199728453773677641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71020145599637938364903521 53265109199728453773677641)
    ·
      refine ⟨39948831899796340330258231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53265109199728453773677641 39948831899796340330258231)
      ·
        refine ⟨59923247849694510495387347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39948831899796340330258231 59923247849694510495387347)
        ·
          refine ⟨89884871774541765743081021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59923247849694510495387347 89884871774541765743081021)
          ·
            refine ⟨33706826915453162153655383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89884871774541765743081021 33706826915453162153655383)
            ·
              refine ⟨50560240373179743230483075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33706826915453162153655383 50560240373179743230483075)
              ·
                refine ⟨75840360559769614845724613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50560240373179743230483075 75840360559769614845724613)
                ·
                  refine ⟨14220067604956802783573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75840360559769614845724613 14220067604956802783573365)
                  ·
                    refine ⟨1333131337964700260960003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14220067604956802783573365 1333131337964700260960003)
                    ·
                      rfl

theorem cell22_3894396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_3894396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894396 prefixEnd_3894396 := by exact prefixLift 3894396
  have htrace : WordTrace (prefixWord ++ tailWord_3894396) baseStart_3894396 baseEnd_3894396 := by
    simpa [prefixWord, tailWord_3894396, baseEnd_3894396] using wordTrace_append hprefix tailTrace_3894396
  have hstable : (prefixWord ++ tailWord_3894396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894396).length < 2 ^ (prefixWord ++ tailWord_3894396).sum := by decide
  have hdescent : baseEnd_3894396 < baseStart_3894396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894411 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_3894411 : Nat := 118140960795 + 3894411 * 2 ^ 59
def prefixEnd_3894411 : Nat := 4983230072969 + 3 ^ 40 * 3894411 * 2
def baseEnd_3894411 : Nat := 1333136472771245221834957

theorem tailTrace_3894411 : CollatzResearch.WordTrace tailWord_3894411 prefixEnd_3894411 1333136472771245221834957 := by
  unfold tailWord_3894411
  simp only [CollatzResearch.WordTrace]
  refine ⟨142040838294221534291603087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94693892196147689527735391 142040838294221534291603087)
  ·
    refine ⟨213061257441332301437404631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142040838294221534291603087 213061257441332301437404631)
    ·
      refine ⟨319591886161998452156106947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213061257441332301437404631 319591886161998452156106947)
      ·
        refine ⟨479387829242997678234160421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319591886161998452156106947 479387829242997678234160421)
        ·
          refine ⟨89885217983062064668905079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 479387829242997678234160421 89885217983062064668905079)
          ·
            refine ⟨134827826974593097003357619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89885217983062064668905079 134827826974593097003357619)
            ·
              refine ⟨202241740461889645505036429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134827826974593097003357619 202241740461889645505036429)
              ·
                refine ⟨75840652673208617064388661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202241740461889645505036429 75840652673208617064388661)
                ·
                  refine ⟨7110061188113307849786437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75840652673208617064388661 7110061188113307849786437)
                  ·
                    refine ⟨1333136472771245221834957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7110061188113307849786437 1333136472771245221834957)
                    ·
                      rfl

theorem cell22_3894411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_3894411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894411 prefixEnd_3894411 := by exact prefixLift 3894411
  have htrace : WordTrace (prefixWord ++ tailWord_3894411) baseStart_3894411 baseEnd_3894411 := by
    simpa [prefixWord, tailWord_3894411, baseEnd_3894411] using wordTrace_append hprefix tailTrace_3894411
  have hstable : (prefixWord ++ tailWord_3894411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894411).length < 2 ^ (prefixWord ++ tailWord_3894411).sum := by decide
  have hdescent : baseEnd_3894411 < baseStart_3894411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894456 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_3894456 : Nat := 118140960795 + 3894456 * 2 ^ 59
def prefixEnd_3894456 : Nat := 4983230072969 + 3 ^ 40 * 3894456 * 2
def baseEnd_3894456 : Nat := 1333151877190880104459819

theorem tailTrace_3894456 : CollatzResearch.WordTrace tailWord_3894456 prefixEnd_3894456 1333151877190880104459819 := by
  unfold tailWord_3894456
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021239789529253488495611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94694986386039004651327481 71021239789529253488495611)
  ·
    refine ⟨106531859684293880232743417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71021239789529253488495611 106531859684293880232743417)
    ·
      refine ⟨79898894763220410174557563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106531859684293880232743417 79898894763220410174557563)
      ·
        refine ⟨119848342144830615261836345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79898894763220410174557563 119848342144830615261836345)
        ·
          refine ⟨89886256608622961446377259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119848342144830615261836345 89886256608622961446377259)
          ·
            refine ⟨134829384912934442169565889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89886256608622961446377259 134829384912934442169565889)
            ·
              refine ⟨101122038684700831627174417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134829384912934442169565889 101122038684700831627174417)
              ·
                refine ⟨75841529013525623720380813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101122038684700831627174417 75841529013525623720380813)
                ·
                  refine ⟨28440573380072108895142805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75841529013525623720380813 28440573380072108895142805)
                  ·
                    refine ⟨1333151877190880104459819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28440573380072108895142805 1333151877190880104459819)
                    ·
                      rfl

theorem cell22_3894456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_3894456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894456 prefixEnd_3894456 := by exact prefixLift 3894456
  have htrace : WordTrace (prefixWord ++ tailWord_3894456) baseStart_3894456 baseEnd_3894456 := by
    simpa [prefixWord, tailWord_3894456, baseEnd_3894456] using wordTrace_append hprefix tailTrace_3894456
  have hstable : (prefixWord ++ tailWord_3894456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894456).length < 2 ^ (prefixWord ++ tailWord_3894456).sum := by decide
  have hdescent : baseEnd_3894456 < baseStart_3894456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894460 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 6]
def baseStart_3894460 : Nat := 118140960795 + 3894460 * 2 ^ 59
def prefixEnd_3894460 : Nat := 4983230072969 + 3 ^ 40 * 3894460 * 2
def baseEnd_3894460 : Nat := 444384415490875142453269

theorem tailTrace_3894460 : CollatzResearch.WordTrace tailWord_3894460 prefixEnd_3894460 444384415490875142453269 := by
  unfold tailWord_3894460
  simp only [CollatzResearch.WordTrace]
  refine ⟨71021312735522007830068417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94695083647362677106757889 71021312735522007830068417)
  ·
    refine ⟨53265984551641505872551313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71021312735522007830068417 53265984551641505872551313)
    ·
      refine ⟨39949488413731129404413485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53265984551641505872551313 39949488413731129404413485)
      ·
        refine ⟨14981058155149173526655057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39949488413731129404413485 14981058155149173526655057)
        ·
          refine ⟨11235793616361880144991293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14981058155149173526655057 11235793616361880144991293)
          ·
            refine ⟨4213422606135705054371735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11235793616361880144991293 4213422606135705054371735)
            ·
              refine ⟨6320133909203557581557603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213422606135705054371735 6320133909203557581557603)
              ·
                refine ⟨9480200863805336372336405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6320133909203557581557603 9480200863805336372336405)
                ·
                  refine ⟨444384415490875142453269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9480200863805336372336405 444384415490875142453269)
                  ·
                    rfl

theorem cell22_3894460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_3894460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894460 prefixEnd_3894460 := by exact prefixLift 3894460
  have htrace : WordTrace (prefixWord ++ tailWord_3894460) baseStart_3894460 baseEnd_3894460 := by
    simpa [prefixWord, tailWord_3894460, baseEnd_3894460] using wordTrace_append hprefix tailTrace_3894460
  have hstable : (prefixWord ++ tailWord_3894460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894460).length < 2 ^ (prefixWord ++ tailWord_3894460).sum := by decide
  have hdescent : baseEnd_3894460 < baseStart_3894460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894466 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3894466 : Nat := 118140960795 + 3894466 * 2 ^ 59
def prefixEnd_3894466 : Nat := 4983230072969 + 3 ^ 40 * 3894466 * 2
def baseEnd_3894466 : Nat := 444385100131747803903263

theorem tailTrace_3894466 : CollatzResearch.WordTrace tailWord_3894466 prefixEnd_3894466 444385100131747803903263 := by
  unfold tailWord_3894466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35510711077255569671213813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94695229539348185789903501 35510711077255569671213813)
  ·
    refine ⟨3329129163492709656676295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35510711077255569671213813 3329129163492709656676295)
    ·
      refine ⟨4993693745239064485014443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3329129163492709656676295 4993693745239064485014443)
      ·
        refine ⟨7490540617858596727521665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4993693745239064485014443 7490540617858596727521665)
        ·
          refine ⟨5617905463393947545641249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7490540617858596727521665 5617905463393947545641249)
          ·
            refine ⟨4213429097545460659230937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5617905463393947545641249 4213429097545460659230937)
            ·
              refine ⟨3160071823159095494423203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4213429097545460659230937 3160071823159095494423203)
              ·
                refine ⟨4740107734738643241634805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160071823159095494423203 4740107734738643241634805)
                ·
                  refine ⟨444385100131747803903263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4740107734738643241634805 444385100131747803903263)
                  ·
                    rfl

theorem cell22_3894466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3894466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894466 prefixEnd_3894466 := by exact prefixLift 3894466
  have htrace : WordTrace (prefixWord ++ tailWord_3894466) baseStart_3894466 baseEnd_3894466 := by
    simpa [prefixWord, tailWord_3894466, baseEnd_3894466] using wordTrace_append hprefix tailTrace_3894466
  have hstable : (prefixWord ++ tailWord_3894466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894466).length < 2 ^ (prefixWord ++ tailWord_3894466).sum := by decide
  have hdescent : baseEnd_3894466 < baseStart_3894466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894533 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 5]
def baseStart_3894533 : Nat := 118140960795 + 3894533 * 2 ^ 59
def prefixEnd_3894533 : Nat := 4983230072969 + 3 ^ 40 * 3894533 * 2
def baseEnd_3894533 : Nat := 444392745288159190094861

theorem tailTrace_3894533 : CollatzResearch.WordTrace tailWord_3894533 prefixEnd_3894533 444392745288159190094861 := by
  unfold tailWord_3894533
  simp only [CollatzResearch.WordTrace]
  refine ⟨142045287999779549127544253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94696858666519699418362835 142045287999779549127544253)
  ·
    refine ⟨53266982999917330922829095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142045287999779549127544253 53266982999917330922829095)
    ·
      refine ⟨79900474499875996384243643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53266982999917330922829095 79900474499875996384243643)
      ·
        refine ⟨119850711749813994576365465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79900474499875996384243643 119850711749813994576365465)
        ·
          refine ⟨89888033812360495932274099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119850711749813994576365465 89888033812360495932274099)
          ·
            refine ⟨134832050718540743898411149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89888033812360495932274099 134832050718540743898411149)
            ·
              refine ⟨50562019019452778961904181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134832050718540743898411149 50562019019452778961904181)
              ·
                refine ⟨4740189283073698027678517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50562019019452778961904181 4740189283073698027678517)
                ·
                  refine ⟨444392745288159190094861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4740189283073698027678517 444392745288159190094861)
                  ·
                    rfl

theorem cell22_3894533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_3894533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894533 prefixEnd_3894533 := by exact prefixLift 3894533
  have htrace : WordTrace (prefixWord ++ tailWord_3894533) baseStart_3894533 baseEnd_3894533 := by
    simpa [prefixWord, tailWord_3894533, baseEnd_3894533] using wordTrace_append hprefix tailTrace_3894533
  have hstable : (prefixWord ++ tailWord_3894533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894533).length < 2 ^ (prefixWord ++ tailWord_3894533).sum := by decide
  have hdescent : baseEnd_3894533 < baseStart_3894533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894554 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_3894554 : Nat := 118140960795 + 3894554 * 2 ^ 59
def prefixEnd_3894554 : Nat := 4983230072969 + 3 ^ 40 * 3894554 * 2
def baseEnd_3894554 : Nat := 1333185424593640515509519

theorem tailTrace_3894554 : CollatzResearch.WordTrace tailWord_3894554 prefixEnd_3894554 1333185424593640515509519 := by
  unfold tailWord_3894554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35511513483175867428514679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94697369288468979809372477 35511513483175867428514679)
  ·
    refine ⟨53267270224763801142772019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35511513483175867428514679 53267270224763801142772019)
    ·
      refine ⟨79900905337145701714158029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53267270224763801142772019 79900905337145701714158029)
      ·
        refine ⟨29962839501429638142809261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79900905337145701714158029 29962839501429638142809261)
        ·
          refine ⟨11236064813036114303553473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29962839501429638142809261 11236064813036114303553473)
          ·
            refine ⟨8427048609777085727665105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11236064813036114303553473 8427048609777085727665105)
            ·
              refine ⟨6320286457332814295748829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8427048609777085727665105 6320286457332814295748829)
              ·
                refine ⟨2370107421499805360905811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6320286457332814295748829 2370107421499805360905811)
                ·
                  refine ⟨3555161132249708041358717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370107421499805360905811 3555161132249708041358717)
                  ·
                    refine ⟨1333185424593640515509519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555161132249708041358717 1333185424593640515509519)
                    ·
                      rfl

theorem cell22_3894554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_3894554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894554 prefixEnd_3894554 := by exact prefixLift 3894554
  have htrace : WordTrace (prefixWord ++ tailWord_3894554) baseStart_3894554 baseEnd_3894554 := by
    simpa [prefixWord, tailWord_3894554, baseEnd_3894554] using wordTrace_append hprefix tailTrace_3894554
  have hstable : (prefixWord ++ tailWord_3894554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894554).length < 2 ^ (prefixWord ++ tailWord_3894554).sum := by decide
  have hdescent : baseEnd_3894554 < baseStart_3894554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894605 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3894605 : Nat := 118140960795 + 3894605 * 2 ^ 59
def prefixEnd_3894605 : Nat := 4983230072969 + 3 ^ 40 * 3894605 * 2
def baseEnd_3894605 : Nat := 1333202882935893382484363

theorem tailTrace_3894605 : CollatzResearch.WordTrace tailWord_3894605 prefixEnd_3894605 1333202882935893382484363 := by
  unfold tailWord_3894605
  simp only [CollatzResearch.WordTrace]
  refine ⟨142047914055518705424165269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94698609370345803616110179 142047914055518705424165269)
  ·
    refine ⟨6658495971352439316757747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142047914055518705424165269 6658495971352439316757747)
    ·
      refine ⟨9987743957028658975136621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6658495971352439316757747 9987743957028658975136621)
      ·
        refine ⟨3745403983885747115676233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9987743957028658975136621 3745403983885747115676233)
        ·
          refine ⟨2809052987914310336757175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3745403983885747115676233 2809052987914310336757175)
          ·
            refine ⟨4213579481871465505135763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2809052987914310336757175 4213579481871465505135763)
            ·
              refine ⟨6320369222807198257703645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4213579481871465505135763 6320369222807198257703645)
              ·
                refine ⟨2370138458552699346638867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6320369222807198257703645 2370138458552699346638867)
                ·
                  refine ⟨3555207687829049019958301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2370138458552699346638867 3555207687829049019958301)
                  ·
                    refine ⟨1333202882935893382484363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555207687829049019958301 1333202882935893382484363)
                    ·
                      rfl

theorem cell22_3894605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3894605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894605 prefixEnd_3894605 := by exact prefixLift 3894605
  have htrace : WordTrace (prefixWord ++ tailWord_3894605) baseStart_3894605 baseEnd_3894605 := by
    simpa [prefixWord, tailWord_3894605, baseEnd_3894605] using wordTrace_append hprefix tailTrace_3894605
  have hstable : (prefixWord ++ tailWord_3894605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894605).length < 2 ^ (prefixWord ++ tailWord_3894605).sum := by decide
  have hdescent : baseEnd_3894605 < baseStart_3894605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894608 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_3894608 : Nat := 118140960795 + 3894608 * 2 ^ 59
def prefixEnd_3894608 : Nat := 4983230072969 + 3 ^ 40 * 3894608 * 2
def baseEnd_3894608 : Nat := 1333203909897202374659353

theorem tailTrace_3894608 : CollatzResearch.WordTrace tailWord_3894608 prefixEnd_3894608 1333203909897202374659353 := by
  unfold tailWord_3894608
  simp only [CollatzResearch.WordTrace]
  refine ⟨71024011737253918468262239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94698682316338557957682985 71024011737253918468262239)
  ·
    refine ⟨106536017605880877702393359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71024011737253918468262239 106536017605880877702393359)
    ·
      refine ⟨159804026408821316553590039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106536017605880877702393359 159804026408821316553590039)
      ·
        refine ⟨239706039613231974830385059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159804026408821316553590039 239706039613231974830385059)
        ·
          refine ⟨359559059419847962245577589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239706039613231974830385059 359559059419847962245577589)
          ·
            refine ⟨33708661820610746460522899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 359559059419847962245577589 33708661820610746460522899)
            ·
              refine ⟨50562992730916119690784349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33708661820610746460522899 50562992730916119690784349)
              ·
                refine ⟨18961122274093544884044131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50562992730916119690784349 18961122274093544884044131)
                ·
                  refine ⟨28441683411140317326066197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18961122274093544884044131 28441683411140317326066197)
                  ·
                    refine ⟨1333203909897202374659353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28441683411140317326066197 1333203909897202374659353)
                    ·
                      rfl

theorem cell22_3894608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_3894608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894608 prefixEnd_3894608 := by exact prefixLift 3894608
  have htrace : WordTrace (prefixWord ++ tailWord_3894608) baseStart_3894608 baseEnd_3894608 := by
    simpa [prefixWord, tailWord_3894608, baseEnd_3894608] using wordTrace_append hprefix tailTrace_3894608
  have hstable : (prefixWord ++ tailWord_3894608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894608).length < 2 ^ (prefixWord ++ tailWord_3894608).sum := by decide
  have hdescent : baseEnd_3894608 < baseStart_3894608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894760 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3894760 : Nat := 118140960795 + 3894760 * 2 ^ 59
def prefixEnd_3894760 : Nat := 4983230072969 + 3 ^ 40 * 3894760 * 2
def baseEnd_3894760 : Nat := 1333255942603524644858887

theorem tailTrace_3894760 : CollatzResearch.WordTrace tailWord_3894760 prefixEnd_3894760 1333255942603524644858887 := by
  unfold tailWord_3894760
  simp only [CollatzResearch.WordTrace]
  refine ⟨71026783684978583448028867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94702378246638111264038489 71026783684978583448028867)
  ·
    refine ⟨106540175527467875172043301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71026783684978583448028867 106540175527467875172043301)
    ·
      refine ⟨19976282911400226594758119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106540175527467875172043301 19976282911400226594758119)
      ·
        refine ⟨29964424367100339892137179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19976282911400226594758119 29964424367100339892137179)
        ·
          refine ⟨44946636550650509838205769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29964424367100339892137179 44946636550650509838205769)
          ·
            refine ⟨33709977412987882378654327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44946636550650509838205769 33709977412987882378654327)
            ·
              refine ⟨50564966119481823567981491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33709977412987882378654327 50564966119481823567981491)
              ·
                refine ⟨75847449179222735351972237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50564966119481823567981491 75847449179222735351972237)
                ·
                  refine ⟨28442793442208525756989589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75847449179222735351972237 28442793442208525756989589)
                  ·
                    refine ⟨1333255942603524644858887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28442793442208525756989589 1333255942603524644858887)
                    ·
                      rfl

theorem cell22_3894760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3894760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894760 prefixEnd_3894760 := by exact prefixLift 3894760
  have htrace : WordTrace (prefixWord ++ tailWord_3894760) baseStart_3894760 baseEnd_3894760 := by
    simpa [prefixWord, tailWord_3894760, baseEnd_3894760] using wordTrace_append hprefix tailTrace_3894760
  have hstable : (prefixWord ++ tailWord_3894760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894760).length < 2 ^ (prefixWord ++ tailWord_3894760).sum := by decide
  have hdescent : baseEnd_3894760 < baseStart_3894760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894901 : List Nat := [1, 3, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3894901 : Nat := 118140960795 + 3894901 * 2 ^ 59
def prefixEnd_3894901 : Nat := 4983230072969 + 3 ^ 40 * 3894901 * 2
def baseEnd_3894901 : Nat := 1333304209785047277083455

theorem tailTrace_3894901 : CollatzResearch.WordTrace tailWord_3894901 prefixEnd_3894901 1333304209785047277083455 := by
  unfold tailWord_3894901
  simp only [CollatzResearch.WordTrace]
  refine ⟨142058710062446347976940557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94705806708297565317960371 142058710062446347976940557)
  ·
    refine ⟨53272016273417380491352709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142058710062446347976940557 53272016273417380491352709)
    ·
      refine ⟨9988503051265758842128633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53272016273417380491352709 9988503051265758842128633)
      ·
        refine ⟨7491377288449319131596475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9988503051265758842128633 7491377288449319131596475)
        ·
          refine ⟨11237065932673978697394713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491377288449319131596475 11237065932673978697394713)
          ·
            refine ⟨8427799449505484023046035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11237065932673978697394713 8427799449505484023046035)
            ·
              refine ⟨12641699174258226034569053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8427799449505484023046035 12641699174258226034569053)
              ·
                refine ⟨4740637190346834762963395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12641699174258226034569053 4740637190346834762963395)
                ·
                  refine ⟨7110955785520252144445093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740637190346834762963395 7110955785520252144445093)
                  ·
                    refine ⟨1333304209785047277083455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7110955785520252144445093 1333304209785047277083455)
                    ·
                      rfl

theorem cell22_3894901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3894901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894901 prefixEnd_3894901 := by exact prefixLift 3894901
  have htrace : WordTrace (prefixWord ++ tailWord_3894901) baseStart_3894901 baseEnd_3894901 := by
    simpa [prefixWord, tailWord_3894901, baseEnd_3894901] using wordTrace_append hprefix tailTrace_3894901
  have hstable : (prefixWord ++ tailWord_3894901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894901).length < 2 ^ (prefixWord ++ tailWord_3894901).sum := by decide
  have hdescent : baseEnd_3894901 < baseStart_3894901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894912 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_3894912 : Nat := 118140960795 + 3894912 * 2 ^ 59
def prefixEnd_3894912 : Nat := 4983230072969 + 3 ^ 40 * 3894912 * 2
def baseEnd_3894912 : Nat := 1333307975309846915058421

theorem tailTrace_3894912 : CollatzResearch.WordTrace tailWord_3894912 prefixEnd_3894912 1333307975309846915058421 := by
  unfold tailWord_3894912
  simp only [CollatzResearch.WordTrace]
  refine ⟨71029555632703248427795495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94706074176937664570393993 71029555632703248427795495)
  ·
    refine ⟨106544333449054872641693243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71029555632703248427795495 106544333449054872641693243)
    ·
      refine ⟨159816500173582308962539865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106544333449054872641693243 159816500173582308962539865)
      ·
        refine ⟨119862375130186731721904899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159816500173582308962539865 119862375130186731721904899)
        ·
          refine ⟨179793562695280097582857349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119862375130186731721904899 179793562695280097582857349)
          ·
            refine ⟨33711293005365018296785753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 179793562695280097582857349 33711293005365018296785753)
            ·
              refine ⟨25283469754023763722589315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33711293005365018296785753 25283469754023763722589315)
              ·
                refine ⟨37925204631035645583883973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25283469754023763722589315 37925204631035645583883973)
                ·
                  refine ⟨7110975868319183546978245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37925204631035645583883973 7110975868319183546978245)
                  ·
                    refine ⟨1333307975309846915058421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7110975868319183546978245 1333307975309846915058421)
                    ·
                      rfl

theorem cell22_3894912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_3894912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894912 prefixEnd_3894912 := by exact prefixLift 3894912
  have htrace : WordTrace (prefixWord ++ tailWord_3894912) baseStart_3894912 baseEnd_3894912 := by
    simpa [prefixWord, tailWord_3894912, baseEnd_3894912] using wordTrace_append hprefix tailTrace_3894912
  have hstable : (prefixWord ++ tailWord_3894912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894912).length < 2 ^ (prefixWord ++ tailWord_3894912).sum := by decide
  have hdescent : baseEnd_3894912 < baseStart_3894912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894944 : List Nat := [2, 1, 1, 4, 3, 1, 4, 6]
def baseStart_3894944 : Nat := 118140960795 + 3894944 * 2 ^ 59
def prefixEnd_3894944 : Nat := 4983230072969 + 3 ^ 40 * 3894944 * 2
def baseEnd_3894944 : Nat := 148146547729312166473147

theorem tailTrace_3894944 : CollatzResearch.WordTrace tailWord_3894944 prefixEnd_3894944 148146547729312166473147 := by
  unfold tailWord_3894944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71030139200645283160377943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94706852267527044213837257 71030139200645283160377943)
  ·
    refine ⟨106545208800967924740566915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71030139200645283160377943 106545208800967924740566915)
    ·
      refine ⟨159817813201451887110850373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106545208800967924740566915 159817813201451887110850373)
      ·
        refine ⟨29965839975272228833284445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159817813201451887110850373 29965839975272228833284445)
        ·
          refine ⟨11237189990727085812481667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29965839975272228833284445 11237189990727085812481667)
          ·
            refine ⟨16855784986090628718722501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237189990727085812481667 16855784986090628718722501)
            ·
              refine ⟨3160459684891992884760469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16855784986090628718722501 3160459684891992884760469)
              ·
                refine ⟨148146547729312166473147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3160459684891992884760469 148146547729312166473147)
                ·
                  rfl

theorem cell22_3894944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_3894944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894944 prefixEnd_3894944 := by exact prefixLift 3894944
  have htrace : WordTrace (prefixWord ++ tailWord_3894944) baseStart_3894944 baseEnd_3894944 := by
    simpa [prefixWord, tailWord_3894944, baseEnd_3894944] using wordTrace_append hprefix tailTrace_3894944
  have hstable : (prefixWord ++ tailWord_3894944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894944).length < 2 ^ (prefixWord ++ tailWord_3894944).sum := by decide
  have hdescent : baseEnd_3894944 < baseStart_3894944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894982 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3894982 : Nat := 118140960795 + 3894982 * 2 ^ 59
def prefixEnd_3894982 : Nat := 4983230072969 + 3 ^ 40 * 3894982 * 2
def baseEnd_3894982 : Nat := 1333331937740390065808207

theorem tailTrace_3894982 : CollatzResearch.WordTrace tailWord_3894982 prefixEnd_3894982 1333331937740390065808207 := by
  unfold tailWord_3894982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4439427011723528087832475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94707776250101932540426133 4439427011723528087832475)
  ·
    refine ⟨6659140517585292131748713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4439427011723528087832475 6659140517585292131748713)
    ·
      refine ⟨4994355388188969098811535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6659140517585292131748713 4994355388188969098811535)
      ·
        refine ⟨7491533082283453648217303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994355388188969098811535 7491533082283453648217303)
        ·
          refine ⟨11237299623425180472325955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7491533082283453648217303 11237299623425180472325955)
          ·
            refine ⟨16855949435137770708488933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11237299623425180472325955 16855949435137770708488933)
            ·
              refine ⟨3160490519088332007841675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16855949435137770708488933 3160490519088332007841675)
              ·
                refine ⟨4740735778632498011762513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160490519088332007841675 4740735778632498011762513)
                ·
                  refine ⟨3555551833974373508821885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4740735778632498011762513 3555551833974373508821885)
                  ·
                    refine ⟨1333331937740390065808207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555551833974373508821885 1333331937740390065808207)
                    ·
                      rfl

theorem cell22_3894982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3894982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894982 prefixEnd_3894982 := by exact prefixLift 3894982
  have htrace : WordTrace (prefixWord ++ tailWord_3894982) baseStart_3894982 baseEnd_3894982 := by
    simpa [prefixWord, tailWord_3894982, baseEnd_3894982] using wordTrace_append hprefix tailTrace_3894982
  have hstable : (prefixWord ++ tailWord_3894982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894982).length < 2 ^ (prefixWord ++ tailWord_3894982).sum := by decide
  have hdescent : baseEnd_3894982 < baseStart_3894982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3894987 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_3894987 : Nat := 118140960795 + 3894987 * 2 ^ 59
def prefixEnd_3894987 : Nat := 4983230072969 + 3 ^ 40 * 3894987 * 2
def baseEnd_3894987 : Nat := 1333333649342571719433191

theorem tailTrace_3894987 : CollatzResearch.WordTrace tailWord_3894987 prefixEnd_3894987 1333333649342571719433191 := by
  unfold tailWord_3894987
  simp only [CollatzResearch.WordTrace]
  refine ⟨142061846740134784664571215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94707897826756523109714143 142061846740134784664571215)
  ·
    refine ⟨213092770110202176996856823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142061846740134784664571215 213092770110202176996856823)
    ·
      refine ⟨319639155165303265495285235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213092770110202176996856823 319639155165303265495285235)
      ·
        refine ⟨479458732747954898242927853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319639155165303265495285235 479458732747954898242927853)
        ·
          refine ⟨179797024780483086841097945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479458732747954898242927853 179797024780483086841097945)
          ·
            refine ⟨134847768585362315130823459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179797024780483086841097945 134847768585362315130823459)
            ·
              refine ⟨202271652878043472696235189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134847768585362315130823459 202271652878043472696235189)
              ·
                refine ⟨18962967457316575565272049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202271652878043472696235189 18962967457316575565272049)
                ·
                  refine ⟨14222225592987431673954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18962967457316575565272049 14222225592987431673954037)
                  ·
                    refine ⟨1333333649342571719433191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14222225592987431673954037 1333333649342571719433191)
                    ·
                      rfl

theorem cell22_3894987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_3894987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3894987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3894987 prefixEnd_3894987 := by exact prefixLift 3894987
  have htrace : WordTrace (prefixWord ++ tailWord_3894987) baseStart_3894987 baseEnd_3894987 := by
    simpa [prefixWord, tailWord_3894987, baseEnd_3894987] using wordTrace_append hprefix tailTrace_3894987
  have hstable : (prefixWord ++ tailWord_3894987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3894987).length < 2 ^ (prefixWord ++ tailWord_3894987).sum := by decide
  have hdescent : baseEnd_3894987 < baseStart_3894987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3894987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895019 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 1, 4]
def baseStart_3895019 : Nat := 118140960795 + 3895019 * 2 ^ 59
def prefixEnd_3895019 : Nat := 4983230072969 + 3 ^ 40 * 3895019 * 2
def baseEnd_3895019 : Nat := 1333344603596534302633093

theorem tailTrace_3895019 : CollatzResearch.WordTrace tailWord_3895019 prefixEnd_3895019 1333344603596534302633093 := by
  unfold tailWord_3895019
  simp only [CollatzResearch.WordTrace]
  refine ⟨142063013876018854129736111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94708675917345902753157407 142063013876018854129736111)
  ·
    refine ⟨213094520814028281194604167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142063013876018854129736111 213094520814028281194604167)
    ·
      refine ⟨319641781221042421791906251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213094520814028281194604167 319641781221042421791906251)
      ·
        refine ⟨479462671831563632687859377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319641781221042421791906251 479462671831563632687859377)
        ·
          refine ⟨359597003873672724515894533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479462671831563632687859377 359597003873672724515894533)
          ·
            refine ⟨67424438226313635846730225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 359597003873672724515894533 67424438226313635846730225)
            ·
              refine ⟨50568328669735226885047669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67424438226313635846730225 50568328669735226885047669)
              ·
                refine ⟨4740780812787677520473219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50568328669735226885047669 4740780812787677520473219)
                ·
                  refine ⟨7111171219181516280709829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4740780812787677520473219 7111171219181516280709829)
                  ·
                    refine ⟨1333344603596534302633093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111171219181516280709829 1333344603596534302633093)
                    ·
                      rfl

theorem cell22_3895019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4].length) (baseStart_3895019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895019 prefixEnd_3895019 := by exact prefixLift 3895019
  have htrace : WordTrace (prefixWord ++ tailWord_3895019) baseStart_3895019 baseEnd_3895019 := by
    simpa [prefixWord, tailWord_3895019, baseEnd_3895019] using wordTrace_append hprefix tailTrace_3895019
  have hstable : (prefixWord ++ tailWord_3895019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895019).length < 2 ^ (prefixWord ++ tailWord_3895019).sum := by decide
  have hdescent : baseEnd_3895019 < baseStart_3895019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895049 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_3895049 : Nat := 118140960795 + 3895049 * 2 ^ 59
def prefixEnd_3895049 : Nat := 4983230072969 + 3 ^ 40 * 3895049 * 2
def baseEnd_3895049 : Nat := 1333354873209624224383001

theorem tailTrace_3895049 : CollatzResearch.WordTrace tailWord_3895049 prefixEnd_3895049 1333354873209624224383001 := by
  unfold tailWord_3895049
  simp only [CollatzResearch.WordTrace]
  refine ⟨142064108065910169253328201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94709405377273446168885467 142064108065910169253328201)
  ·
    refine ⟨106548081049432626939996151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142064108065910169253328201 106548081049432626939996151)
    ·
      refine ⟨159822121574148940409994227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106548081049432626939996151 159822121574148940409994227)
      ·
        refine ⟨239733182361223410614991341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159822121574148940409994227 239733182361223410614991341)
        ·
          refine ⟨89899943385458778980621753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239733182361223410614991341 89899943385458778980621753)
          ·
            refine ⟨67424957539094084235466315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89899943385458778980621753 67424957539094084235466315)
            ·
              refine ⟨101137436308641126353199473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67424957539094084235466315 101137436308641126353199473)
              ·
                refine ⟨75853077231480844764899605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101137436308641126353199473 75853077231480844764899605)
                ·
                  refine ⟨3555612995225664598354669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75853077231480844764899605 3555612995225664598354669)
                  ·
                    refine ⟨1333354873209624224383001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555612995225664598354669 1333354873209624224383001)
                    ·
                      rfl

theorem cell22_3895049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_3895049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895049 prefixEnd_3895049 := by exact prefixLift 3895049
  have htrace : WordTrace (prefixWord ++ tailWord_3895049) baseStart_3895049 baseEnd_3895049 := by
    simpa [prefixWord, tailWord_3895049, baseEnd_3895049] using wordTrace_append hprefix tailTrace_3895049
  have hstable : (prefixWord ++ tailWord_3895049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895049).length < 2 ^ (prefixWord ++ tailWord_3895049).sum := by decide
  have hdescent : baseEnd_3895049 < baseStart_3895049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895111 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3895111 : Nat := 118140960795 + 3895111 * 2 ^ 59
def prefixEnd_3895111 : Nat := 4983230072969 + 3 ^ 40 * 3895111 * 2
def baseEnd_3895111 : Nat := 1333376097076676729332811

theorem tailTrace_3895111 : CollatzResearch.WordTrace tailWord_3895111 prefixEnd_3895111 1333376097076676729332811 := by
  unfold tailWord_3895111
  simp only [CollatzResearch.WordTrace]
  refine ⟨142066369391685553842085187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94710912927790369228056791 142066369391685553842085187)
  ·
    refine ⟨213099554087528330763127781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142066369391685553842085187 213099554087528330763127781)
    ·
      refine ⟨39956166391411562018086459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213099554087528330763127781 39956166391411562018086459)
      ·
        refine ⟨59934249587117343027129689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39956166391411562018086459 59934249587117343027129689)
        ·
          refine ⟨44950687190338007270347267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59934249587117343027129689 44950687190338007270347267)
          ·
            refine ⟨67426030785507010905520901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44950687190338007270347267 67426030785507010905520901)
            ·
              refine ⟨12642380772282564544785169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67426030785507010905520901 12642380772282564544785169)
              ·
                refine ⟨9481785579211923408588877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12642380772282564544785169 9481785579211923408588877)
                ·
                  refine ⟨3555669592204471278220829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9481785579211923408588877 3555669592204471278220829)
                  ·
                    refine ⟨1333376097076676729332811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555669592204471278220829 1333376097076676729332811)
                    ·
                      rfl

theorem cell22_3895111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3895111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895111 prefixEnd_3895111 := by exact prefixLift 3895111
  have htrace : WordTrace (prefixWord ++ tailWord_3895111) baseStart_3895111 baseEnd_3895111 := by
    simpa [prefixWord, tailWord_3895111, baseEnd_3895111] using wordTrace_append hprefix tailTrace_3895111
  have hstable : (prefixWord ++ tailWord_3895111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895111).length < 2 ^ (prefixWord ++ tailWord_3895111).sum := by decide
  have hdescent : baseEnd_3895111 < baseStart_3895111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895154 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_3895154 : Nat := 118140960795 + 3895154 * 2 ^ 59
def prefixEnd_3895154 : Nat := 4983230072969 + 3 ^ 40 * 3895154 * 2
def baseEnd_3895154 : Nat := 1333390816855438950507679

theorem tailTrace_3895154 : CollatzResearch.WordTrace tailWord_3895154 prefixEnd_3895154 1333390816855438950507679 := by
  unfold tailWord_3895154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35516984432632443046475129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94711958487019848123933677 35516984432632443046475129)
  ·
    refine ⟨26637738324474332284856347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35516984432632443046475129 26637738324474332284856347)
    ·
      refine ⟨39956607486711498427284521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26637738324474332284856347 39956607486711498427284521)
      ·
        refine ⟨29967455615033623820463391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39956607486711498427284521 29967455615033623820463391)
        ·
          refine ⟨44951183422550435730695087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29967455615033623820463391 44951183422550435730695087)
          ·
            refine ⟨67426775133825653596042631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44951183422550435730695087 67426775133825653596042631)
            ·
              refine ⟨101140162700738480394063947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67426775133825653596042631 101140162700738480394063947)
              ·
                refine ⟨151710244051107720591095921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101140162700738480394063947 151710244051107720591095921)
                ·
                  refine ⟨113782683038330790443321941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151710244051107720591095921 113782683038330790443321941)
                  ·
                    refine ⟨1333390816855438950507679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113782683038330790443321941 1333390816855438950507679)
                    ·
                      rfl

theorem cell22_3895154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_3895154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895154 prefixEnd_3895154 := by exact prefixLift 3895154
  have htrace : WordTrace (prefixWord ++ tailWord_3895154) baseStart_3895154 baseEnd_3895154 := by
    simpa [prefixWord, tailWord_3895154, baseEnd_3895154] using wordTrace_append hprefix tailTrace_3895154
  have hstable : (prefixWord ++ tailWord_3895154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895154).length < 2 ^ (prefixWord ++ tailWord_3895154).sum := by decide
  have hdescent : baseEnd_3895154 < baseStart_3895154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895171 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_3895171 : Nat := 118140960795 + 3895171 * 2 ^ 59
def prefixEnd_3895171 : Nat := 4983230072969 + 3 ^ 40 * 3895171 * 2
def baseEnd_3895171 : Nat := 1333396636302856572832627

theorem tailTrace_3895171 : CollatzResearch.WordTrace tailWord_3895171 prefixEnd_3895171 1333396636302856572832627 := by
  unfold tailWord_3895171
  simp only [CollatzResearch.WordTrace]
  refine ⟨142068557771468184089269367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94712371847645456059512911 142068557771468184089269367)
  ·
    refine ⟨213102836657202276133904051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142068557771468184089269367 213102836657202276133904051)
    ·
      refine ⟨319654254985803414200856077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213102836657202276133904051 319654254985803414200856077)
      ·
        refine ⟨119870345619676280325321029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 319654254985803414200856077 119870345619676280325321029)
        ·
          refine ⟨22475689803689302560997693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119870345619676280325321029 22475689803689302560997693)
          ·
            refine ⟨8428383676383488460374135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22475689803689302560997693 8428383676383488460374135)
            ·
              refine ⟨12642575514575232690561203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428383676383488460374135 12642575514575232690561203)
              ·
                refine ⟨18963863271862849035841805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12642575514575232690561203 18963863271862849035841805)
                ·
                  refine ⟨7111448726948568388440677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18963863271862849035841805 7111448726948568388440677)
                  ·
                    refine ⟨1333396636302856572832627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111448726948568388440677 1333396636302856572832627)
                    ·
                      rfl

theorem cell22_3895171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_3895171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895171 prefixEnd_3895171 := by exact prefixLift 3895171
  have htrace : WordTrace (prefixWord ++ tailWord_3895171) baseStart_3895171 baseEnd_3895171 := by
    simpa [prefixWord, tailWord_3895171, baseEnd_3895171] using wordTrace_append hprefix tailTrace_3895171
  have hstable : (prefixWord ++ tailWord_3895171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895171).length < 2 ^ (prefixWord ++ tailWord_3895171).sum := by decide
  have hdescent : baseEnd_3895171 < baseStart_3895171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895184 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_3895184 : Nat := 118140960795 + 3895184 * 2 ^ 59
def prefixEnd_3895184 : Nat := 4983230072969 + 3 ^ 40 * 3895184 * 2
def baseEnd_3895184 : Nat := 1333401086468528872257587

theorem tailTrace_3895184 : CollatzResearch.WordTrace tailWord_3895184 prefixEnd_3895184 1333401086468528872257587 := by
  unfold tailWord_3895184
  simp only [CollatzResearch.WordTrace]
  refine ⟨71034515960210543654746303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94712687946947391539661737 71034515960210543654746303)
  ·
    refine ⟨106551773940315815482119455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71034515960210543654746303 106551773940315815482119455)
    ·
      refine ⟨159827660910473723223179183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106551773940315815482119455 159827660910473723223179183)
      ·
        refine ⟨239741491365710584834768775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159827660910473723223179183 239741491365710584834768775)
        ·
          refine ⟨359612237048565877252153163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239741491365710584834768775 359612237048565877252153163)
          ·
            refine ⟨539418355572848815878229745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359612237048565877252153163 539418355572848815878229745)
            ·
              refine ⟨404563766679636611908672309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539418355572848815878229745 404563766679636611908672309)
              ·
                refine ⟨37927853126215932366438029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404563766679636611908672309 37927853126215932366438029)
                ·
                  refine ⟨14222944922330974637414261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37927853126215932366438029 14222944922330974637414261)
                  ·
                    refine ⟨1333401086468528872257587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14222944922330974637414261 1333401086468528872257587)
                    ·
                      rfl

theorem cell22_3895184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_3895184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895184 prefixEnd_3895184 := by exact prefixLift 3895184
  have htrace : WordTrace (prefixWord ++ tailWord_3895184) baseStart_3895184 baseEnd_3895184 := by
    simpa [prefixWord, tailWord_3895184, baseEnd_3895184] using wordTrace_append hprefix tailTrace_3895184
  have hstable : (prefixWord ++ tailWord_3895184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895184).length < 2 ^ (prefixWord ++ tailWord_3895184).sum := by decide
  have hdescent : baseEnd_3895184 < baseStart_3895184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895220 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_3895220 : Nat := 118140960795 + 3895220 * 2 ^ 59
def prefixEnd_3895220 : Nat := 4983230072969 + 3 ^ 40 * 3895220 * 2
def baseEnd_3895220 : Nat := 444471136668078926119159

theorem tailTrace_3895220 : CollatzResearch.WordTrace tailWord_3895220 prefixEnd_3895220 444471136668078926119159 := by
  unfold tailWord_3895220
  simp only [CollatzResearch.WordTrace]
  refine ⟨71035172474145332728901557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94713563298860443638535409 71035172474145332728901557)
  ·
    refine ⟨6659547419451124943334521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71035172474145332728901557 6659547419451124943334521)
    ·
      refine ⟨4994660564588343707500891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6659547419451124943334521 4994660564588343707500891)
      ·
        refine ⟨7491990846882515561251337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4994660564588343707500891 7491990846882515561251337)
        ·
          refine ⟨5618993135161886670938503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7491990846882515561251337 5618993135161886670938503)
          ·
            refine ⟨8428489702742830006407755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5618993135161886670938503 8428489702742830006407755)
            ·
              refine ⟨12642734554114245009611633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8428489702742830006407755 12642734554114245009611633)
              ·
                refine ⟨9482050915585683757208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12642734554114245009611633 9482050915585683757208725)
                ·
                  refine ⟨444471136668078926119159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9482050915585683757208725 444471136668078926119159)
                  ·
                    rfl

theorem cell22_3895220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_3895220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895220 prefixEnd_3895220 := by exact prefixLift 3895220
  have htrace : WordTrace (prefixWord ++ tailWord_3895220) baseStart_3895220 baseEnd_3895220 := by
    simpa [prefixWord, tailWord_3895220, baseEnd_3895220] using wordTrace_append hprefix tailTrace_3895220
  have hstable : (prefixWord ++ tailWord_3895220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895220).length < 2 ^ (prefixWord ++ tailWord_3895220).sum := by decide
  have hdescent : baseEnd_3895220 < baseStart_3895220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895231 : List Nat := [1, 1, 2, 2, 2, 1, 7, 6]
def baseStart_3895231 : Nat := 118140960795 + 3895231 * 2 ^ 59
def prefixEnd_3895231 : Nat := 4983230072969 + 3 ^ 40 * 3895231 * 2
def baseEnd_3895231 : Nat := 148157463947670712925827

theorem tailTrace_3895231 : CollatzResearch.WordTrace tailWord_3895231 prefixEnd_3895231 148157463947670712925827 := by
  unfold tailWord_3895231
  simp only [CollatzResearch.WordTrace]
  refine ⟨142070746151250814336453547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94713830767500542890969031 142070746151250814336453547)
  ·
    refine ⟨213106119226876221504680321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142070746151250814336453547 213106119226876221504680321)
    ·
      refine ⟨159829589420157166128510241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213106119226876221504680321 159829589420157166128510241)
      ·
        refine ⟨119872192065117874596382681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159829589420157166128510241 119872192065117874596382681)
        ·
          refine ⟨89904144048838405947287011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119872192065117874596382681 89904144048838405947287011)
          ·
            refine ⟨134856216073257608920930517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89904144048838405947287011 134856216073257608920930517)
            ·
              refine ⟨3160692564216975209084309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134856216073257608920930517 3160692564216975209084309)
              ·
                refine ⟨148157463947670712925827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3160692564216975209084309 148157463947670712925827)
                ·
                  rfl

theorem cell22_3895231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 6].length) (baseStart_3895231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895231 prefixEnd_3895231 := by exact prefixLift 3895231
  have htrace : WordTrace (prefixWord ++ tailWord_3895231) baseStart_3895231 baseEnd_3895231 := by
    simpa [prefixWord, tailWord_3895231, baseEnd_3895231] using wordTrace_append hprefix tailTrace_3895231
  have hstable : (prefixWord ++ tailWord_3895231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895231).length < 2 ^ (prefixWord ++ tailWord_3895231).sum := by decide
  have hdescent : baseEnd_3895231 < baseStart_3895231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895263 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 3, 3]
def baseStart_3895263 : Nat := 118140960795 + 3895263 * 2 ^ 59
def prefixEnd_3895263 : Nat := 4983230072969 + 3 ^ 40 * 3895263 * 2
def baseEnd_3895263 : Nat := 1333428129782998999532345

theorem tailTrace_3895263 : CollatzResearch.WordTrace tailWord_3895263 prefixEnd_3895263 1333428129782998999532345 := by
  unfold tailWord_3895263
  simp only [CollatzResearch.WordTrace]
  refine ⟨142071913287134883801618443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94714608858089922534412295 142071913287134883801618443)
  ·
    refine ⟨213107869930702325702427665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142071913287134883801618443 213107869930702325702427665)
    ·
      refine ⟨159830902448026744276820749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213107869930702325702427665 159830902448026744276820749)
      ·
        refine ⟨59936588418010029103807781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159830902448026744276820749 59936588418010029103807781)
        ·
          refine ⟨11238110328376880456963959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59936588418010029103807781 11238110328376880456963959)
          ·
            refine ⟨16857165492565320685445939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11238110328376880456963959 16857165492565320685445939)
            ·
              refine ⟨25285748238847981028168909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16857165492565320685445939 25285748238847981028168909)
              ·
                refine ⟨9482155589567992885563341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25285748238847981028168909 9482155589567992885563341)
                ·
                  refine ⟨3555808346087997332086253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9482155589567992885563341 3555808346087997332086253)
                  ·
                    refine ⟨1333428129782998999532345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555808346087997332086253 1333428129782998999532345)
                    ·
                      rfl

theorem cell22_3895263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_3895263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895263 prefixEnd_3895263 := by exact prefixLift 3895263
  have htrace : WordTrace (prefixWord ++ tailWord_3895263) baseStart_3895263 baseEnd_3895263 := by
    simpa [prefixWord, tailWord_3895263, baseEnd_3895263] using wordTrace_append hprefix tailTrace_3895263
  have hstable : (prefixWord ++ tailWord_3895263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895263).length < 2 ^ (prefixWord ++ tailWord_3895263).sum := by decide
  have hdescent : baseEnd_3895263 < baseStart_3895263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895276 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 5]
def baseStart_3895276 : Nat := 118140960795 + 3895276 * 2 ^ 59
def prefixEnd_3895276 : Nat := 4983230072969 + 3 ^ 40 * 3895276 * 2
def baseEnd_3895276 : Nat := 444477526649557099652435

theorem tailTrace_3895276 : CollatzResearch.WordTrace tailWord_3895276 prefixEnd_3895276 444477526649557099652435 := by
  unfold tailWord_3895276
  simp only [CollatzResearch.WordTrace]
  refine ⟨71036193718043893510920841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94714924957391858014561121 71036193718043893510920841)
  ·
    refine ⟨53277145288532920133190631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71036193718043893510920841 53277145288532920133190631)
    ·
      refine ⟨79915717932799380199785947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53277145288532920133190631 79915717932799380199785947)
      ·
        refine ⟨119873576899199070299678921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79915717932799380199785947 119873576899199070299678921)
        ·
          refine ⟨89905182674399302724759191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119873576899199070299678921 89905182674399302724759191)
          ·
            refine ⟨134857774011598954087138787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89905182674399302724759191 134857774011598954087138787)
            ·
              refine ⟨202286661017398431130708181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134857774011598954087138787 202286661017398431130708181)
              ·
                refine ⟨4741093617595275729625973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 202286661017398431130708181 4741093617595275729625973)
                ·
                  refine ⟨444477526649557099652435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741093617595275729625973 444477526649557099652435)
                  ·
                    rfl

theorem cell22_3895276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_3895276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895276 prefixEnd_3895276 := by exact prefixLift 3895276
  have htrace : WordTrace (prefixWord ++ tailWord_3895276) baseStart_3895276 baseEnd_3895276 := by
    simpa [prefixWord, tailWord_3895276, baseEnd_3895276] using wordTrace_append hprefix tailTrace_3895276
  have hstable : (prefixWord ++ tailWord_3895276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895276).length < 2 ^ (prefixWord ++ tailWord_3895276).sum := by decide
  have hdescent : baseEnd_3895276 < baseStart_3895276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895351 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_3895351 : Nat := 118140960795 + 3895351 * 2 ^ 59
def prefixEnd_3895351 : Nat := 4983230072969 + 3 ^ 40 * 3895351 * 2
def baseEnd_3895351 : Nat := 1333458253981396103332075

theorem tailTrace_3895351 : CollatzResearch.WordTrace tailWord_3895351 prefixEnd_3895351 1333458253981396103332075 := by
  unfold tailWord_3895351
  simp only [CollatzResearch.WordTrace]
  refine ⟨142075122910816074830821907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94716748607210716553881271 142075122910816074830821907)
  ·
    refine ⟨213112684366224112246232861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142075122910816074830821907 213112684366224112246232861)
    ·
      refine ⟨79917256637334042092337323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213112684366224112246232861 79917256637334042092337323)
      ·
        refine ⟨119875884956001063138505985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79917256637334042092337323 119875884956001063138505985)
        ·
          refine ⟨89906913717000797353879489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119875884956001063138505985 89906913717000797353879489)
          ·
            refine ⟨67430185287750598015409617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89906913717000797353879489 67430185287750598015409617)
            ·
              refine ⟨50572638965812948511557213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67430185287750598015409617 50572638965812948511557213)
              ·
                refine ⟨18964739612179855691833955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50572638965812948511557213 18964739612179855691833955)
                ·
                  refine ⟨28447109418269783537750933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18964739612179855691833955 28447109418269783537750933)
                  ·
                    refine ⟨1333458253981396103332075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28447109418269783537750933 1333458253981396103332075)
                    ·
                      rfl

theorem cell22_3895351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_3895351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895351 prefixEnd_3895351 := by exact prefixLift 3895351
  have htrace : WordTrace (prefixWord ++ tailWord_3895351) baseStart_3895351 baseEnd_3895351 := by
    simpa [prefixWord, tailWord_3895351, baseEnd_3895351] using wordTrace_append hprefix tailTrace_3895351
  have hstable : (prefixWord ++ tailWord_3895351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895351).length < 2 ^ (prefixWord ++ tailWord_3895351).sum := by decide
  have hdescent : baseEnd_3895351 < baseStart_3895351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895402 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_3895402 : Nat := 118140960795 + 3895402 * 2 ^ 59
def prefixEnd_3895402 : Nat := 4983230072969 + 3 ^ 40 * 3895402 * 2
def baseEnd_3895402 : Nat := 1333475712323648970306919

theorem tailTrace_3895402 : CollatzResearch.WordTrace tailWord_3895402 prefixEnd_3895402 1333475712323648970306919 := by
  unfold tailWord_3895402
  simp only [CollatzResearch.WordTrace]
  refine ⟨35519245758407827635232115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94717988689087540360618973 35519245758407827635232115)
  ·
    refine ⟨53278868637611741452848173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35519245758407827635232115 53278868637611741452848173)
    ·
      refine ⟨19979575739104403044818065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53278868637611741452848173 19979575739104403044818065)
      ·
        refine ⟨14984681804328302283613549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19979575739104403044818065 14984681804328302283613549)
        ·
          refine ⟨5619255676623113356355081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14984681804328302283613549 5619255676623113356355081)
          ·
            refine ⟨4214441757467335017266311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5619255676623113356355081 4214441757467335017266311)
            ·
              refine ⟨6321662636201002525899467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4214441757467335017266311 6321662636201002525899467)
              ·
                refine ⟨9482493954301503788849201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321662636201002525899467 9482493954301503788849201)
                ·
                  refine ⟨7111870465726127841636901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9482493954301503788849201 7111870465726127841636901)
                  ·
                    refine ⟨1333475712323648970306919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7111870465726127841636901 1333475712323648970306919)
                    ·
                      rfl

theorem cell22_3895402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_3895402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895402 prefixEnd_3895402 := by exact prefixLift 3895402
  have htrace : WordTrace (prefixWord ++ tailWord_3895402) baseStart_3895402 baseEnd_3895402 := by
    simpa [prefixWord, tailWord_3895402, baseEnd_3895402] using wordTrace_append hprefix tailTrace_3895402
  have hstable : (prefixWord ++ tailWord_3895402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895402).length < 2 ^ (prefixWord ++ tailWord_3895402).sum := by decide
  have hdescent : baseEnd_3895402 < baseStart_3895402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895428 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3895428 : Nat := 118140960795 + 3895428 * 2 ^ 59
def prefixEnd_3895428 : Nat := 4983230072969 + 3 ^ 40 * 3895428 * 2
def baseEnd_3895428 : Nat := 444494870884997856385613

theorem tailTrace_3895428 : CollatzResearch.WordTrace tailWord_3895428 prefixEnd_3895428 444494870884997856385613 := by
  unfold tailWord_3895428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71038965665768558490687469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94718620887691411320916625 71038965665768558490687469)
  ·
    refine ⟨26639612124663209434007801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71038965665768558490687469 26639612124663209434007801)
    ·
      refine ⟨19979709093497407075505851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26639612124663209434007801 19979709093497407075505851)
      ·
        refine ⟨29969563640246110613258777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19979709093497407075505851 29969563640246110613258777)
        ·
          refine ⟨22477172730184582959944083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29969563640246110613258777 22477172730184582959944083)
          ·
            refine ⟨33715759095276874439916125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22477172730184582959944083 33715759095276874439916125)
            ·
              refine ⟨12643409660728827914968547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33715759095276874439916125 12643409660728827914968547)
              ·
                refine ⟨18965114491093241872452821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12643409660728827914968547 18965114491093241872452821)
                ·
                  refine ⟨444494870884997856385613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18965114491093241872452821 444494870884997856385613)
                  ·
                    rfl

theorem cell22_3895428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3895428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895428 prefixEnd_3895428 := by exact prefixLift 3895428
  have htrace : WordTrace (prefixWord ++ tailWord_3895428) baseStart_3895428 baseEnd_3895428 := by
    simpa [prefixWord, tailWord_3895428, baseEnd_3895428] using wordTrace_append hprefix tailTrace_3895428
  have hstable : (prefixWord ++ tailWord_3895428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895428).length < 2 ^ (prefixWord ++ tailWord_3895428).sum := by decide
  have hdescent : baseEnd_3895428 < baseStart_3895428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895432 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 3, 3]
def baseStart_3895432 : Nat := 118140960795 + 3895432 * 2 ^ 59
def prefixEnd_3895432 : Nat := 4983230072969 + 3 ^ 40 * 3895432 * 2
def baseEnd_3895432 : Nat := 1333485981936738892056827

theorem tailTrace_3895432 : CollatzResearch.WordTrace tailWord_3895432 prefixEnd_3895432 1333485981936738892056827 := by
  unfold tailWord_3895432
  simp only [CollatzResearch.WordTrace]
  refine ⟨71039038611761312832260275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94718718149015083776347033 71039038611761312832260275)
  ·
    refine ⟨106558557917641969248390413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71039038611761312832260275 106558557917641969248390413)
    ·
      refine ⟨39959459219115738468146405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106558557917641969248390413 39959459219115738468146405)
      ·
        refine ⟨7492398603584200962777451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39959459219115738468146405 7492398603584200962777451)
        ·
          refine ⟨11238597905376301444166177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7492398603584200962777451 11238597905376301444166177)
          ·
            refine ⟨8428948429032226083124633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11238597905376301444166177 8428948429032226083124633)
            ·
              refine ⟨6321711321774169562343475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8428948429032226083124633 6321711321774169562343475)
              ·
                refine ⟨9482566982661254343515213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6321711321774169562343475 9482566982661254343515213)
                ·
                  refine ⟨3555962618497970378818205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9482566982661254343515213 3555962618497970378818205)
                  ·
                    refine ⟨1333485981936738892056827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3555962618497970378818205 1333485981936738892056827)
                    ·
                      rfl

theorem cell22_3895432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_3895432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895432 prefixEnd_3895432 := by exact prefixLift 3895432
  have htrace : WordTrace (prefixWord ++ tailWord_3895432) baseStart_3895432 baseEnd_3895432 := by
    simpa [prefixWord, tailWord_3895432, baseEnd_3895432] using wordTrace_append hprefix tailTrace_3895432
  have hstable : (prefixWord ++ tailWord_3895432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895432).length < 2 ^ (prefixWord ++ tailWord_3895432).sum := by decide
  have hdescent : baseEnd_3895432 < baseStart_3895432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895445 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 5]
def baseStart_3895445 : Nat := 118140960795 + 3895445 * 2 ^ 59
def prefixEnd_3895445 : Nat := 4983230072969 + 3 ^ 40 * 3895445 * 2
def baseEnd_3895445 : Nat := 444496810700803730493929

theorem tailTrace_3895445 : CollatzResearch.WordTrace tailWord_3895445 prefixEnd_3895445 444496810700803730493929 := by
  unfold tailWord_3895445
  simp only [CollatzResearch.WordTrace]
  refine ⟨142078551372475528884743789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94719034248317019256495859 142078551372475528884743789)
  ·
    refine ⟨53279456764678323331778921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142078551372475528884743789 53279456764678323331778921)
    ·
      refine ⟨39959592573508742498834191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53279456764678323331778921 39959592573508742498834191)
      ·
        refine ⟨59939388860263113748251287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39959592573508742498834191 59939388860263113748251287)
        ·
          refine ⟨89909083290394670622376931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59939388860263113748251287 89909083290394670622376931)
          ·
            refine ⟨134863624935592005933565397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89909083290394670622376931 134863624935592005933565397)
            ·
              refine ⟨3160866209427937639067939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134863624935592005933565397 3160866209427937639067939)
              ·
                refine ⟨4741299314141906458601909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3160866209427937639067939 4741299314141906458601909)
                ·
                  refine ⟨444496810700803730493929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4741299314141906458601909 444496810700803730493929)
                  ·
                    rfl

theorem cell22_3895445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_3895445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895445 prefixEnd_3895445 := by exact prefixLift 3895445
  have htrace : WordTrace (prefixWord ++ tailWord_3895445) baseStart_3895445 baseEnd_3895445 := by
    simpa [prefixWord, tailWord_3895445, baseEnd_3895445] using wordTrace_append hprefix tailTrace_3895445
  have hstable : (prefixWord ++ tailWord_3895445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895445).length < 2 ^ (prefixWord ++ tailWord_3895445).sum := by decide
  have hdescent : baseEnd_3895445 < baseStart_3895445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3895503 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_3895503 : Nat := 118140960795 + 3895503 * 2 ^ 59
def prefixEnd_3895503 : Nat := 4983230072969 + 3 ^ 40 * 3895503 * 2
def baseEnd_3895503 : Nat := 1333510286687718373531609

theorem tailTrace_3895503 : CollatzResearch.WordTrace tailWord_3895503 prefixEnd_3895503 1333510286687718373531609 := by
  unfold tailWord_3895503
  simp only [CollatzResearch.WordTrace]
  refine ⟨142080666806265404790355163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94720444537510269860236775 142080666806265404790355163)
  ·
    refine ⟨213121000209398107185532745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142080666806265404790355163 213121000209398107185532745)
    ·
      refine ⟨159840750157048580389149559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213121000209398107185532745 159840750157048580389149559)
      ·
        refine ⟨239761125235572870583724339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159840750157048580389149559 239761125235572870583724339)
        ·
          refine ⟨359641687853359305875586509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239761125235572870583724339 359641687853359305875586509)
          ·
            refine ⟨134865632945009739703344941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 359641687853359305875586509 134865632945009739703344941)
            ·
              refine ⟨50574612354378652388754353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134865632945009739703344941 50574612354378652388754353)
              ·
                refine ⟨37930959265783989291565765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50574612354378652388754353 37930959265783989291565765)
                ·
                  refine ⟨7112054862334497992168581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37930959265783989291565765 7112054862334497992168581)
                  ·
                    refine ⟨1333510286687718373531609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7112054862334497992168581 1333510286687718373531609)
                    ·
                      rfl

theorem cell22_3895503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_3895503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3895503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3895503 prefixEnd_3895503 := by exact prefixLift 3895503
  have htrace : WordTrace (prefixWord ++ tailWord_3895503) baseStart_3895503 baseEnd_3895503 := by
    simpa [prefixWord, tailWord_3895503, baseEnd_3895503] using wordTrace_append hprefix tailTrace_3895503
  have hstable : (prefixWord ++ tailWord_3895503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3895503).length < 2 ^ (prefixWord ++ tailWord_3895503).sum := by decide
  have hdescent : baseEnd_3895503 < baseStart_3895503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3895503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
