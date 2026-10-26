import V185TrunkScan22Chunk235

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2104327 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 2, 3]
def baseStart_2104327 : Nat := 118140960795 + 2104327 * 2 ^ 59
def prefixEnd_2104327 : Nat := 4983230072969 + 3 ^ 40 * 2104327 * 2
def baseEnd_2104327 : Nat := 720354136822595696423255

theorem tailTrace_2104327 : CollatzResearch.WordTrace tailWord_2104327 prefixEnd_2104327 720354136822595696423255 := by
  unfold tailWord_2104327
  simp only [CollatzResearch.WordTrace]
  refine ⟨76751111047390144284175235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51167407364926762856116823 76751111047390144284175235)
  ·
    refine ⟨115126666571085216426262853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76751111047390144284175235 115126666571085216426262853)
    ·
      refine ⟨21586249982078478079924285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115126666571085216426262853 21586249982078478079924285)
      ·
        refine ⟨8094843743279429279971607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21586249982078478079924285 8094843743279429279971607)
        ·
          refine ⟨12142265614919143919957411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8094843743279429279971607 12142265614919143919957411)
          ·
            refine ⟨18213398422378715879936117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12142265614919143919957411 18213398422378715879936117)
            ·
              refine ⟨1707506102098004613744011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18213398422378715879936117 1707506102098004613744011)
              ·
                refine ⟨2561259153147006920616017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707506102098004613744011 2561259153147006920616017)
                ·
                  refine ⟨1920944364860255190462013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561259153147006920616017 1920944364860255190462013)
                  ·
                    refine ⟨720354136822595696423255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1920944364860255190462013 720354136822595696423255)
                    ·
                      rfl

theorem cell22_2104327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_2104327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104327 prefixEnd_2104327 := by exact prefixLift 2104327
  have htrace : WordTrace (prefixWord ++ tailWord_2104327) baseStart_2104327 baseEnd_2104327 := by
    simpa [prefixWord, tailWord_2104327, baseEnd_2104327] using wordTrace_append hprefix tailTrace_2104327
  have hstable : (prefixWord ++ tailWord_2104327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104327).length < 2 ^ (prefixWord ++ tailWord_2104327).sum := by decide
  have hdescent : baseEnd_2104327 < baseStart_2104327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104368 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_2104368 : Nat := 118140960795 + 2104368 * 2 ^ 59
def prefixEnd_2104368 : Nat := 4983230072969 + 3 ^ 40 * 2104368 * 2
def baseEnd_2104368 : Nat := 240122723986828418716043

theorem tailTrace_2104368 : CollatzResearch.WordTrace tailWord_2104368 prefixEnd_2104368 240122723986828418716043 := by
  unfold tailWord_2104368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38376303220120804143208879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51168404293494405524278505 38376303220120804143208879)
  ·
    refine ⟨57564454830181206214813319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38376303220120804143208879 57564454830181206214813319)
    ·
      refine ⟨86346682245271809322219979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57564454830181206214813319 86346682245271809322219979)
      ·
        refine ⟨129520023367907713983329969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86346682245271809322219979 129520023367907713983329969)
        ·
          refine ⟨97140017525930785487497477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129520023367907713983329969 97140017525930785487497477)
          ·
            refine ⟨18213753286112022278905777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97140017525930785487497477 18213753286112022278905777)
            ·
              refine ⟨13660314964584016709179333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18213753286112022278905777 13660314964584016709179333)
              ·
                refine ⟨2561309055859503132971125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13660314964584016709179333 2561309055859503132971125)
                ·
                  refine ⟨240122723986828418716043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561309055859503132971125 240122723986828418716043)
                  ·
                    rfl

theorem cell22_2104368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_2104368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104368 prefixEnd_2104368 := by exact prefixLift 2104368
  have htrace : WordTrace (prefixWord ++ tailWord_2104368) baseStart_2104368 baseEnd_2104368 := by
    simpa [prefixWord, tailWord_2104368, baseEnd_2104368] using wordTrace_append hprefix tailTrace_2104368
  have hstable : (prefixWord ++ tailWord_2104368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104368).length < 2 ^ (prefixWord ++ tailWord_2104368).sum := by decide
  have hdescent : baseEnd_2104368 < baseStart_2104368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104428 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 3, 5]
def baseStart_2104428 : Nat := 118140960795 + 2104428 * 2 ^ 59
def prefixEnd_2104428 : Nat := 4983230072969 + 3 ^ 40 * 2104428 * 2
def baseEnd_2104428 : Nat := 720388711186665099647945

theorem tailTrace_2104428 : CollatzResearch.WordTrace tailWord_2104428 prefixEnd_2104428 720388711186665099647945 := by
  unfold tailWord_2104428
  simp only [CollatzResearch.WordTrace]
  refine ⟨38377397410012119266800969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51169863213349492355734625 38377397410012119266800969)
  ·
    refine ⟨28783048057509089450100727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38377397410012119266800969 28783048057509089450100727)
    ·
      refine ⟨43174572086263634175151091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28783048057509089450100727 43174572086263634175151091)
      ·
        refine ⟨64761858129395451262726637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43174572086263634175151091 64761858129395451262726637)
        ·
          refine ⟨24285696798523294223522489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64761858129395451262726637 24285696798523294223522489)
          ·
            refine ⟨18214272598892470667641867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24285696798523294223522489 18214272598892470667641867)
            ·
              refine ⟨27321408898338706001462801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18214272598892470667641867 27321408898338706001462801)
              ·
                refine ⟨20491056673754029501097101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27321408898338706001462801 20491056673754029501097101)
                ·
                  refine ⟨7684146252657761062911413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20491056673754029501097101 7684146252657761062911413)
                  ·
                    refine ⟨720388711186665099647945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7684146252657761062911413 720388711186665099647945)
                    ·
                      rfl

theorem cell22_2104428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_2104428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104428 prefixEnd_2104428 := by exact prefixLift 2104428
  have htrace : WordTrace (prefixWord ++ tailWord_2104428) baseStart_2104428 baseEnd_2104428 := by
    simpa [prefixWord, tailWord_2104428, baseEnd_2104428] using wordTrace_append hprefix tailTrace_2104428
  have hstable : (prefixWord ++ tailWord_2104428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104428).length < 2 ^ (prefixWord ++ tailWord_2104428).sum := by decide
  have hdescent : baseEnd_2104428 < baseStart_2104428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104443 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_2104443 : Nat := 118140960795 + 2104443 * 2 ^ 59
def prefixEnd_2104443 : Nat := 4983230072969 + 3 ^ 40 * 2104443 * 2
def baseEnd_2104443 : Nat := 720393845993210060522899

theorem tailTrace_2104443 : CollatzResearch.WordTrace tailWord_2104443 prefixEnd_2104443 720393845993210060522899 := by
  unfold tailWord_2104443
  simp only [CollatzResearch.WordTrace]
  refine ⟨76755341914969896095397983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51170227943313264063598655 76755341914969896095397983)
  ·
    refine ⟨115133012872454844143096975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76755341914969896095397983 115133012872454844143096975)
    ·
      refine ⟨172699519308682266214645463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115133012872454844143096975 172699519308682266214645463)
      ·
        refine ⟨259049278963023399321968195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172699519308682266214645463 259049278963023399321968195)
        ·
          refine ⟨388573918444535098982952293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259049278963023399321968195 388573918444535098982952293)
          ·
            refine ⟨72857609708350331059303555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 388573918444535098982952293 72857609708350331059303555)
            ·
              refine ⟨109286414562525496588955333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72857609708350331059303555 109286414562525496588955333)
              ·
                refine ⟨20491202730473530610429125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109286414562525496588955333 20491202730473530610429125)
                ·
                  refine ⟨3842100511963786989455461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20491202730473530610429125 3842100511963786989455461)
                  ·
                    refine ⟨720393845993210060522899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842100511963786989455461 720393845993210060522899)
                    ·
                      rfl

theorem cell22_2104443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_2104443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104443 prefixEnd_2104443 := by exact prefixLift 2104443
  have htrace : WordTrace (prefixWord ++ tailWord_2104443) baseStart_2104443 baseEnd_2104443 := by
    simpa [prefixWord, tailWord_2104443, baseEnd_2104443] using wordTrace_append hprefix tailTrace_2104443
  have hstable : (prefixWord ++ tailWord_2104443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104443).length < 2 ^ (prefixWord ++ tailWord_2104443).sum := by decide
  have hdescent : baseEnd_2104443 < baseStart_2104443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104445 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_2104445 : Nat := 118140960795 + 2104445 * 2 ^ 59
def prefixEnd_2104445 : Nat := 4983230072969 + 3 ^ 40 * 2104445 * 2
def baseEnd_2104445 : Nat := 720394530634082721972893

theorem tailTrace_2104445 : CollatzResearch.WordTrace tailWord_2104445 prefixEnd_2104445 720394530634082721972893 := by
  unfold tailWord_2104445
  simp only [CollatzResearch.WordTrace]
  refine ⟨76755414860962650436970789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51170276573975100291313859 76755414860962650436970789)
  ·
    refine ⟨14391640286430496956932023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76755414860962650436970789 14391640286430496956932023)
    ·
      refine ⟨21587460429645745435398035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14391640286430496956932023 21587460429645745435398035)
      ·
        refine ⟨32381190644468618153097053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21587460429645745435398035 32381190644468618153097053)
        ·
          refine ⟨12142946491675731807411395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32381190644468618153097053 12142946491675731807411395)
          ·
            refine ⟨18214419737513597711117093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12142946491675731807411395 18214419737513597711117093)
            ·
              refine ⟨3415203700783799570834455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18214419737513597711117093 3415203700783799570834455)
              ·
                refine ⟨5122805551175699356251683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415203700783799570834455 5122805551175699356251683)
                ·
                  refine ⟨7684208326763549034377525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5122805551175699356251683 7684208326763549034377525)
                  ·
                    refine ⟨720394530634082721972893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7684208326763549034377525 720394530634082721972893)
                    ·
                      rfl

theorem cell22_2104445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_2104445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104445 prefixEnd_2104445 := by exact prefixLift 2104445
  have htrace : WordTrace (prefixWord ++ tailWord_2104445) baseStart_2104445 baseEnd_2104445 := by
    simpa [prefixWord, tailWord_2104445, baseEnd_2104445] using wordTrace_append hprefix tailTrace_2104445
  have hstable : (prefixWord ++ tailWord_2104445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104445).length < 2 ^ (prefixWord ++ tailWord_2104445).sum := by decide
  have hdescent : baseEnd_2104445 < baseStart_2104445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104541 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2104541 : Nat := 118140960795 + 2104541 * 2 ^ 59
def prefixEnd_2104541 : Nat := 4983230072969 + 3 ^ 40 * 2104541 * 2
def baseEnd_2104541 : Nat := 720427393395970471572599

theorem tailTrace_2104541 : CollatzResearch.WordTrace tailWord_2104541 prefixEnd_2104541 720427393395970471572599 := by
  unfold tailWord_2104541
  simp only [CollatzResearch.WordTrace]
  refine ⟨76758916268614858832465477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51172610845743239221643651 76758916268614858832465477)
  ·
    refine ⟨14392296800365286031087277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76758916268614858832465477 14392296800365286031087277)
    ·
      refine ⟨5397111300136982261657729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14392296800365286031087277 5397111300136982261657729)
      ·
        refine ⟨4047833475102736696243297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5397111300136982261657729 4047833475102736696243297)
        ·
          refine ⟨3035875106327052522182473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4047833475102736696243297 3035875106327052522182473)
          ·
            refine ⟨2276906329745289391636855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035875106327052522182473 2276906329745289391636855)
            ·
              refine ⟨3415359494617934087455283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276906329745289391636855 3415359494617934087455283)
              ·
                refine ⟨5123039241926901131182925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415359494617934087455283 5123039241926901131182925)
                ·
                  refine ⟨1921139715722587924193597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5123039241926901131182925 1921139715722587924193597)
                  ·
                    refine ⟨720427393395970471572599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921139715722587924193597 720427393395970471572599)
                    ·
                      rfl

theorem cell22_2104541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2104541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104541 prefixEnd_2104541 := by exact prefixLift 2104541
  have htrace : WordTrace (prefixWord ++ tailWord_2104541) baseStart_2104541 baseEnd_2104541 := by
    simpa [prefixWord, tailWord_2104541, baseEnd_2104541] using wordTrace_append hprefix tailTrace_2104541
  have hstable : (prefixWord ++ tailWord_2104541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104541).length < 2 ^ (prefixWord ++ tailWord_2104541).sum := by decide
  have hdescent : baseEnd_2104541 < baseStart_2104541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104554 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_2104554 : Nat := 118140960795 + 2104554 * 2 ^ 59
def prefixEnd_2104554 : Nat := 4983230072969 + 3 ^ 40 * 2104554 * 2
def baseEnd_2104554 : Nat := 240143947853880923665853

theorem tailTrace_2104554 : CollatzResearch.WordTrace tailWord_2104554 prefixEnd_2104554 240143947853880923665853 := by
  unfold tailWord_2104554
  simp only [CollatzResearch.WordTrace]
  refine ⟨19189847604391940513172179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51172926945045174701792477 19189847604391940513172179)
  ·
    refine ⟨28784771406587910769758269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19189847604391940513172179 28784771406587910769758269)
    ·
      refine ⟨10794289277470466538659351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28784771406587910769758269 10794289277470466538659351)
      ·
        refine ⟨16191433916205699807989027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794289277470466538659351 16191433916205699807989027)
        ·
          refine ⟨24287150874308549711983541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16191433916205699807989027 24287150874308549711983541)
          ·
            refine ⟨2276920394466426535498457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24287150874308549711983541 2276920394466426535498457)
            ·
              refine ⟨1707690295849819901623843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2276920394466426535498457 1707690295849819901623843)
              ·
                refine ⟨2561535443774729852435765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707690295849819901623843 2561535443774729852435765)
                ·
                  refine ⟨240143947853880923665853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561535443774729852435765 240143947853880923665853)
                  ·
                    rfl

theorem cell22_2104554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_2104554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104554 prefixEnd_2104554 := by exact prefixLift 2104554
  have htrace : WordTrace (prefixWord ++ tailWord_2104554) baseStart_2104554 baseEnd_2104554 := by
    simpa [prefixWord, tailWord_2104554, baseEnd_2104554] using wordTrace_append hprefix tailTrace_2104554
  have hstable : (prefixWord ++ tailWord_2104554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104554).length < 2 ^ (prefixWord ++ tailWord_2104554).sum := by decide
  have hdescent : baseEnd_2104554 < baseStart_2104554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104627 : List Nat := [1, 1, 1, 2, 5, 3, 3, 6]
def baseStart_2104627 : Nat := 118140960795 + 2104627 * 2 ^ 59
def prefixEnd_2104627 : Nat := 4983230072969 + 3 ^ 40 * 2104627 * 2
def baseEnd_2104627 : Nat := 80050759217054990435815

theorem tailTrace_2104627 : CollatzResearch.WordTrace tailWord_2104627 prefixEnd_2104627 80050759217054990435815 := by
  unfold tailWord_2104627
  simp only [CollatzResearch.WordTrace]
  refine ⟨76762052946303295520096135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51174701964202197013397423 76762052946303295520096135)
  ·
    refine ⟨115143079419454943280144203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76762052946303295520096135 115143079419454943280144203)
    ·
      refine ⟨172714619129182414920216305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115143079419454943280144203 172714619129182414920216305)
      ·
        refine ⟨129535964346886811190162229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172714619129182414920216305 129535964346886811190162229)
        ·
          refine ⟨12143996657520638549077709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129535964346886811190162229 12143996657520638549077709)
          ·
            refine ⟨4553998746570239455904141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12143996657520638549077709 4553998746570239455904141)
            ·
              refine ⟨1707749529963839795964053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4553998746570239455904141 1707749529963839795964053)
              ·
                refine ⟨80050759217054990435815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1707749529963839795964053 80050759217054990435815)
                ·
                  rfl

theorem cell22_2104627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 3, 6].length) (baseStart_2104627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104627 prefixEnd_2104627 := by exact prefixLift 2104627
  have htrace : WordTrace (prefixWord ++ tailWord_2104627) baseStart_2104627 baseEnd_2104627 := by
    simpa [prefixWord, tailWord_2104627, baseEnd_2104627] using wordTrace_append hprefix tailTrace_2104627
  have hstable : (prefixWord ++ tailWord_2104627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104627).length < 2 ^ (prefixWord ++ tailWord_2104627).sum := by decide
  have hdescent : baseEnd_2104627 < baseStart_2104627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104629 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_2104629 : Nat := 118140960795 + 2104629 * 2 ^ 59
def prefixEnd_2104629 : Nat := 4983230072969 + 3 ^ 40 * 2104629 * 2
def baseEnd_2104629 : Nat := 720457517594367575372329

theorem tailTrace_2104629 : CollatzResearch.WordTrace tailWord_2104629 prefixEnd_2104629 720457517594367575372329 := by
  unfold tailWord_2104629
  simp only [CollatzResearch.WordTrace]
  refine ⟨76762125892296049861668941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51174750594864033241112627 76762125892296049861668941)
  ·
    refine ⟨28785797209611018698125853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76762125892296049861668941 28785797209611018698125853)
    ·
      refine ⟨10794673953604132011797195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28785797209611018698125853 10794673953604132011797195)
      ·
        refine ⟨16192010930406198017695793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10794673953604132011797195 16192010930406198017695793)
        ·
          refine ⟨12144008197804648513271845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16192010930406198017695793 12144008197804648513271845)
          ·
            refine ⟨2277001537088371596238471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12144008197804648513271845 2277001537088371596238471)
            ·
              refine ⟨3415502305632557394357707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277001537088371596238471 3415502305632557394357707)
              ·
                refine ⟨5123253458448836091536561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415502305632557394357707 5123253458448836091536561)
                ·
                  refine ⟨3842440093836627068652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123253458448836091536561 3842440093836627068652421)
                  ·
                    refine ⟨720457517594367575372329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842440093836627068652421 720457517594367575372329)
                    ·
                      rfl

theorem cell22_2104629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_2104629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104629 prefixEnd_2104629 := by exact prefixLift 2104629
  have htrace : WordTrace (prefixWord ++ tailWord_2104629) baseStart_2104629 baseEnd_2104629 := by
    simpa [prefixWord, tailWord_2104629, baseEnd_2104629] using wordTrace_append hprefix tailTrace_2104629
  have hstable : (prefixWord ++ tailWord_2104629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104629).length < 2 ^ (prefixWord ++ tailWord_2104629).sum := by decide
  have hdescent : baseEnd_2104629 < baseStart_2104629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104659 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 1, 3]
def baseStart_2104659 : Nat := 118140960795 + 2104659 * 2 ^ 59
def prefixEnd_2104659 : Nat := 4983230072969 + 3 ^ 40 * 2104659 * 2
def baseEnd_2104659 : Nat := 720467787207457497122237

theorem tailTrace_2104659 : CollatzResearch.WordTrace tailWord_2104659 prefixEnd_2104659 720467787207457497122237 := by
  unfold tailWord_2104659
  simp only [CollatzResearch.WordTrace]
  refine ⟨76763220082187364985261031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51175480054791576656840687 76763220082187364985261031)
  ·
    refine ⟨115144830123281047477891547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76763220082187364985261031 115144830123281047477891547)
    ·
      refine ⟨172717245184921571216837321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115144830123281047477891547 172717245184921571216837321)
      ·
        refine ⟨129537933888691178412627991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172717245184921571216837321 129537933888691178412627991)
        ·
          refine ⟨194306900833036767618941987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129537933888691178412627991 194306900833036767618941987)
          ·
            refine ⟨291460351249555151428412981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194306900833036767618941987 291460351249555151428412981)
            ·
              refine ⟨27324407929645795446413717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291460351249555151428412981 27324407929645795446413717)
              ·
                refine ⟨1280831621702146661550643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27324407929645795446413717 1280831621702146661550643)
                ·
                  refine ⟨1921247432553219992325965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1280831621702146661550643 1921247432553219992325965)
                  ·
                    refine ⟨720467787207457497122237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921247432553219992325965 720467787207457497122237)
                    ·
                      rfl

theorem cell22_2104659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 1, 3].length) (baseStart_2104659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104659 prefixEnd_2104659 := by exact prefixLift 2104659
  have htrace : WordTrace (prefixWord ++ tailWord_2104659) baseStart_2104659 baseEnd_2104659 := by
    simpa [prefixWord, tailWord_2104659, baseEnd_2104659] using wordTrace_append hprefix tailTrace_2104659
  have hstable : (prefixWord ++ tailWord_2104659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104659).length < 2 ^ (prefixWord ++ tailWord_2104659).sum := by decide
  have hdescent : baseEnd_2104659 < baseStart_2104659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104749 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2104749 : Nat := 118140960795 + 2104749 * 2 ^ 59
def prefixEnd_2104749 : Nat := 4983230072969 + 3 ^ 40 * 2104749 * 2
def baseEnd_2104749 : Nat := 720498596046727262371961

theorem tailTrace_2104749 : CollatzResearch.WordTrace tailWord_2104749 prefixEnd_2104749 720498596046727262371961 := by
  unfold tailWord_2104749
  simp only [CollatzResearch.WordTrace]
  refine ⟨76766502651861310356037301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51177668434574206904024867 76766502651861310356037301)
  ·
    refine ⟨7196859623611997845878497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76766502651861310356037301 7196859623611997845878497)
    ·
      refine ⟨5397644717708998384408873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7196859623611997845878497 5397644717708998384408873)
      ·
        refine ⟨4048233538281748788306655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5397644717708998384408873 4048233538281748788306655)
        ·
          refine ⟨6072350307422623182459983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048233538281748788306655 6072350307422623182459983)
          ·
            refine ⟨9108525461133934773689975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072350307422623182459983 9108525461133934773689975)
            ·
              refine ⟨13662788191700902160534963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9108525461133934773689975 13662788191700902160534963)
              ·
                refine ⟨20494182287551353240802445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13662788191700902160534963 20494182287551353240802445)
                ·
                  refine ⟨7685318357831757465300917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20494182287551353240802445 7685318357831757465300917)
                  ·
                    refine ⟨720498596046727262371961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7685318357831757465300917 720498596046727262371961)
                    ·
                      rfl

theorem cell22_2104749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2104749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104749 prefixEnd_2104749 := by exact prefixLift 2104749
  have htrace : WordTrace (prefixWord ++ tailWord_2104749) baseStart_2104749 baseEnd_2104749 := by
    simpa [prefixWord, tailWord_2104749, baseEnd_2104749] using wordTrace_append hprefix tailTrace_2104749
  have hstable : (prefixWord ++ tailWord_2104749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104749).length < 2 ^ (prefixWord ++ tailWord_2104749).sum := by decide
  have hdescent : baseEnd_2104749 < baseStart_2104749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104794 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_2104794 : Nat := 118140960795 + 2104794 * 2 ^ 59
def prefixEnd_2104794 : Nat := 4983230072969 + 3 ^ 40 * 2104794 * 2
def baseEnd_2104794 : Nat := 720514000466362144996823

theorem tailTrace_2104794 : CollatzResearch.WordTrace tailWord_2104794 prefixEnd_2104794 720514000466362144996823 := by
  unfold tailWord_2104794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19192035984174570760356359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51178762624465522027616957 19192035984174570760356359)
  ·
    refine ⟨28788053976261856140534539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19192035984174570760356359 28788053976261856140534539)
    ·
      refine ⟨43182080964392784210801809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28788053976261856140534539 43182080964392784210801809)
      ·
        refine ⟨32386560723294588158101357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43182080964392784210801809 32386560723294588158101357)
        ·
          refine ⟨12144960271235470559288009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32386560723294588158101357 12144960271235470559288009)
          ·
            refine ⟨9108720203426602919466007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12144960271235470559288009 9108720203426602919466007)
            ·
              refine ⟨13663080305139904379199011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9108720203426602919466007 13663080305139904379199011)
              ·
                refine ⟨20494620457709856568798517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13663080305139904379199011 20494620457709856568798517)
                ·
                  refine ⟨1921370667910299053324861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20494620457709856568798517 1921370667910299053324861)
                  ·
                    refine ⟨720514000466362144996823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921370667910299053324861 720514000466362144996823)
                    ·
                      rfl

theorem cell22_2104794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_2104794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104794 prefixEnd_2104794 := by exact prefixLift 2104794
  have htrace : WordTrace (prefixWord ++ tailWord_2104794) baseStart_2104794 baseEnd_2104794 := by
    simpa [prefixWord, tailWord_2104794, baseEnd_2104794] using wordTrace_append hprefix tailTrace_2104794
  have hstable : (prefixWord ++ tailWord_2104794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104794).length < 2 ^ (prefixWord ++ tailWord_2104794).sum := by decide
  have hdescent : baseEnd_2104794 < baseStart_2104794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104824 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_2104824 : Nat := 118140960795 + 2104824 * 2 ^ 59
def prefixEnd_2104824 : Nat := 4983230072969 + 3 ^ 40 * 2104824 * 2
def baseEnd_2104824 : Nat := 240174756693150688915577

theorem tailTrace_2104824 : CollatzResearch.WordTrace tailWord_2104824 prefixEnd_2104824 240174756693150688915577 := by
  unfold tailWord_2104824
  simp only [CollatzResearch.WordTrace]
  refine ⟨38384619063294799082508763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51179492084393065443345017 38384619063294799082508763)
  ·
    refine ⟨57576928594942198623763145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38384619063294799082508763 57576928594942198623763145)
    ·
      refine ⟨43182696446206648967822359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57576928594942198623763145 43182696446206648967822359)
      ·
        refine ⟨64774044669309973451733539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43182696446206648967822359 64774044669309973451733539)
        ·
          refine ⟨97161067003964960177600309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64774044669309973451733539 97161067003964960177600309)
          ·
            refine ⟨9108850031621715016650029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97161067003964960177600309 9108850031621715016650029)
            ·
              refine ⟨3415818761858143131243761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9108850031621715016650029 3415818761858143131243761)
              ·
                refine ⟨2561864071393607348432821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3415818761858143131243761 2561864071393607348432821)
                ·
                  refine ⟨240174756693150688915577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561864071393607348432821 240174756693150688915577)
                  ·
                    rfl

theorem cell22_2104824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_2104824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104824 prefixEnd_2104824 := by exact prefixLift 2104824
  have htrace : WordTrace (prefixWord ++ tailWord_2104824) baseStart_2104824 baseEnd_2104824 := by
    simpa [prefixWord, tailWord_2104824, baseEnd_2104824] using wordTrace_append hprefix tailTrace_2104824
  have hstable : (prefixWord ++ tailWord_2104824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104824).length < 2 ^ (prefixWord ++ tailWord_2104824).sum := by decide
  have hdescent : baseEnd_2104824 < baseStart_2104824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104839 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2104839 : Nat := 118140960795 + 2104839 * 2 ^ 59
def prefixEnd_2104839 : Nat := 4983230072969 + 3 ^ 40 * 2104839 * 2
def baseEnd_2104839 : Nat := 720529404885997027621685

theorem tailTrace_2104839 : CollatzResearch.WordTrace tailWord_2104839 prefixEnd_2104839 720529404885997027621685 := by
  unfold tailWord_2104839
  simp only [CollatzResearch.WordTrace]
  refine ⟨76769785221535255726813571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51179856814356837151209047 76769785221535255726813571)
  ·
    refine ⟨115154677832302883590220357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76769785221535255726813571 115154677832302883590220357)
    ·
      refine ⟨21591502093556790673166317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115154677832302883590220357 21591502093556790673166317)
      ·
        refine ⟨8096813285083796502437369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21591502093556790673166317 8096813285083796502437369)
        ·
          refine ⟨6072609963812847376828027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8096813285083796502437369 6072609963812847376828027)
          ·
            refine ⟨9108914945719271065242041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072609963812847376828027 9108914945719271065242041)
            ·
              refine ⟨6831686209289453298931531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9108914945719271065242041 6831686209289453298931531)
              ·
                refine ⟨10247529313934179948397297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6831686209289453298931531 10247529313934179948397297)
                ·
                  refine ⟨7685646985450634961297973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10247529313934179948397297 7685646985450634961297973)
                  ·
                    refine ⟨720529404885997027621685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7685646985450634961297973 720529404885997027621685)
                    ·
                      rfl

theorem cell22_2104839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2104839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104839 prefixEnd_2104839 := by exact prefixLift 2104839
  have htrace : WordTrace (prefixWord ++ tailWord_2104839) baseStart_2104839 baseEnd_2104839 := by
    simpa [prefixWord, tailWord_2104839, baseEnd_2104839] using wordTrace_append hprefix tailTrace_2104839
  have hstable : (prefixWord ++ tailWord_2104839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104839).length < 2 ^ (prefixWord ++ tailWord_2104839).sum := by decide
  have hdescent : baseEnd_2104839 < baseStart_2104839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104901 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_2104901 : Nat := 118140960795 + 2104901 * 2 ^ 59
def prefixEnd_2104901 : Nat := 4983230072969 + 3 ^ 40 * 2104901 * 2
def baseEnd_2104901 : Nat := 720550628753049532571495

theorem tailTrace_2104901 : CollatzResearch.WordTrace tailWord_2104901 prefixEnd_2104901 720550628753049532571495 := by
  unfold tailWord_2104901
  simp only [CollatzResearch.WordTrace]
  refine ⟨76772046547310640315570557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51181364364873760210380371 76772046547310640315570557)
  ·
    refine ⟨28789517455241490118338959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76772046547310640315570557 28789517455241490118338959)
    ·
      refine ⟨43184276182862235177508439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28789517455241490118338959 43184276182862235177508439)
      ·
        refine ⟨64776414274293352766262659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43184276182862235177508439 64776414274293352766262659)
        ·
          refine ⟨97164621411440029149393989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64776414274293352766262659 97164621411440029149393989)
          ·
            refine ⟨18218366514645005465511373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97164621411440029149393989 18218366514645005465511373)
            ·
              refine ⟨6831887442991877049566765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18218366514645005465511373 6831887442991877049566765)
              ·
                refine ⟨2561957791121953893587537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6831887442991877049566765 2561957791121953893587537)
                ·
                  refine ⟨1921468343341465420190653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561957791121953893587537 1921468343341465420190653)
                  ·
                    refine ⟨720550628753049532571495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921468343341465420190653 720550628753049532571495)
                    ·
                      rfl

theorem cell22_2104901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_2104901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104901 prefixEnd_2104901 := by exact prefixLift 2104901
  have htrace : WordTrace (prefixWord ++ tailWord_2104901) baseStart_2104901 baseEnd_2104901 := by
    simpa [prefixWord, tailWord_2104901, baseEnd_2104901] using wordTrace_append hprefix tailTrace_2104901
  have hstable : (prefixWord ++ tailWord_2104901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104901).length < 2 ^ (prefixWord ++ tailWord_2104901).sum := by decide
  have hdescent : baseEnd_2104901 < baseStart_2104901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104914 : List Nat := [3, 2, 2, 1, 2, 2, 2, 8]
def baseStart_2104914 : Nat := 118140960795 + 2104914 * 2 ^ 59
def prefixEnd_2104914 : Nat := 4983230072969 + 3 ^ 40 * 2104914 * 2
def baseEnd_2104914 : Nat := 80061675435413536888495

theorem tailTrace_2104914 : CollatzResearch.WordTrace tailWord_2104914 prefixEnd_2104914 80061675435413536888495 := by
  unfold tailWord_2104914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193130174065885883948449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51181680464175695690529197 19193130174065885883948449)
  ·
    refine ⟨14394847630549414412961337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19193130174065885883948449 14394847630549414412961337)
    ·
      refine ⟨10796135722912060809721003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14394847630549414412961337 10796135722912060809721003)
      ·
        refine ⟨16194203584368091214581505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10796135722912060809721003 16194203584368091214581505)
        ·
          refine ⟨12145652688276068410936129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16194203584368091214581505 12145652688276068410936129)
          ·
            refine ⟨9109239516207051308202097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12145652688276068410936129 9109239516207051308202097)
            ·
              refine ⟨6831929637155288481151573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9109239516207051308202097 6831929637155288481151573)
              ·
                refine ⟨80061675435413536888495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6831929637155288481151573 80061675435413536888495)
                ·
                  rfl

theorem cell22_2104914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_2104914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104914 prefixEnd_2104914 := by exact prefixLift 2104914
  have htrace : WordTrace (prefixWord ++ tailWord_2104914) baseStart_2104914 baseEnd_2104914 := by
    simpa [prefixWord, tailWord_2104914, baseEnd_2104914] using wordTrace_append hprefix tailTrace_2104914
  have hstable : (prefixWord ++ tailWord_2104914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104914).length < 2 ^ (prefixWord ++ tailWord_2104914).sum := by decide
  have hdescent : baseEnd_2104914 < baseStart_2104914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104916 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2104916 : Nat := 118140960795 + 2104916 * 2 ^ 59
def prefixEnd_2104916 : Nat := 4983230072969 + 3 ^ 40 * 2104916 * 2
def baseEnd_2104916 : Nat := 720555763559594493446449

theorem tailTrace_2104916 : CollatzResearch.WordTrace tailWord_2104916 prefixEnd_2104916 720555763559594493446449 := by
  unfold tailWord_2104916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38386296821128148938683301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51181729094837531918244401 38386296821128148938683301)
  ·
    refine ⟨7197430653961527926003119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38386296821128148938683301 7197430653961527926003119)
    ·
      refine ⟨10796145980942291889004679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197430653961527926003119 10796145980942291889004679)
      ·
        refine ⟨16194218971413437833507019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10796145980942291889004679 16194218971413437833507019)
        ·
          refine ⟨24291328457120156750260529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16194218971413437833507019 24291328457120156750260529)
          ·
            refine ⟨18218496342840117562695397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24291328457120156750260529 18218496342840117562695397)
            ·
              refine ⟨3415968064282522043005387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18218496342840117562695397 3415968064282522043005387)
              ·
                refine ⟨5123952096423783064508081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3415968064282522043005387 5123952096423783064508081)
                ·
                  refine ⟨3842964072317837298381061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123952096423783064508081 3842964072317837298381061)
                  ·
                    refine ⟨720555763559594493446449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842964072317837298381061 720555763559594493446449)
                    ·
                      rfl

theorem cell22_2104916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2104916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104916 prefixEnd_2104916 := by exact prefixLift 2104916
  have htrace : WordTrace (prefixWord ++ tailWord_2104916) baseStart_2104916 baseEnd_2104916 := by
    simpa [prefixWord, tailWord_2104916, baseEnd_2104916] using wordTrace_append hprefix tailTrace_2104916
  have hstable : (prefixWord ++ tailWord_2104916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104916).length < 2 ^ (prefixWord ++ tailWord_2104916).sum := by decide
  have hdescent : baseEnd_2104916 < baseStart_2104916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104944 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 6]
def baseStart_2104944 : Nat := 118140960795 + 2104944 * 2 ^ 59
def prefixEnd_2104944 : Nat := 4983230072969 + 3 ^ 40 * 2104944 * 2
def baseEnd_2104944 : Nat := 720565348531811753746363

theorem tailTrace_2104944 : CollatzResearch.WordTrace tailWord_2104944 prefixEnd_2104944 720565348531811753746363 := by
  unfold tailWord_2104944
  simp only [CollatzResearch.WordTrace]
  refine ⟨38386807443077429329692943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51182409924103239106257257 38386807443077429329692943)
  ·
    refine ⟨57580211164616143994539415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38386807443077429329692943 57580211164616143994539415)
    ·
      refine ⟨86370316746924215991809123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57580211164616143994539415 86370316746924215991809123)
      ·
        refine ⟨129555475120386323987713685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86370316746924215991809123 129555475120386323987713685)
        ·
          refine ⟨6072912896268108936924079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129555475120386323987713685 6072912896268108936924079)
          ·
            refine ⟨9109369344402163405386119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072912896268108936924079 9109369344402163405386119)
            ·
              refine ⟨13664054016603245108079179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9109369344402163405386119 13664054016603245108079179)
              ·
                refine ⟨20496081024904867662118769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13664054016603245108079179 20496081024904867662118769)
                ·
                  refine ⟨15372060768678650746589077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20496081024904867662118769 15372060768678650746589077)
                  ·
                    refine ⟨720565348531811753746363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15372060768678650746589077 720565348531811753746363)
                    ·
                      rfl

theorem cell22_2104944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_2104944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104944 prefixEnd_2104944 := by exact prefixLift 2104944
  have htrace : WordTrace (prefixWord ++ tailWord_2104944) baseStart_2104944 baseEnd_2104944 := by
    simpa [prefixWord, tailWord_2104944, baseEnd_2104944] using wordTrace_append hprefix tailTrace_2104944
  have hstable : (prefixWord ++ tailWord_2104944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104944).length < 2 ^ (prefixWord ++ tailWord_2104944).sum := by decide
  have hdescent : baseEnd_2104944 < baseStart_2104944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2104993 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 5]
def baseStart_2104993 : Nat := 118140960795 + 2104993 * 2 ^ 59
def prefixEnd_2104993 : Nat := 4983230072969 + 3 ^ 40 * 2104993 * 2
def baseEnd_2104993 : Nat := 240194040744397319757071

theorem tailTrace_2104993 : CollatzResearch.WordTrace tailWord_2104993 prefixEnd_2104993 240194040744397319757071 := by
  unfold tailWord_2104993
  simp only [CollatzResearch.WordTrace]
  refine ⟨76775402062977340027919633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51183601375318226685279755 76775402062977340027919633)
  ·
    refine ⟨57581551547233005020939725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76775402062977340027919633 57581551547233005020939725)
    ·
      refine ⟨21593081830212376882852397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57581551547233005020939725 21593081830212376882852397)
      ·
        refine ⟨8097405686329641331069649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21593081830212376882852397 8097405686329641331069649)
        ·
          refine ⟨6073054264747230998302237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8097405686329641331069649 6073054264747230998302237)
          ·
            refine ⟨2277395349280211624363339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6073054264747230998302237 2277395349280211624363339)
            ·
              refine ⟨3416093023920317436545009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277395349280211624363339 3416093023920317436545009)
              ·
                refine ⟨2562069767940238077408757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416093023920317436545009 2562069767940238077408757)
                ·
                  refine ⟨240194040744397319757071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562069767940238077408757 240194040744397319757071)
                  ·
                    rfl

theorem cell22_2104993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_2104993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2104993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2104993 prefixEnd_2104993 := by exact prefixLift 2104993
  have htrace : WordTrace (prefixWord ++ tailWord_2104993) baseStart_2104993 baseEnd_2104993 := by
    simpa [prefixWord, tailWord_2104993, baseEnd_2104993] using wordTrace_append hprefix tailTrace_2104993
  have hstable : (prefixWord ++ tailWord_2104993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2104993).length < 2 ^ (prefixWord ++ tailWord_2104993).sum := by decide
  have hdescent : baseEnd_2104993 < baseStart_2104993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2104993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105049 : List Nat := [1, 2, 1, 2, 3, 3, 10]
def baseStart_2105049 : Nat := 118140960795 + 2105049 * 2 ^ 59
def prefixEnd_2105049 : Nat := 4983230072969 + 3 ^ 40 * 2105049 * 2
def baseEnd_2105049 : Nat := 26688936747319499254483

theorem tailTrace_2105049 : CollatzResearch.WordTrace tailWord_2105049 prefixEnd_2105049 26688936747319499254483 := by
  unfold tailWord_2105049
  simp only [CollatzResearch.WordTrace]
  refine ⟨76777444550774461591958201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51184963033849641061305467 76777444550774461591958201)
  ·
    refine ⟨57583083413080846193968651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76777444550774461591958201 57583083413080846193968651)
    ·
      refine ⟨86374625119621269290952977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57583083413080846193968651 86374625119621269290952977)
      ·
        refine ⟨64780968839715951968214733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86374625119621269290952977 64780968839715951968214733)
        ·
          refine ⟨24292863314893481988080525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64780968839715951968214733 24292863314893481988080525)
          ·
            refine ⟨9109823743085055745530197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24292863314893481988080525 9109823743085055745530197)
            ·
              refine ⟨26688936747319499254483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9109823743085055745530197 26688936747319499254483)
              ·
                rfl

theorem cell22_2105049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 10].length) (baseStart_2105049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105049 prefixEnd_2105049 := by exact prefixLift 2105049
  have htrace : WordTrace (prefixWord ++ tailWord_2105049) baseStart_2105049 baseEnd_2105049 := by
    simpa [prefixWord, tailWord_2105049, baseEnd_2105049] using wordTrace_append hprefix tailTrace_2105049
  have hstable : (prefixWord ++ tailWord_2105049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105049).length < 2 ^ (prefixWord ++ tailWord_2105049).sum := by decide
  have hdescent : baseEnd_2105049 < baseStart_2105049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105128 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_2105128 : Nat := 118140960795 + 2105128 * 2 ^ 59
def prefixEnd_2105128 : Nat := 4983230072969 + 3 ^ 40 * 2105128 * 2
def baseEnd_2105128 : Nat := 240209445164032202381933

theorem tailTrace_2105128 : CollatzResearch.WordTrace tailWord_2105128 prefixEnd_2105128 240209445164032202381933 := by
  unfold tailWord_2105128
  simp only [CollatzResearch.WordTrace]
  refine ⟨38390162958744129042042019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51186883944992172056056025 38390162958744129042042019)
  ·
    refine ⟨57585244438116193563063029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38390162958744129042042019 57585244438116193563063029)
    ·
      refine ⟨5398616666073393146537159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57585244438116193563063029 5398616666073393146537159)
      ·
        refine ⟨8097924999110089719805739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5398616666073393146537159 8097924999110089719805739)
        ·
          refine ⟨12146887498665134579708609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8097924999110089719805739 12146887498665134579708609)
          ·
            refine ⟨9110165623998850934781457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12146887498665134579708609 9110165623998850934781457)
            ·
              refine ⟨6832624217999138201086093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9110165623998850934781457 6832624217999138201086093)
              ·
                refine ⟨2562234081749676825407285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6832624217999138201086093 2562234081749676825407285)
                ·
                  refine ⟨240209445164032202381933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562234081749676825407285 240209445164032202381933)
                  ·
                    rfl

theorem cell22_2105128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_2105128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105128 prefixEnd_2105128 := by exact prefixLift 2105128
  have htrace : WordTrace (prefixWord ++ tailWord_2105128) baseStart_2105128 baseEnd_2105128 := by
    simpa [prefixWord, tailWord_2105128, baseEnd_2105128] using wordTrace_append hprefix tailTrace_2105128
  have hstable : (prefixWord ++ tailWord_2105128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105128).length < 2 ^ (prefixWord ++ tailWord_2105128).sum := by decide
  have hdescent : baseEnd_2105128 < baseStart_2105128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105173 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 6]
def baseStart_2105173 : Nat := 118140960795 + 2105173 * 2 ^ 59
def prefixEnd_2105173 : Nat := 4983230072969 + 3 ^ 40 * 2105173 * 2
def baseEnd_2105173 : Nat := 240214579970577163256887

theorem tailTrace_2105173 : CollatzResearch.WordTrace tailWord_2105173 prefixEnd_2105173 240214579970577163256887 := by
  unfold tailWord_2105173
  simp only [CollatzResearch.WordTrace]
  refine ⟨76781967202325230769472173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51187978134883487179648115 76781967202325230769472173)
  ·
    refine ⟨28793237700871961538552065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76781967202325230769472173 28793237700871961538552065)
    ·
      refine ⟨21594928275653971153914049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28793237700871961538552065 21594928275653971153914049)
      ·
        refine ⟨16196196206740478365435537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21594928275653971153914049 16196196206740478365435537)
        ·
          refine ⟨12147147155055358774076653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16196196206740478365435537 12147147155055358774076653)
          ·
            refine ⟨4555180183145759540278745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12147147155055358774076653 4555180183145759540278745)
            ·
              refine ⟨3416385137359319655209059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555180183145759540278745 3416385137359319655209059)
              ·
                refine ⟨5124577706038979482813589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416385137359319655209059 5124577706038979482813589)
                ·
                  refine ⟨240214579970577163256887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5124577706038979482813589 240214579970577163256887)
                  ·
                    rfl

theorem cell22_2105173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_2105173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105173 prefixEnd_2105173 := by exact prefixLift 2105173
  have htrace : WordTrace (prefixWord ++ tailWord_2105173) baseStart_2105173 baseEnd_2105173 := by
    simpa [prefixWord, tailWord_2105173, baseEnd_2105173] using wordTrace_append hprefix tailTrace_2105173
  have hstable : (prefixWord ++ tailWord_2105173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105173).length < 2 ^ (prefixWord ++ tailWord_2105173).sum := by decide
  have hdescent : baseEnd_2105173 < baseStart_2105173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105201 : List Nat := [1, 2, 2, 2, 1, 3, 3, 8]
def baseStart_2105201 : Nat := 118140960795 + 2105201 * 2 ^ 59
def prefixEnd_2105201 : Nat := 4983230072969 + 3 ^ 40 * 2105201 * 2
def baseEnd_2105201 : Nat := 80072591653772083341175

theorem tailTrace_2105201 : CollatzResearch.WordTrace tailWord_2105201 prefixEnd_2105201 80072591653772083341175 := by
  unfold tailWord_2105201
  simp only [CollatzResearch.WordTrace]
  refine ⟨76782988446223791551491457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51188658964149194367660971 76782988446223791551491457)
  ·
    refine ⟨57587241334667843663618593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76782988446223791551491457 57587241334667843663618593)
    ·
      refine ⟨43190431001000882747713945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57587241334667843663618593 43190431001000882747713945)
      ·
        refine ⟨32392823250750662060785459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43190431001000882747713945 32392823250750662060785459)
        ·
          refine ⟨48589234876125993091178189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32392823250750662060785459 48589234876125993091178189)
          ·
            refine ⟨18220963078547247409191821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48589234876125993091178189 18220963078547247409191821)
            ·
              refine ⟨6832861154455217778446933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18220963078547247409191821 6832861154455217778446933)
              ·
                refine ⟨80072591653772083341175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6832861154455217778446933 80072591653772083341175)
                ·
                  rfl

theorem cell22_2105201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 8].length) (baseStart_2105201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105201 prefixEnd_2105201 := by exact prefixLift 2105201
  have htrace : WordTrace (prefixWord ++ tailWord_2105201) baseStart_2105201 baseEnd_2105201 := by
    simpa [prefixWord, tailWord_2105201, baseEnd_2105201] using wordTrace_append hprefix tailTrace_2105201
  have hstable : (prefixWord ++ tailWord_2105201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105201).length < 2 ^ (prefixWord ++ tailWord_2105201).sum := by decide
  have hdescent : baseEnd_2105201 < baseStart_2105201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105340 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 4, 3]
def baseStart_2105340 : Nat := 118140960795 + 2105340 * 2 ^ 59
def prefixEnd_2105340 : Nat := 4983230072969 + 3 ^ 40 * 2105340 * 2
def baseEnd_2105340 : Nat := 720700907424598720845149

theorem tailTrace_2105340 : CollatzResearch.WordTrace tailWord_2105340 prefixEnd_2105340 720700907424598720845149 := by
  unfold tailWord_2105340
  simp only [CollatzResearch.WordTrace]
  refine ⟨38394029096360109145400737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51192038795146812193867649 38394029096360109145400737)
  ·
    refine ⟨28795521822270081859050553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38394029096360109145400737 28795521822270081859050553)
    ·
      refine ⟨21596641366702561394287915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28795521822270081859050553 21596641366702561394287915)
      ·
        refine ⟨32394962050053842091431873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21596641366702561394287915 32394962050053842091431873)
        ·
          refine ⟨24296221537540381568573905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32394962050053842091431873 24296221537540381568573905)
          ·
            refine ⟨18222166153155286176430429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24296221537540381568573905 18222166153155286176430429)
            ·
              refine ⟨6833312307433232316161411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18222166153155286176430429 6833312307433232316161411)
              ·
                refine ⟨10249968461149848474242117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6833312307433232316161411 10249968461149848474242117)
                ·
                  refine ⟨1921869086465596588920397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10249968461149848474242117 1921869086465596588920397)
                  ·
                    refine ⟨720700907424598720845149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1921869086465596588920397 720700907424598720845149)
                    ·
                      rfl

theorem cell22_2105340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_2105340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105340 prefixEnd_2105340 := by exact prefixLift 2105340
  have htrace : WordTrace (prefixWord ++ tailWord_2105340) baseStart_2105340 baseEnd_2105340 := by
    simpa [prefixWord, tailWord_2105340, baseEnd_2105340] using wordTrace_append hprefix tailTrace_2105340
  have hstable : (prefixWord ++ tailWord_2105340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105340).length < 2 ^ (prefixWord ++ tailWord_2105340).sum := by decide
  have hdescent : baseEnd_2105340 < baseStart_2105340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105342 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_2105342 : Nat := 118140960795 + 2105342 * 2 ^ 59
def prefixEnd_2105342 : Nat := 4983230072969 + 3 ^ 40 * 2105342 * 2
def baseEnd_2105342 : Nat := 240233864021823794098381

theorem tailTrace_2105342 : CollatzResearch.WordTrace tailWord_2105342 prefixEnd_2105342 240233864021823794098381 := by
  unfold tailWord_2105342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598516392339121579046785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51192087425808648421582853 9598516392339121579046785)
  ·
    refine ⟨7198887294254341184285089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9598516392339121579046785 7198887294254341184285089)
    ·
      refine ⟨5399165470690755888213817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7198887294254341184285089 5399165470690755888213817)
      ·
        refine ⟨4049374103018066916160363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5399165470690755888213817 4049374103018066916160363)
        ·
          refine ⟨6074061154527100374240545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4049374103018066916160363 6074061154527100374240545)
          ·
            refine ⟨4555545865895325280680409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6074061154527100374240545 4555545865895325280680409)
            ·
              refine ⟨3416659399421493960510307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555545865895325280680409 3416659399421493960510307)
              ·
                refine ⟨5124989099132240940765461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416659399421493960510307 5124989099132240940765461)
                ·
                  refine ⟨240233864021823794098381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5124989099132240940765461 240233864021823794098381)
                  ·
                    rfl

theorem cell22_2105342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_2105342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105342 prefixEnd_2105342 := by exact prefixLift 2105342
  have htrace : WordTrace (prefixWord ++ tailWord_2105342) baseStart_2105342 baseEnd_2105342 := by
    simpa [prefixWord, tailWord_2105342, baseEnd_2105342] using wordTrace_append hprefix tailTrace_2105342
  have hstable : (prefixWord ++ tailWord_2105342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105342).length < 2 ^ (prefixWord ++ tailWord_2105342).sum := by decide
  have hdescent : baseEnd_2105342 < baseStart_2105342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105368 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 7]
def baseStart_2105368 : Nat := 118140960795 + 2105368 * 2 ^ 59
def prefixEnd_2105368 : Nat := 4983230072969 + 3 ^ 40 * 2105368 * 2
def baseEnd_2105368 : Nat := 720710492396815981145063

theorem tailTrace_2105368 : CollatzResearch.WordTrace tailWord_2105368 prefixEnd_2105368 720710492396815981145063 := by
  unfold tailWord_2105368
  simp only [CollatzResearch.WordTrace]
  refine ⟨38394539718309389536410379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51192719624412519381880505 38394539718309389536410379)
  ·
    refine ⟨57591809577464084304615569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38394539718309389536410379 57591809577464084304615569)
    ·
      refine ⟨43193857183098063228461677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57591809577464084304615569 43193857183098063228461677)
      ·
        refine ⟨16197696443661773710673129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43193857183098063228461677 16197696443661773710673129)
        ·
          refine ⟨12148272332746330283004847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16197696443661773710673129 12148272332746330283004847)
          ·
            refine ⟨18222408499119495424507271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12148272332746330283004847 18222408499119495424507271)
            ·
              refine ⟨27333612748679243136760907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18222408499119495424507271 27333612748679243136760907)
              ·
                refine ⟨41000419123018864705141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27333612748679243136760907 41000419123018864705141361)
                ·
                  refine ⟨30750314342264148528856021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41000419123018864705141361 30750314342264148528856021)
                  ·
                    refine ⟨720710492396815981145063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30750314342264148528856021 720710492396815981145063)
                    ·
                      rfl

theorem cell22_2105368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_2105368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105368 prefixEnd_2105368 := by exact prefixLift 2105368
  have htrace : WordTrace (prefixWord ++ tailWord_2105368) baseStart_2105368 baseEnd_2105368 := by
    simpa [prefixWord, tailWord_2105368, baseEnd_2105368] using wordTrace_append hprefix tailTrace_2105368
  have hstable : (prefixWord ++ tailWord_2105368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105368).length < 2 ^ (prefixWord ++ tailWord_2105368).sum := by decide
  have hdescent : baseEnd_2105368 < baseStart_2105368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105370 : List Nat := [3, 1, 1, 3, 1, 3, 4, 6]
def baseStart_2105370 : Nat := 118140960795 + 2105370 * 2 ^ 59
def prefixEnd_2105370 : Nat := 4983230072969 + 3 ^ 40 * 2105370 * 2
def baseEnd_2105370 : Nat := 80079019670854293621673

theorem tailTrace_2105370 : CollatzResearch.WordTrace tailWord_2105370 prefixEnd_2105370 80079019670854293621673 := by
  unfold tailWord_2105370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197288095652883353598391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51192768255074355609595709 19197288095652883353598391)
  ·
    refine ⟨28795932143479325030397587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197288095652883353598391 28795932143479325030397587)
    ·
      refine ⟨43193898215218987545596381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28795932143479325030397587 43193898215218987545596381)
      ·
        refine ⟨16197711830707120329598643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43193898215218987545596381 16197711830707120329598643)
        ·
          refine ⟨24296567746060680494397965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16197711830707120329598643 24296567746060680494397965)
          ·
            refine ⟨9111212904772755185399237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24296567746060680494397965 9111212904772755185399237)
            ·
              refine ⟨1708352419644891597262357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9111212904772755185399237 1708352419644891597262357)
              ·
                refine ⟨80079019670854293621673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1708352419644891597262357 80079019670854293621673)
                ·
                  rfl

theorem cell22_2105370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_2105370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105370 prefixEnd_2105370 := by exact prefixLift 2105370
  have htrace : WordTrace (prefixWord ++ tailWord_2105370) baseStart_2105370 baseEnd_2105370 := by
    simpa [prefixWord, tailWord_2105370, baseEnd_2105370] using wordTrace_append hprefix tailTrace_2105370
  have hstable : (prefixWord ++ tailWord_2105370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105370).length < 2 ^ (prefixWord ++ tailWord_2105370).sum := by decide
  have hdescent : baseEnd_2105370 < baseStart_2105370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105413 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_2105413 : Nat := 118140960795 + 2105413 * 2 ^ 59
def prefixEnd_2105413 : Nat := 4983230072969 + 3 ^ 40 * 2105413 * 2
def baseEnd_2105413 : Nat := 720725896816450863769925

theorem tailTrace_2105413 : CollatzResearch.WordTrace tailWord_2105413 prefixEnd_2105413 720725896816450863769925 := by
  unfold tailWord_2105413
  simp only [CollatzResearch.WordTrace]
  refine ⟨76790720721455751758208893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51193813814303834505472595 76790720721455751758208893)
  ·
    refine ⟨28796520270545906909328335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76790720721455751758208893 28796520270545906909328335)
    ·
      refine ⟨43194780405818860363992503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28796520270545906909328335 43194780405818860363992503)
      ·
        refine ⟨64792170608728290545988755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43194780405818860363992503 64792170608728290545988755)
        ·
          refine ⟨97188255913092435818983133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64792170608728290545988755 97188255913092435818983133)
          ·
            refine ⟨36445595967409663432118675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97188255913092435818983133 36445595967409663432118675)
            ·
              refine ⟨54668393951114495148178013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36445595967409663432118675 54668393951114495148178013)
              ·
                refine ⟨20500647731667935680566755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54668393951114495148178013 20500647731667935680566755)
                ·
                  refine ⟨30750971597501903520850133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20500647731667935680566755 30750971597501903520850133)
                  ·
                    refine ⟨720725896816450863769925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30750971597501903520850133 720725896816450863769925)
                    ·
                      rfl

theorem cell22_2105413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_2105413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105413 prefixEnd_2105413 := by exact prefixLift 2105413
  have htrace : WordTrace (prefixWord ++ tailWord_2105413) baseStart_2105413 baseEnd_2105413 := by
    simpa [prefixWord, tailWord_2105413, baseEnd_2105413] using wordTrace_append hprefix tailTrace_2105413
  have hstable : (prefixWord ++ tailWord_2105413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105413).length < 2 ^ (prefixWord ++ tailWord_2105413).sum := by decide
  have hdescent : baseEnd_2105413 < baseStart_2105413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105415 : List Nat := [1, 1, 4, 1, 3, 1, 3, 3, 5]
def baseStart_2105415 : Nat := 118140960795 + 2105415 * 2 ^ 59
def prefixEnd_2105415 : Nat := 4983230072969 + 3 ^ 40 * 2105415 * 2
def baseEnd_2105415 : Nat := 240242193819107841739973

theorem tailTrace_2105415 : CollatzResearch.WordTrace tailWord_2105415 prefixEnd_2105415 240242193819107841739973 := by
  unfold tailWord_2105415
  simp only [CollatzResearch.WordTrace]
  refine ⟨76790793667448506099781699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51193862444965670733187799 76790793667448506099781699)
  ·
    refine ⟨115186190501172759149672549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76790793667448506099781699 115186190501172759149672549)
    ·
      refine ⟨21597410718969892340563603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115186190501172759149672549 21597410718969892340563603)
      ·
        refine ⟨32396116078454838510845405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21597410718969892340563603 32396116078454838510845405)
        ·
          refine ⟨12148543529420564441567027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32396116078454838510845405 12148543529420564441567027)
          ·
            refine ⟨18222815294130846662350541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12148543529420564441567027 18222815294130846662350541)
            ·
              refine ⟨6833555735299067498381453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18222815294130846662350541 6833555735299067498381453)
              ·
                refine ⟨2562583400737150311893045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6833555735299067498381453 2562583400737150311893045)
                ·
                  refine ⟨240242193819107841739973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562583400737150311893045 240242193819107841739973)
                  ·
                    rfl

theorem cell22_2105415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 3, 5].length) (baseStart_2105415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105415 prefixEnd_2105415 := by exact prefixLift 2105415
  have htrace : WordTrace (prefixWord ++ tailWord_2105415) baseStart_2105415 baseEnd_2105415 := by
    simpa [prefixWord, tailWord_2105415, baseEnd_2105415] using wordTrace_append hprefix tailTrace_2105415
  have hstable : (prefixWord ++ tailWord_2105415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105415).length < 2 ^ (prefixWord ++ tailWord_2105415).sum := by decide
  have hdescent : baseEnd_2105415 < baseStart_2105415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105462 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2105462 : Nat := 118140960795 + 2105462 * 2 ^ 59
def prefixEnd_2105462 : Nat := 4983230072969 + 3 ^ 40 * 2105462 * 2
def baseEnd_2105462 : Nat := 720742670517831069294775

theorem tailTrace_2105462 : CollatzResearch.WordTrace tailWord_2105462 prefixEnd_2105462 720742670517831069294775 := by
  unfold tailWord_2105462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799531743642389570421415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51195005265518822084495093 4799531743642389570421415)
  ·
    refine ⟨7199297615463584355632123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4799531743642389570421415 7199297615463584355632123)
    ·
      refine ⟨10798946423195376533448185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7199297615463584355632123 10798946423195376533448185)
      ·
        refine ⟨8099209817396532400086139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10798946423195376533448185 8099209817396532400086139)
        ·
          refine ⟨12148814726094798600129209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099209817396532400086139 12148814726094798600129209)
          ·
            refine ⟨9111611044571098950096907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12148814726094798600129209 9111611044571098950096907)
            ·
              refine ⟨13667416566856648425145361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9111611044571098950096907 13667416566856648425145361)
              ·
                refine ⟨10250562425142486318859021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13667416566856648425145361 10250562425142486318859021)
                ·
                  refine ⟨3843960909428432369572133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10250562425142486318859021 3843960909428432369572133)
                  ·
                    refine ⟨720742670517831069294775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3843960909428432369572133 720742670517831069294775)
                    ·
                      rfl

theorem cell22_2105462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2105462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105462 prefixEnd_2105462 := by exact prefixLift 2105462
  have htrace : WordTrace (prefixWord ++ tailWord_2105462) baseStart_2105462 baseEnd_2105462 := by
    simpa [prefixWord, tailWord_2105462, baseEnd_2105462] using wordTrace_append hprefix tailTrace_2105462
  have hstable : (prefixWord ++ tailWord_2105462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105462).length < 2 ^ (prefixWord ++ tailWord_2105462).sum := by decide
  have hdescent : baseEnd_2105462 < baseStart_2105462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105475 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_2105475 : Nat := 118140960795 + 2105475 * 2 ^ 59
def prefixEnd_2105475 : Nat := 4983230072969 + 3 ^ 40 * 2105475 * 2
def baseEnd_2105475 : Nat := 720747120683503368719735

theorem tailTrace_2105475 : CollatzResearch.WordTrace tailWord_2105475 prefixEnd_2105475 720747120683503368719735 := by
  unfold tailWord_2105475
  simp only [CollatzResearch.WordTrace]
  refine ⟨76792982047231136346965879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51195321364820757564643919 76792982047231136346965879)
  ·
    refine ⟨115189473070846704520448819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76792982047231136346965879 115189473070846704520448819)
    ·
      refine ⟨172784209606270056780673229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115189473070846704520448819 172784209606270056780673229)
      ·
        refine ⟨64794078602351271292752461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172784209606270056780673229 64794078602351271292752461)
        ·
          refine ⟨24297779475881726734782173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64794078602351271292752461 24297779475881726734782173)
          ·
            refine ⟨9111667303455647525543315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24297779475881726734782173 9111667303455647525543315)
            ·
              refine ⟨13667500955183471288314973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9111667303455647525543315 13667500955183471288314973)
              ·
                refine ⟨5125312858193801733118115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13667500955183471288314973 5125312858193801733118115)
                ·
                  refine ⟨7687969287290702599677173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125312858193801733118115 7687969287290702599677173)
                  ·
                    refine ⟨720747120683503368719735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7687969287290702599677173 720747120683503368719735)
                    ·
                      rfl

theorem cell22_2105475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_2105475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105475 prefixEnd_2105475 := by exact prefixLift 2105475
  have htrace : WordTrace (prefixWord ++ tailWord_2105475) baseStart_2105475 baseEnd_2105475 := by
    simpa [prefixWord, tailWord_2105475, baseEnd_2105475] using wordTrace_append hprefix tailTrace_2105475
  have hstable : (prefixWord ++ tailWord_2105475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105475).length < 2 ^ (prefixWord ++ tailWord_2105475).sum := by decide
  have hdescent : baseEnd_2105475 < baseStart_2105475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105496 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 1, 4]
def baseStart_2105496 : Nat := 118140960795 + 2105496 * 2 ^ 59
def prefixEnd_2105496 : Nat := 4983230072969 + 3 ^ 40 * 2105496 * 2
def baseEnd_2105496 : Nat := 720754309412666313944671

theorem tailTrace_2105496 : CollatzResearch.WordTrace tailWord_2105496 prefixEnd_2105496 720754309412666313944671 := by
  unfold tailWord_2105496
  simp only [CollatzResearch.WordTrace]
  refine ⟨38396873990077528466740171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51195831986770037955653561 38396873990077528466740171)
  ·
    refine ⟨57595310985116292700110257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38396873990077528466740171 57595310985116292700110257)
    ·
      refine ⟨43196483238837219525082693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57595310985116292700110257 43196483238837219525082693)
      ·
        refine ⟨8099340607281978660953005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43196483238837219525082693 8099340607281978660953005)
        ·
          refine ⟨3037252727730741997857377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8099340607281978660953005 3037252727730741997857377)
          ·
            refine ⟨2277939545798056498393033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037252727730741997857377 2277939545798056498393033)
            ·
              refine ⟨1708454659348542373794775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2277939545798056498393033 1708454659348542373794775)
              ·
                refine ⟨2562681989022813560692163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708454659348542373794775 2562681989022813560692163)
                ·
                  refine ⟨3844022983534220341038245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562681989022813560692163 3844022983534220341038245)
                  ·
                    refine ⟨720754309412666313944671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844022983534220341038245 720754309412666313944671)
                    ·
                      rfl

theorem cell22_2105496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_2105496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105496 prefixEnd_2105496 := by exact prefixLift 2105496
  have htrace : WordTrace (prefixWord ++ tailWord_2105496) baseStart_2105496 baseEnd_2105496 := by
    simpa [prefixWord, tailWord_2105496, baseEnd_2105496] using wordTrace_append hprefix tailTrace_2105496
  have hstable : (prefixWord ++ tailWord_2105496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105496).length < 2 ^ (prefixWord ++ tailWord_2105496).sum := by decide
  have hdescent : baseEnd_2105496 < baseStart_2105496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105505 : List Nat := [1, 2, 3, 3, 1, 3, 9]
def baseStart_2105505 : Nat := 118140960795 + 2105505 * 2 ^ 59
def prefixEnd_2105505 : Nat := 4983230072969 + 3 ^ 40 * 2105505 * 2
def baseEnd_2105505 : Nat := 26694718159133084832209

theorem tailTrace_2105505 : CollatzResearch.WordTrace tailWord_2105505 prefixEnd_2105505 26694718159133084832209 := by
  unfold tailWord_2105505
  simp only [CollatzResearch.WordTrace]
  refine ⟨76794076237122451470557969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51196050824748300980371979 76794076237122451470557969)
  ·
    refine ⟨57595557177841838602918477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76794076237122451470557969 57595557177841838602918477)
    ·
      refine ⟨21598333941690689476094429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57595557177841838602918477 21598333941690689476094429)
      ·
        refine ⟨8099375228134008553535411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21598333941690689476094429 8099375228134008553535411)
        ·
          refine ⟨12149062842201012830303117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099375228134008553535411 12149062842201012830303117)
          ·
            refine ⟨4555898565825379811363669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12149062842201012830303117 4555898565825379811363669)
            ·
              refine ⟨26694718159133084832209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4555898565825379811363669 26694718159133084832209)
              ·
                rfl

theorem cell22_2105505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 9].length) (baseStart_2105505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105505 prefixEnd_2105505 := by exact prefixLift 2105505
  have htrace : WordTrace (prefixWord ++ tailWord_2105505) baseStart_2105505 baseEnd_2105505 := by
    simpa [prefixWord, tailWord_2105505, baseEnd_2105505] using wordTrace_append hprefix tailTrace_2105505
  have hstable : (prefixWord ++ tailWord_2105505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105505).length < 2 ^ (prefixWord ++ tailWord_2105505).sum := by decide
  have hdescent : baseEnd_2105505 < baseStart_2105505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105627 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 4, 3]
def baseStart_2105627 : Nat := 118140960795 + 2105627 * 2 ^ 59
def prefixEnd_2105627 : Nat := 4983230072969 + 3 ^ 40 * 2105627 * 2
def baseEnd_2105627 : Nat := 720799153389825638919269

theorem tailTrace_2105627 : CollatzResearch.WordTrace tailWord_2105627 prefixEnd_2105627 720799153389825638919269 := by
  unfold tailWord_2105627
  simp only [CollatzResearch.WordTrace]
  refine ⟨76798525942680466306499135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51199017295120310870999423 76798525942680466306499135)
  ·
    refine ⟨115197788914020699459748703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76798525942680466306499135 115197788914020699459748703)
    ·
      refine ⟨172796683371031049189623055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115197788914020699459748703 172796683371031049189623055)
      ·
        refine ⟨259195025056546573784434583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172796683371031049189623055 259195025056546573784434583)
        ·
          refine ⟨388792537584819860676651875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259195025056546573784434583 388792537584819860676651875)
          ·
            refine ⟨583188806377229791014977813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388792537584819860676651875 583188806377229791014977813)
            ·
              refine ⟨27336975298932646453827085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 583188806377229791014977813 27336975298932646453827085)
              ·
                refine ⟨10251365737099742420185157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27336975298932646453827085 10251365737099742420185157)
                ·
                  refine ⟨1922131075706201703784717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10251365737099742420185157 1922131075706201703784717)
                  ·
                    refine ⟨720799153389825638919269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922131075706201703784717 720799153389825638919269)
                    ·
                      rfl

theorem cell22_2105627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3].length) (baseStart_2105627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105627 prefixEnd_2105627 := by exact prefixLift 2105627
  have htrace : WordTrace (prefixWord ++ tailWord_2105627) baseStart_2105627 baseEnd_2105627 := by
    simpa [prefixWord, tailWord_2105627, baseEnd_2105627] using wordTrace_append hprefix tailTrace_2105627
  have hstable : (prefixWord ++ tailWord_2105627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105627).length < 2 ^ (prefixWord ++ tailWord_2105627).sum := by decide
  have hdescent : baseEnd_2105627 < baseStart_2105627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105644 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 2, 3]
def baseStart_2105644 : Nat := 118140960795 + 2105644 * 2 ^ 59
def prefixEnd_2105644 : Nat := 4983230072969 + 3 ^ 40 * 2105644 * 2
def baseEnd_2105644 : Nat := 720804972837243261244217

theorem tailTrace_2105644 : CollatzResearch.WordTrace tailWord_2105644 prefixEnd_2105644 720804972837243261244217 := by
  unfold tailWord_2105644
  simp only [CollatzResearch.WordTrace]
  refine ⟨38399572991809439104933993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51199430655745918806578657 38399572991809439104933993)
  ·
    refine ⟨28799679743857079328700495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38399572991809439104933993 28799679743857079328700495)
    ·
      refine ⟨43199519615785618993050743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28799679743857079328700495 43199519615785618993050743)
      ·
        refine ⟨64799279423678428489576115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43199519615785618993050743 64799279423678428489576115)
        ·
          refine ⟨97198919135517642734364173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64799279423678428489576115 97198919135517642734364173)
          ·
            refine ⟨36449594675819116025386565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97198919135517642734364173 36449594675819116025386565)
            ·
              refine ⟨6834299001716084254759981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36449594675819116025386565 6834299001716084254759981)
              ·
                refine ⟨2562862125643531595534993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6834299001716084254759981 2562862125643531595534993)
                ·
                  refine ⟨1922146594232648696651245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562862125643531595534993 1922146594232648696651245)
                  ·
                    refine ⟨720804972837243261244217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922146594232648696651245 720804972837243261244217)
                    ·
                      rfl

theorem cell22_2105644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_2105644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105644 prefixEnd_2105644 := by exact prefixLift 2105644
  have htrace : WordTrace (prefixWord ++ tailWord_2105644) baseStart_2105644 baseEnd_2105644 := by
    simpa [prefixWord, tailWord_2105644, baseEnd_2105644] using wordTrace_append hprefix tailTrace_2105644
  have hstable : (prefixWord ++ tailWord_2105644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105644).length < 2 ^ (prefixWord ++ tailWord_2105644).sum := by decide
  have hdescent : baseEnd_2105644 < baseStart_2105644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105646 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_2105646 : Nat := 118140960795 + 2105646 * 2 ^ 59
def prefixEnd_2105646 : Nat := 4983230072969 + 3 ^ 40 * 2105646 * 2
def baseEnd_2105646 : Nat := 240268552492705307564737

theorem tailTrace_2105646 : CollatzResearch.WordTrace tailWord_2105646 prefixEnd_2105646 240268552492705307564737 := by
  unfold tailWord_2105646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9599902366201454068930099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51199479286407755034293861 9599902366201454068930099)
  ·
    refine ⟨14399853549302181103395149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9599902366201454068930099 14399853549302181103395149)
    ·
      refine ⟨5399945080988317913773181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14399853549302181103395149 5399945080988317913773181)
      ·
        refine ⟨2024979405370619217664943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5399945080988317913773181 2024979405370619217664943)
        ·
          refine ⟨3037469108055928826497415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024979405370619217664943 3037469108055928826497415)
          ·
            refine ⟨4556203662083893239746123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037469108055928826497415 4556203662083893239746123)
            ·
              refine ⟨6834305493125839859619185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556203662083893239746123 6834305493125839859619185)
              ·
                refine ⟨5125729119844379894714389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6834305493125839859619185 5125729119844379894714389)
                ·
                  refine ⟨240268552492705307564737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5125729119844379894714389 240268552492705307564737)
                  ·
                    rfl

theorem cell22_2105646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_2105646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105646 prefixEnd_2105646 := by exact prefixLift 2105646
  have htrace : WordTrace (prefixWord ++ tailWord_2105646) baseStart_2105646 baseEnd_2105646 := by
    simpa [prefixWord, tailWord_2105646, baseEnd_2105646] using wordTrace_append hprefix tailTrace_2105646
  have hstable : (prefixWord ++ tailWord_2105646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105646).length < 2 ^ (prefixWord ++ tailWord_2105646).sum := by decide
  have hdescent : baseEnd_2105646 < baseStart_2105646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105665 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2105665 : Nat := 118140960795 + 2105665 * 2 ^ 59
def prefixEnd_2105665 : Nat := 4983230072969 + 3 ^ 40 * 2105665 * 2
def baseEnd_2105665 : Nat := 720812161566406206469153

theorem tailTrace_2105665 : CollatzResearch.WordTrace tailWord_2105665 prefixEnd_2105665 720812161566406206469153 := by
  unfold tailWord_2105665
  simp only [CollatzResearch.WordTrace]
  refine ⟨76799911916542798796382449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51199941277695199197588299 76799911916542798796382449)
  ·
    refine ⟨57599933937407099097286837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76799911916542798796382449 57599933937407099097286837)
    ·
      refine ⟨5399993806631915540370641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57599933937407099097286837 5399993806631915540370641)
      ·
        refine ⟨4049995354973936655277981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5399993806631915540370641 4049995354973936655277981)
        ·
          refine ⟨1518748258115226245729243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4049995354973936655277981 1518748258115226245729243)
          ·
            refine ⟨2278122387172839368593865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518748258115226245729243 2278122387172839368593865)
            ·
              refine ⟨1708591790379629526445399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2278122387172839368593865 1708591790379629526445399)
              ·
                refine ⟨2562887685569444289668099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1708591790379629526445399 2562887685569444289668099)
                ·
                  refine ⟨3844331528354166434502149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562887685569444289668099 3844331528354166434502149)
                  ·
                    refine ⟨720812161566406206469153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844331528354166434502149 720812161566406206469153)
                    ·
                      rfl

theorem cell22_2105665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2105665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105665 prefixEnd_2105665 := by exact prefixLift 2105665
  have htrace : WordTrace (prefixWord ++ tailWord_2105665) baseStart_2105665 baseEnd_2105665 := by
    simpa [prefixWord, tailWord_2105665, baseEnd_2105665] using wordTrace_append hprefix tailTrace_2105665
  have hstable : (prefixWord ++ tailWord_2105665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105665).length < 2 ^ (prefixWord ++ tailWord_2105665).sum := by decide
  have hdescent : baseEnd_2105665 < baseStart_2105665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105706 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2105706 : Nat := 118140960795 + 2105706 * 2 ^ 59
def prefixEnd_2105706 : Nat := 4983230072969 + 3 ^ 40 * 2105706 * 2
def baseEnd_2105706 : Nat := 720826196704295766194027

theorem tailTrace_2105706 : CollatzResearch.WordTrace tailWord_2105706 prefixEnd_2105706 720826196704295766194027 := by
  unfold tailWord_2105706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19200351827348565699656243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51200938206262841865749981 19200351827348565699656243)
  ·
    refine ⟨28800527741022848549484365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19200351827348565699656243 28800527741022848549484365)
    ·
      refine ⟨10800197902883568206056637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28800527741022848549484365 10800197902883568206056637)
      ·
        refine ⟨4050074213581338077271239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10800197902883568206056637 4050074213581338077271239)
        ·
          refine ⟨6075111320372007115906859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4050074213581338077271239 6075111320372007115906859)
          ·
            refine ⟨9112666980558010673860289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6075111320372007115906859 9112666980558010673860289)
            ·
              refine ⟨6834500235418508005395217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9112666980558010673860289 6834500235418508005395217)
              ·
                refine ⟨5125875176563881004046413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6834500235418508005395217 5125875176563881004046413)
                ·
                  refine ⟨1922203191211455376517405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5125875176563881004046413 1922203191211455376517405)
                  ·
                    refine ⟨720826196704295766194027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922203191211455376517405 720826196704295766194027)
                    ·
                      rfl

theorem cell22_2105706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2105706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105706 prefixEnd_2105706 := by exact prefixLift 2105706
  have htrace : WordTrace (prefixWord ++ tailWord_2105706) baseStart_2105706 baseEnd_2105706 := by
    simpa [prefixWord, tailWord_2105706, baseEnd_2105706] using wordTrace_append hprefix tailTrace_2105706
  have hstable : (prefixWord ++ tailWord_2105706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105706).length < 2 ^ (prefixWord ++ tailWord_2105706).sum := by decide
  have hdescent : baseEnd_2105706 < baseStart_2105706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105723 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 1, 3]
def baseStart_2105723 : Nat := 118140960795 + 2105723 * 2 ^ 59
def prefixEnd_2105723 : Nat := 4983230072969 + 3 ^ 40 * 2105723 * 2
def baseEnd_2105723 : Nat := 720832016151713388518975

theorem tailTrace_2105723 : CollatzResearch.WordTrace tailWord_2105723 prefixEnd_2105723 720832016151713388518975 := by
  unfold tailWord_2105723
  simp only [CollatzResearch.WordTrace]
  refine ⟨76802027350332674701993823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51201351566888449801329215 76802027350332674701993823)
  ·
    refine ⟨115203041025499012052990735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76802027350332674701993823 115203041025499012052990735)
    ·
      refine ⟨172804561538248518079486103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115203041025499012052990735 172804561538248518079486103)
      ·
        refine ⟨259206842307372777119229155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172804561538248518079486103 259206842307372777119229155)
        ·
          refine ⟨388810263461059165678843733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259206842307372777119229155 388810263461059165678843733)
          ·
            refine ⟨2278185137467143548899475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 388810263461059165678843733 2278185137467143548899475)
            ·
              refine ⟨3417277706200715323349213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278185137467143548899475 3417277706200715323349213)
              ·
                refine ⟨1281479139825268246255955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3417277706200715323349213 1281479139825268246255955)
                ·
                  refine ⟨1922218709737902369383933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281479139825268246255955 1922218709737902369383933)
                  ·
                    refine ⟨720832016151713388518975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922218709737902369383933 720832016151713388518975)
                    ·
                      rfl

theorem cell22_2105723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 1, 3].length) (baseStart_2105723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105723 prefixEnd_2105723 := by exact prefixLift 2105723
  have htrace : WordTrace (prefixWord ++ tailWord_2105723) baseStart_2105723 baseEnd_2105723 := by
    simpa [prefixWord, tailWord_2105723, baseEnd_2105723] using wordTrace_append hprefix tailTrace_2105723
  have hstable : (prefixWord ++ tailWord_2105723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105723).length < 2 ^ (prefixWord ++ tailWord_2105723).sum := by decide
  have hdescent : baseEnd_2105723 < baseStart_2105723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105807 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_2105807 : Nat := 118140960795 + 2105807 * 2 ^ 59
def prefixEnd_2105807 : Nat := 4983230072969 + 3 ^ 40 * 2105807 * 2
def baseEnd_2105807 : Nat := 720860771068365169418717

theorem tailTrace_2105807 : CollatzResearch.WordTrace tailWord_2105807 prefixEnd_2105807 720860771068365169418717 := by
  unfold tailWord_2105807
  simp only [CollatzResearch.WordTrace]
  refine ⟨76805091082028357048051675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51203394054685571365367783 76805091082028357048051675)
  ·
    refine ⟨115207636623042535572077513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76805091082028357048051675 115207636623042535572077513)
    ·
      refine ⟨86405727467281901679058135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115207636623042535572077513 86405727467281901679058135)
      ·
        refine ⟨129608591200922852518587203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86405727467281901679058135 129608591200922852518587203)
        ·
          refine ⟨194412886801384278777880805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129608591200922852518587203 194412886801384278777880805)
          ·
            refine ⟨36452416275259552270852651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194412886801384278777880805 36452416275259552270852651)
            ·
              refine ⟨54678624412889328406278977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36452416275259552270852651 54678624412889328406278977)
              ·
                refine ⟨41008968309666996304709233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54678624412889328406278977 41008968309666996304709233)
                ·
                  refine ⟨30756726232250247228531925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41008968309666996304709233 30756726232250247228531925)
                  ·
                    refine ⟨720860771068365169418717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30756726232250247228531925 720860771068365169418717)
                    ·
                      rfl

theorem cell22_2105807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_2105807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105807 prefixEnd_2105807 := by exact prefixLift 2105807
  have htrace : WordTrace (prefixWord ++ tailWord_2105807) baseStart_2105807 baseEnd_2105807 := by
    simpa [prefixWord, tailWord_2105807, baseEnd_2105807] using wordTrace_append hprefix tailTrace_2105807
  have hstable : (prefixWord ++ tailWord_2105807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105807).length < 2 ^ (prefixWord ++ tailWord_2105807).sum := by decide
  have hdescent : baseEnd_2105807 < baseStart_2105807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105916 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_2105916 : Nat := 118140960795 + 2105916 * 2 ^ 59
def prefixEnd_2105916 : Nat := 4983230072969 + 3 ^ 40 * 2105916 * 2
def baseEnd_2105916 : Nat := 240299361331975072814461

theorem tailTrace_2105916 : CollatzResearch.WordTrace tailWord_2105916 prefixEnd_2105916 240299361331975072814461 := by
  unfold tailWord_2105916
  simp only [CollatzResearch.WordTrace]
  refine ⟨38404533319316734331884801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51206044425755645775846401 38404533319316734331884801)
  ·
    refine ⟨28803399989487550748913601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38404533319316734331884801 28803399989487550748913601)
    ·
      refine ⟨21602549992115663061685201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28803399989487550748913601 21602549992115663061685201)
      ·
        refine ⟨16201912494086747296263901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21602549992115663061685201 16201912494086747296263901)
        ·
          refine ⟨6075717185282530236098963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16201912494086747296263901 6075717185282530236098963)
          ·
            refine ⟨9113575777923795354148445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6075717185282530236098963 9113575777923795354148445)
            ·
              refine ⟨3417590916721423257805667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9113575777923795354148445 3417590916721423257805667)
              ·
                refine ⟨5126386375082134886708501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417590916721423257805667 5126386375082134886708501)
                ·
                  refine ⟨240299361331975072814461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5126386375082134886708501 240299361331975072814461)
                  ·
                    rfl

theorem cell22_2105916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_2105916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105916 prefixEnd_2105916 := by exact prefixLift 2105916
  have htrace : WordTrace (prefixWord ++ tailWord_2105916) baseStart_2105916 baseEnd_2105916 := by
    simpa [prefixWord, tailWord_2105916, baseEnd_2105916] using wordTrace_append hprefix tailTrace_2105916
  have hstable : (prefixWord ++ tailWord_2105916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105916).length < 2 ^ (prefixWord ++ tailWord_2105916).sum := by decide
  have hdescent : baseEnd_2105916 < baseStart_2105916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105944 : List Nat := [2, 1, 2, 2, 1, 2, 4, 8]
def baseStart_2105944 : Nat := 118140960795 + 2105944 * 2 ^ 59
def prefixEnd_2105944 : Nat := 4983230072969 + 3 ^ 40 * 2105944 * 2
def baseEnd_2105944 : Nat := 80100852107571386527033

theorem tailTrace_2105944 : CollatzResearch.WordTrace tailWord_2105944 prefixEnd_2105944 80100852107571386527033 := by
  unfold tailWord_2105944
  simp only [CollatzResearch.WordTrace]
  refine ⟨38405043941266014722894443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51206725255021352963859257 38405043941266014722894443)
  ·
    refine ⟨57607565911899022084341665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38405043941266014722894443 57607565911899022084341665)
    ·
      refine ⟨43205674433924266563256249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57607565911899022084341665 43205674433924266563256249)
      ·
        refine ⟨32404255825443199922442187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43205674433924266563256249 32404255825443199922442187)
        ·
          refine ⟨48606383738164799883663281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32404255825443199922442187 48606383738164799883663281)
          ·
            refine ⟨36454787803623599912747461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48606383738164799883663281 36454787803623599912747461)
            ·
              refine ⟨6835272713179424983640149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36454787803623599912747461 6835272713179424983640149)
              ·
                refine ⟨80100852107571386527033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6835272713179424983640149 80100852107571386527033)
                ·
                  rfl

theorem cell22_2105944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_2105944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105944 prefixEnd_2105944 := by exact prefixLift 2105944
  have htrace : WordTrace (prefixWord ++ tailWord_2105944) baseStart_2105944 baseEnd_2105944 := by
    simpa [prefixWord, tailWord_2105944, baseEnd_2105944] using wordTrace_append hprefix tailTrace_2105944
  have hstable : (prefixWord ++ tailWord_2105944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105944).length < 2 ^ (prefixWord ++ tailWord_2105944).sum := by decide
  have hdescent : baseEnd_2105944 < baseStart_2105944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105948 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2105948 : Nat := 118140960795 + 2105948 * 2 ^ 59
def prefixEnd_2105948 : Nat := 4983230072969 + 3 ^ 40 * 2105948 * 2
def baseEnd_2105948 : Nat := 720909038249887801643285

theorem tailTrace_2105948 : CollatzResearch.WordTrace tailWord_2105948 prefixEnd_2105948 720909038249887801643285 := by
  unfold tailWord_2105948
  simp only [CollatzResearch.WordTrace]
  refine ⟨38405116887258769064467249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51206822516345025419289665 38405116887258769064467249)
  ·
    refine ⟨28803837665444076798350437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38405116887258769064467249 28803837665444076798350437)
    ·
      refine ⟨5400719562270764399690707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28803837665444076798350437 5400719562270764399690707)
      ·
        refine ⟨8101079343406146599536061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400719562270764399690707 8101079343406146599536061)
        ·
          refine ⟨3037904753777304974826023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8101079343406146599536061 3037904753777304974826023)
          ·
            refine ⟨4556857130665957462239035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037904753777304974826023 4556857130665957462239035)
            ·
              refine ⟨6835285695998936193358553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556857130665957462239035 6835285695998936193358553)
              ·
                refine ⟨5126464271999202145018915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6835285695998936193358553 5126464271999202145018915)
                ·
                  refine ⟨7689696407998803217528373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5126464271999202145018915 7689696407998803217528373)
                  ·
                    refine ⟨720909038249887801643285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7689696407998803217528373 720909038249887801643285)
                    ·
                      rfl

theorem cell22_2105948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2105948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105948 prefixEnd_2105948 := by exact prefixLift 2105948
  have htrace : WordTrace (prefixWord ++ tailWord_2105948) baseStart_2105948 baseEnd_2105948 := by
    simpa [prefixWord, tailWord_2105948, baseEnd_2105948] using wordTrace_append hprefix tailTrace_2105948
  have hstable : (prefixWord ++ tailWord_2105948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105948).length < 2 ^ (prefixWord ++ tailWord_2105948).sum := by decide
  have hdescent : baseEnd_2105948 < baseStart_2105948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2105965 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2105965 : Nat := 118140960795 + 2105965 * 2 ^ 59
def prefixEnd_2105965 : Nat := 4983230072969 + 3 ^ 40 * 2105965 * 2
def baseEnd_2105965 : Nat := 720914857697305423968233

theorem tailTrace_2105965 : CollatzResearch.WordTrace tailWord_2105965 prefixEnd_2105965 720914857697305423968233 := by
  unfold tailWord_2105965
  simp only [CollatzResearch.WordTrace]
  refine ⟨76810853815455950032303349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51207235876970633354868899 76810853815455950032303349)
  ·
    refine ⟨7201017545198995315528439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76810853815455950032303349 7201017545198995315528439)
    ·
      refine ⟨10801526317798492973292659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7201017545198995315528439 10801526317798492973292659)
      ·
        refine ⟨16202289476697739459938989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10801526317798492973292659 16202289476697739459938989)
        ·
          refine ⟨6075858553761652297477121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16202289476697739459938989 6075858553761652297477121)
          ·
            refine ⟨4556893915321239223107841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6075858553761652297477121 4556893915321239223107841)
            ·
              refine ⟨3417670436490929417330881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556893915321239223107841 3417670436490929417330881)
              ·
                refine ⟨2563252827368197062998161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3417670436490929417330881 2563252827368197062998161)
                ·
                  refine ⟨1922439620526147797248621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2563252827368197062998161 1922439620526147797248621)
                  ·
                    refine ⟨720914857697305423968233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922439620526147797248621 720914857697305423968233)
                    ·
                      rfl

theorem cell22_2105965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2105965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2105965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2105965 prefixEnd_2105965 := by exact prefixLift 2105965
  have htrace : WordTrace (prefixWord ++ tailWord_2105965) baseStart_2105965 baseEnd_2105965 := by
    simpa [prefixWord, tailWord_2105965, baseEnd_2105965] using wordTrace_append hprefix tailTrace_2105965
  have hstable : (prefixWord ++ tailWord_2105965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2105965).length < 2 ^ (prefixWord ++ tailWord_2105965).sum := by decide
  have hdescent : baseEnd_2105965 < baseStart_2105965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2105965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106061 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2106061 : Nat := 118140960795 + 2106061 * 2 ^ 59
def prefixEnd_2106061 : Nat := 4983230072969 + 3 ^ 40 * 2106061 * 2
def baseEnd_2106061 : Nat := 720947720459193173567939

theorem tailTrace_2106061 : CollatzResearch.WordTrace tailWord_2106061 prefixEnd_2106061 720947720459193173567939 := by
  unfold tailWord_2106061
  simp only [CollatzResearch.WordTrace]
  refine ⟨76814355223108158427798037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51209570148738772285198691 76814355223108158427798037)
  ·
    refine ⟨3600672901083194926303033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76814355223108158427798037 3600672901083194926303033)
    ·
      refine ⟨2700504675812396194727275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3600672901083194926303033 2700504675812396194727275)
      ·
        refine ⟨4050757013718594292090913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700504675812396194727275 4050757013718594292090913)
        ·
          refine ⟨3038067760288945719068185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4050757013718594292090913 3038067760288945719068185)
          ·
            refine ⟨2278550820216709289301139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038067760288945719068185 2278550820216709289301139)
            ·
              refine ⟨3417826230325063933951709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278550820216709289301139 3417826230325063933951709)
              ·
                refine ⟨1281684836371898975231891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3417826230325063933951709 1281684836371898975231891)
                ·
                  refine ⟨1922527254557848462847837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281684836371898975231891 1922527254557848462847837)
                  ·
                    refine ⟨720947720459193173567939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922527254557848462847837 720947720459193173567939)
                    ·
                      rfl

theorem cell22_2106061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2106061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106061 prefixEnd_2106061 := by exact prefixLift 2106061
  have htrace : WordTrace (prefixWord ++ tailWord_2106061) baseStart_2106061 baseEnd_2106061 := by
    simpa [prefixWord, tailWord_2106061, baseEnd_2106061] using wordTrace_append hprefix tailTrace_2106061
  have hstable : (prefixWord ++ tailWord_2106061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106061).length < 2 ^ (prefixWord ++ tailWord_2106061).sum := by decide
  have hdescent : baseEnd_2106061 < baseStart_2106061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106096 : List Nat := [2, 1, 1, 1, 3, 1, 6, 7]
def baseStart_2106096 : Nat := 118140960795 + 2106096 * 2 ^ 59
def prefixEnd_2106096 : Nat := 4983230072969 + 3 ^ 40 * 2106096 * 2
def baseEnd_2106096 : Nat := 80106633519384972104759

theorem tailTrace_2106096 : CollatzResearch.WordTrace tailWord_2106096 prefixEnd_2106096 80106633519384972104759 := by
  unfold tailWord_2106096
  simp only [CollatzResearch.WordTrace]
  refine ⟨38407815888990679702661071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51210421185320906270214761 38407815888990679702661071)
  ·
    refine ⟨57611723833486019553991607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38407815888990679702661071 57611723833486019553991607)
    ·
      refine ⟨86417585750229029330987411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57611723833486019553991607 86417585750229029330987411)
      ·
        refine ⟨129626378625343543996481117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86417585750229029330987411 129626378625343543996481117)
        ·
          refine ⟨48609891984503828998680419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129626378625343543996481117 48609891984503828998680419)
          ·
            refine ⟨72914837976755743498020629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48609891984503828998680419 72914837976755743498020629)
            ·
              refine ⟨3417883030160425476469717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 72914837976755743498020629 3417883030160425476469717)
              ·
                refine ⟨80106633519384972104759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3417883030160425476469717 80106633519384972104759)
                ·
                  rfl

theorem cell22_2106096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_2106096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106096 prefixEnd_2106096 := by exact prefixLift 2106096
  have htrace : WordTrace (prefixWord ++ tailWord_2106096) baseStart_2106096 baseEnd_2106096 := by
    simpa [prefixWord, tailWord_2106096, baseEnd_2106096] using wordTrace_append hprefix tailTrace_2106096
  have hstable : (prefixWord ++ tailWord_2106096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106096).length < 2 ^ (prefixWord ++ tailWord_2106096).sum := by decide
  have hdescent : baseEnd_2106096 < baseStart_2106096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106130 : List Nat := [3, 2, 4, 1, 3, 9]
def baseStart_2106130 : Nat := 118140960795 + 2106130 * 2 ^ 59
def prefixEnd_2106130 : Nat := 4983230072969 + 3 ^ 40 * 2106130 * 2
def baseEnd_2106130 : Nat := 8900880747769135723367

theorem tailTrace_2106130 : CollatzResearch.WordTrace tailWord_2106130 prefixEnd_2106130 8900880747769135723367 := by
  unfold tailWord_2106130
  simp only [CollatzResearch.WordTrace]
  refine ⟨19204217964964545803014961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51211247906572122141373229 19204217964964545803014961)
  ·
    refine ⟨14403163473723409352261221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19204217964964545803014961 14403163473723409352261221)
    ·
      refine ⟨2700593151323139253548979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14403163473723409352261221 2700593151323139253548979)
      ·
        refine ⟨4050889726984708880323469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700593151323139253548979 4050889726984708880323469)
        ·
          refine ⟨1519083647619265830121301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4050889726984708880323469 1519083647619265830121301)
          ·
            refine ⟨8900880747769135723367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1519083647619265830121301 8900880747769135723367)
            ·
              rfl

theorem cell22_2106130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 9].length) (baseStart_2106130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106130 prefixEnd_2106130 := by exact prefixLift 2106130
  have htrace : WordTrace (prefixWord ++ tailWord_2106130) baseStart_2106130 baseEnd_2106130 := by
    simpa [prefixWord, tailWord_2106130, baseEnd_2106130] using wordTrace_append hprefix tailTrace_2106130
  have hstable : (prefixWord ++ tailWord_2106130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106130).length < 2 ^ (prefixWord ++ tailWord_2106130).sum := by decide
  have hdescent : baseEnd_2106130 < baseStart_2106130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106233 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_2106233 : Nat := 118140960795 + 2106233 * 2 ^ 59
def prefixEnd_2106233 : Nat := 4983230072969 + 3 ^ 40 * 2106233 * 2
def baseEnd_2106233 : Nat := 721006599574242058267411

theorem tailTrace_2106233 : CollatzResearch.WordTrace tailWord_2106233 prefixEnd_2106233 721006599574242058267411 := by
  unfold tailWord_2106233
  simp only [CollatzResearch.WordTrace]
  refine ⟨76820628578485031803059353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51213752385656687868706235 76820628578485031803059353)
  ·
    refine ⟨57615471433863773852294515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76820628578485031803059353 57615471433863773852294515)
    ·
      refine ⟨86423207150795660778441773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57615471433863773852294515 86423207150795660778441773)
      ·
        refine ⟨32408702681548372791915665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86423207150795660778441773 32408702681548372791915665)
        ·
          refine ⟨24306527011161279593936749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32408702681548372791915665 24306527011161279593936749)
          ·
            refine ⟨9114947629185479847726281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24306527011161279593936749 9114947629185479847726281)
            ·
              refine ⟨6836210721889109885794711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9114947629185479847726281 6836210721889109885794711)
              ·
                refine ⟨10254316082833664828692067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6836210721889109885794711 10254316082833664828692067)
                ·
                  refine ⟨15381474124250497243038101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10254316082833664828692067 15381474124250497243038101)
                  ·
                    refine ⟨721006599574242058267411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15381474124250497243038101 721006599574242058267411)
                    ·
                      rfl

theorem cell22_2106233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_2106233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106233 prefixEnd_2106233 := by exact prefixLift 2106233
  have htrace : WordTrace (prefixWord ++ tailWord_2106233) baseStart_2106233 baseEnd_2106233 := by
    simpa [prefixWord, tailWord_2106233, baseEnd_2106233] using wordTrace_append hprefix tailTrace_2106233
  have hstable : (prefixWord ++ tailWord_2106233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106233).length < 2 ^ (prefixWord ++ tailWord_2106233).sum := by decide
  have hdescent : baseEnd_2106233 < baseStart_2106233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106248 : List Nat := [2, 1, 3, 3, 2, 1, 10]
def baseStart_2106248 : Nat := 118140960795 + 2106248 * 2 ^ 59
def prefixEnd_2106248 : Nat := 4983230072969 + 3 ^ 40 * 2106248 * 2
def baseEnd_2106248 : Nat := 26704138310399519227495

theorem tailTrace_2106248 : CollatzResearch.WordTrace tailWord_2106248 prefixEnd_2106248 26704138310399519227495 := by
  unfold tailWord_2106248
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410587836715344682427699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51214117115620459576570265 38410587836715344682427699)
  ·
    refine ⟨57615881755073017023641549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38410587836715344682427699 57615881755073017023641549)
    ·
      refine ⟨21605955658152381383865581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57615881755073017023641549 21605955658152381383865581)
      ·
        refine ⟨8102233371807143018949593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21605955658152381383865581 8102233371807143018949593)
        ·
          refine ⟨6076675028855357264212195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8102233371807143018949593 6076675028855357264212195)
          ·
            refine ⟨9115012543283035896318293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076675028855357264212195 9115012543283035896318293)
            ·
              refine ⟨26704138310399519227495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9115012543283035896318293 26704138310399519227495)
              ·
                rfl

theorem cell22_2106248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 10].length) (baseStart_2106248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106248 prefixEnd_2106248 := by exact prefixLift 2106248
  have htrace : WordTrace (prefixWord ++ tailWord_2106248) baseStart_2106248 baseEnd_2106248 := by
    simpa [prefixWord, tailWord_2106248, baseEnd_2106248] using wordTrace_append hprefix tailTrace_2106248
  have hstable : (prefixWord ++ tailWord_2106248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106248).length < 2 ^ (prefixWord ++ tailWord_2106248).sum := by decide
  have hdescent : baseEnd_2106248 < baseStart_2106248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106250 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2106250 : Nat := 118140960795 + 2106250 * 2 ^ 59
def prefixEnd_2106250 : Nat := 4983230072969 + 3 ^ 40 * 2106250 * 2
def baseEnd_2106250 : Nat := 721012419021659680592359

theorem tailTrace_2106250 : CollatzResearch.WordTrace tailWord_2106250 prefixEnd_2106250 721012419021659680592359 := by
  unfold tailWord_2106250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19205312154855860926607051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51214165746282295804285469 19205312154855860926607051)
  ·
    refine ⟨28807968232283791389910577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19205312154855860926607051 28807968232283791389910577)
    ·
      refine ⟨21605976174212843542432933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28807968232283791389910577 21605976174212843542432933)
      ·
        refine ⟨4051120532664908164206175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21605976174212843542432933 4051120532664908164206175)
        ·
          refine ⟨6076680798997362246309263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051120532664908164206175 6076680798997362246309263)
          ·
            refine ⟨9115021198496043369463895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076680798997362246309263 9115021198496043369463895)
            ·
              refine ⟨13672531797744065054195843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9115021198496043369463895 13672531797744065054195843)
              ·
                refine ⟨20508797696616097581293765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13672531797744065054195843 20508797696616097581293765)
                ·
                  refine ⟨3845399568115518296492581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20508797696616097581293765 3845399568115518296492581)
                  ·
                    refine ⟨721012419021659680592359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3845399568115518296492581 721012419021659680592359)
                    ·
                      rfl

theorem cell22_2106250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2106250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106250 prefixEnd_2106250 := by exact prefixLift 2106250
  have htrace : WordTrace (prefixWord ++ tailWord_2106250) baseStart_2106250 baseEnd_2106250 := by
    simpa [prefixWord, tailWord_2106250, baseEnd_2106250] using wordTrace_append hprefix tailTrace_2106250
  have hstable : (prefixWord ++ tailWord_2106250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106250).length < 2 ^ (prefixWord ++ tailWord_2106250).sum := by decide
  have hdescent : baseEnd_2106250 < baseStart_2106250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106438 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2106438 : Nat := 118140960795 + 2106438 * 2 ^ 59
def prefixEnd_2106438 : Nat := 4983230072969 + 3 ^ 40 * 2106438 * 2
def baseEnd_2106438 : Nat := 721076775263689856891783

theorem tailTrace_2106438 : CollatzResearch.WordTrace tailWord_2106438 prefixEnd_2106438 721076775263689856891783 := by
  unfold tailWord_2106438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400878298210698494195999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51218737028494901209514645 2400878298210698494195999)
  ·
    refine ⟨3601317447316047741293999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400878298210698494195999 3601317447316047741293999)
    ·
      refine ⟨5401976170974071611940999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601317447316047741293999 5401976170974071611940999)
      ·
        refine ⟨8102964256461107417911499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401976170974071611940999 8102964256461107417911499)
        ·
          refine ⟨12154446384691661126867249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8102964256461107417911499 12154446384691661126867249)
          ·
            refine ⟨9115834788518745845150437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12154446384691661126867249 9115834788518745845150437)
            ·
              refine ⟨1709219022847264845965707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9115834788518745845150437 1709219022847264845965707)
              ·
                refine ⟨2563828534270897268948561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709219022847264845965707 2563828534270897268948561)
                ·
                  refine ⟨1922871400703172951711421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2563828534270897268948561 1922871400703172951711421)
                  ·
                    refine ⟨721076775263689856891783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1922871400703172951711421 721076775263689856891783)
                    ·
                      rfl

theorem cell22_2106438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2106438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106438 prefixEnd_2106438 := by exact prefixLift 2106438
  have htrace : WordTrace (prefixWord ++ tailWord_2106438) baseStart_2106438 baseEnd_2106438 := by
    simpa [prefixWord, tailWord_2106438, baseEnd_2106438] using wordTrace_append hprefix tailTrace_2106438
  have hstable : (prefixWord ++ tailWord_2106438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106438).length < 2 ^ (prefixWord ++ tailWord_2106438).sum := by decide
  have hdescent : baseEnd_2106438 < baseStart_2106438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106524 : List Nat := [2, 2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_2106524 : Nat := 118140960795 + 2106524 * 2 ^ 59
def prefixEnd_2106524 : Nat := 4983230072969 + 3 ^ 40 * 2106524 * 2
def baseEnd_2106524 : Nat := 240368738273738099747173

theorem tailTrace_2106524 : CollatzResearch.WordTrace tailWord_2106524 prefixEnd_2106524 240368738273738099747173 := by
  unfold tailWord_2106524
  simp only [CollatzResearch.WordTrace]
  refine ⟨38415621110215394250951313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51220828146953859001268417 38415621110215394250951313)
  ·
    refine ⟨28811715832661545688213485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38415621110215394250951313 28811715832661545688213485)
    ·
      refine ⟨10804393437248079633080057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28811715832661545688213485 10804393437248079633080057)
      ·
        refine ⟨8103295077936059724810043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10804393437248079633080057 8103295077936059724810043)
        ·
          refine ⟨12154942616904089587215065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103295077936059724810043 12154942616904089587215065)
          ·
            refine ⟨9116206962678067190411299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12154942616904089587215065 9116206962678067190411299)
            ·
              refine ⟨13674310444017100785616949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9116206962678067190411299 13674310444017100785616949)
              ·
                refine ⟨1281966604126603198651589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13674310444017100785616949 1281966604126603198651589)
                ·
                  refine ⟨240368738273738099747173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1281966604126603198651589 240368738273738099747173)
                  ·
                    rfl

theorem cell22_2106524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_2106524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106524 prefixEnd_2106524 := by exact prefixLift 2106524
  have htrace : WordTrace (prefixWord ++ tailWord_2106524) baseStart_2106524 baseEnd_2106524 := by
    simpa [prefixWord, tailWord_2106524, baseEnd_2106524] using wordTrace_append hprefix tailTrace_2106524
  have hstable : (prefixWord ++ tailWord_2106524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106524).length < 2 ^ (prefixWord ++ tailWord_2106524).sum := by decide
  have hdescent : baseEnd_2106524 < baseStart_2106524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106526 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2106526 : Nat := 118140960795 + 2106526 * 2 ^ 59
def prefixEnd_2106526 : Nat := 4983230072969 + 3 ^ 40 * 2106526 * 2
def baseEnd_2106526 : Nat := 721106899462086960691513

theorem tailTrace_2106526 : CollatzResearch.WordTrace tailWord_2106526 prefixEnd_2106526 721106899462086960691513 := by
  unfold tailWord_2106526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9603914395802942855434429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51220876777615695228983621 9603914395802942855434429)
  ·
    refine ⟨3601467898426103570787911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9603914395802942855434429 3601467898426103570787911)
    ·
      refine ⟨5402201847639155356181867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601467898426103570787911 5402201847639155356181867)
      ·
        refine ⟨8103302771458733034272801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402201847639155356181867 8103302771458733034272801)
        ·
          refine ⟨6077477078594049775704601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8103302771458733034272801 6077477078594049775704601)
          ·
            refine ⟨4558107808945537331778451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6077477078594049775704601 4558107808945537331778451)
            ·
              refine ⟨6837161713418305997667677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558107808945537331778451 6837161713418305997667677)
              ·
                refine ⟨2563935642531864749125379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6837161713418305997667677 2563935642531864749125379)
                ·
                  refine ⟨3845903463797797123688069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563935642531864749125379 3845903463797797123688069)
                  ·
                    refine ⟨721106899462086960691513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3845903463797797123688069 721106899462086960691513)
                    ·
                      rfl

theorem cell22_2106526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2106526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106526 prefixEnd_2106526 := by exact prefixLift 2106526
  have htrace : WordTrace (prefixWord ++ tailWord_2106526) baseStart_2106526 baseEnd_2106526 := by
    simpa [prefixWord, tailWord_2106526, baseEnd_2106526] using wordTrace_append hprefix tailTrace_2106526
  have hstable : (prefixWord ++ tailWord_2106526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106526).length < 2 ^ (prefixWord ++ tailWord_2106526).sum := by decide
  have hdescent : baseEnd_2106526 < baseStart_2106526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106657 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2106657 : Nat := 118140960795 + 2106657 * 2 ^ 59
def prefixEnd_2106657 : Nat := 4983230072969 + 3 ^ 40 * 2106657 * 2
def baseEnd_2106657 : Nat := 721151743439246285666111

theorem tailTrace_2106657 : CollatzResearch.WordTrace tailWord_2106657 prefixEnd_2106657 721151743439246285666111 := by
  unfold tailWord_2106657
  simp only [CollatzResearch.WordTrace]
  refine ⟨76836093128948952216494225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51224062085965968144329483 76836093128948952216494225)
  ·
    refine ⟨57627069846711714162370669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76836093128948952216494225 57627069846711714162370669)
    ·
      refine ⟨21610151192516892810889001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57627069846711714162370669 21610151192516892810889001)
      ·
        refine ⟨16207613394387669608166751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21610151192516892810889001 16207613394387669608166751)
        ·
          refine ⟨24311420091581504412250127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16207613394387669608166751 24311420091581504412250127)
          ·
            refine ⟨36467130137372256618375191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24311420091581504412250127 36467130137372256618375191)
            ·
              refine ⟨54700695206058384927562787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36467130137372256618375191 54700695206058384927562787)
              ·
                refine ⟨82051042809087577391344181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54700695206058384927562787 82051042809087577391344181)
                ·
                  refine ⟨7692285263351960380438517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82051042809087577391344181 7692285263351960380438517)
                  ·
                    refine ⟨721151743439246285666111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7692285263351960380438517 721151743439246285666111)
                    ·
                      rfl

theorem cell22_2106657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2106657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106657 prefixEnd_2106657 := by exact prefixLift 2106657
  have htrace : WordTrace (prefixWord ++ tailWord_2106657) baseStart_2106657 baseEnd_2106657 := by
    simpa [prefixWord, tailWord_2106657, baseEnd_2106657] using wordTrace_append hprefix tailTrace_2106657
  have hstable : (prefixWord ++ tailWord_2106657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106657).length < 2 ^ (prefixWord ++ tailWord_2106657).sum := by decide
  have hdescent : baseEnd_2106657 < baseStart_2106657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106672 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_2106672 : Nat := 118140960795 + 2106672 * 2 ^ 59
def prefixEnd_2106672 : Nat := 4983230072969 + 3 ^ 40 * 2106672 * 2
def baseEnd_2106672 : Nat := 721156878245791246541065

theorem tailTrace_2106672 : CollatzResearch.WordTrace tailWord_2106672 prefixEnd_2106672 721156878245791246541065 := by
  unfold tailWord_2106672
  simp only [CollatzResearch.WordTrace]
  refine ⟨38418320111947304889145135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51224426815929739852193513 38418320111947304889145135)
  ·
    refine ⟨57627480167920957333717703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38418320111947304889145135 57627480167920957333717703)
    ·
      refine ⟨86441220251881436000576555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57627480167920957333717703 86441220251881436000576555)
      ·
        refine ⟨129661830377822154000864833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86441220251881436000576555 129661830377822154000864833)
        ·
          refine ⟨97246372783366615500648625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129661830377822154000864833 97246372783366615500648625)
          ·
            refine ⟨72934779587524961625486469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97246372783366615500648625 72934779587524961625486469)
            ·
              refine ⟨13675271172660930304778713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72934779587524961625486469 13675271172660930304778713)
              ·
                refine ⟨10256453379495697728584035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13675271172660930304778713 10256453379495697728584035)
                ·
                  refine ⟨15384680069243546592876053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10256453379495697728584035 15384680069243546592876053)
                  ·
                    refine ⟨721156878245791246541065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15384680069243546592876053 721156878245791246541065)
                    ·
                      rfl

theorem cell22_2106672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_2106672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106672 prefixEnd_2106672 := by exact prefixLift 2106672
  have htrace : WordTrace (prefixWord ++ tailWord_2106672) baseStart_2106672 baseEnd_2106672 := by
    simpa [prefixWord, tailWord_2106672, baseEnd_2106672] using wordTrace_append hprefix tailTrace_2106672
  have hstable : (prefixWord ++ tailWord_2106672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106672).length < 2 ^ (prefixWord ++ tailWord_2106672).sum := by decide
  have hdescent : baseEnd_2106672 < baseStart_2106672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106674 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_2106674 : Nat := 118140960795 + 2106674 * 2 ^ 59
def prefixEnd_2106674 : Nat := 4983230072969 + 3 ^ 40 * 2106674 * 2
def baseEnd_2106674 : Nat := 721157562886663907991059

theorem tailTrace_2106674 : CollatzResearch.WordTrace tailWord_2106674 prefixEnd_2106674 721157562886663907991059 := by
  unfold tailWord_2106674
  simp only [CollatzResearch.WordTrace]
  refine ⟨19209178292471841029965769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51224475446591576079908717 19209178292471841029965769)
  ·
    refine ⟨14406883719353880772474327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19209178292471841029965769 14406883719353880772474327)
    ·
      refine ⟨21610325579030821158711491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14406883719353880772474327 21610325579030821158711491)
      ·
        refine ⟨32415488368546231738067237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21610325579030821158711491 32415488368546231738067237)
        ·
          refine ⟨6077904069102418450887607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32415488368546231738067237 6077904069102418450887607)
          ·
            refine ⟨9116856103653627676331411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6077904069102418450887607 9116856103653627676331411)
            ·
              refine ⟨13675284155480441514497117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9116856103653627676331411 13675284155480441514497117)
              ·
                refine ⟨5128231558305165567936419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13675284155480441514497117 5128231558305165567936419)
                ·
                  refine ⟨7692347337457748351904629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128231558305165567936419 7692347337457748351904629)
                  ·
                    refine ⟨721157562886663907991059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7692347337457748351904629 721157562886663907991059)
                    ·
                      rfl

theorem cell22_2106674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_2106674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106674 prefixEnd_2106674 := by exact prefixLift 2106674
  have htrace : WordTrace (prefixWord ++ tailWord_2106674) baseStart_2106674 baseEnd_2106674 := by
    simpa [prefixWord, tailWord_2106674, baseEnd_2106674] using wordTrace_append hprefix tailTrace_2106674
  have hstable : (prefixWord ++ tailWord_2106674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106674).length < 2 ^ (prefixWord ++ tailWord_2106674).sum := by decide
  have hdescent : baseEnd_2106674 < baseStart_2106674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106783 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 5]
def baseStart_2106783 : Nat := 118140960795 + 2106783 * 2 ^ 59
def prefixEnd_2106783 : Nat := 4983230072969 + 3 ^ 40 * 2106783 * 2
def baseEnd_2106783 : Nat := 240398291938074652338575

theorem tailTrace_2106783 : CollatzResearch.WordTrace tailWord_2106783 prefixEnd_2106783 240398291938074652338575 := by
  unfold tailWord_2106783
  simp only [CollatzResearch.WordTrace]
  refine ⟨76840688726492475735581003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51227125817661650490387335 76840688726492475735581003)
  ·
    refine ⟨115261033089738713603371505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76840688726492475735581003 115261033089738713603371505)
    ·
      refine ⟨86445774817304035202528629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115261033089738713603371505 86445774817304035202528629)
      ·
        refine ⟨8104291389122253300237059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86445774817304035202528629 8104291389122253300237059)
        ·
          refine ⟨12156437083683379950355589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104291389122253300237059 12156437083683379950355589)
          ·
            refine ⟨2279331953190633740691673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12156437083683379950355589 2279331953190633740691673)
            ·
              refine ⟨1709498964892975305518755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2279331953190633740691673 1709498964892975305518755)
              ·
                refine ⟨2564248447339462958278133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709498964892975305518755 2564248447339462958278133)
                ·
                  refine ⟨240398291938074652338575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2564248447339462958278133 240398291938074652338575)
                  ·
                    rfl

theorem cell22_2106783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 5].length) (baseStart_2106783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106783 prefixEnd_2106783 := by exact prefixLift 2106783
  have htrace : WordTrace (prefixWord ++ tailWord_2106783) baseStart_2106783 baseEnd_2106783 := by
    simpa [prefixWord, tailWord_2106783, baseEnd_2106783] using wordTrace_append hprefix tailTrace_2106783
  have hstable : (prefixWord ++ tailWord_2106783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106783).length < 2 ^ (prefixWord ++ tailWord_2106783).sum := by decide
  have hdescent : baseEnd_2106783 < baseStart_2106783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106796 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 1, 4]
def baseStart_2106796 : Nat := 118140960795 + 2106796 * 2 ^ 59
def prefixEnd_2106796 : Nat := 4983230072969 + 3 ^ 40 * 2106796 * 2
def baseEnd_2106796 : Nat := 721199325979896256440685

theorem tailTrace_2106796 : CollatzResearch.WordTrace tailWord_2106796 prefixEnd_2106796 721199325979896256440685 := by
  unfold tailWord_2106796
  simp only [CollatzResearch.WordTrace]
  refine ⟨38420581437722689477902121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51227441916963585970536161 38420581437722689477902121)
  ·
    refine ⟨28815436078292017108426591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38420581437722689477902121 28815436078292017108426591)
    ·
      refine ⟨43223154117438025662639887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28815436078292017108426591 43223154117438025662639887)
      ·
        refine ⟨64834731176157038493959831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43223154117438025662639887 64834731176157038493959831)
        ·
          refine ⟨97252096764235557740939747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64834731176157038493959831 97252096764235557740939747)
          ·
            refine ⟨145878145146353336611409621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97252096764235557740939747 145878145146353336611409621)
            ·
              refine ⟨3419019026867656326829913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 145878145146353336611409621 3419019026867656326829913)
              ·
                refine ⟨2564264270150742245122435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419019026867656326829913 2564264270150742245122435)
                ·
                  refine ⟨3846396405226113367683653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564264270150742245122435 3846396405226113367683653)
                  ·
                    refine ⟨721199325979896256440685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3846396405226113367683653 721199325979896256440685)
                    ·
                      rfl

theorem cell22_2106796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_2106796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106796 prefixEnd_2106796 := by exact prefixLift 2106796
  have htrace : WordTrace (prefixWord ++ tailWord_2106796) baseStart_2106796 baseEnd_2106796 := by
    simpa [prefixWord, tailWord_2106796, baseEnd_2106796] using wordTrace_append hprefix tailTrace_2106796
  have hstable : (prefixWord ++ tailWord_2106796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106796).length < 2 ^ (prefixWord ++ tailWord_2106796).sum := by decide
  have hdescent : baseEnd_2106796 < baseStart_2106796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106813 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_2106813 : Nat := 118140960795 + 2106813 * 2 ^ 59
def prefixEnd_2106813 : Nat := 4983230072969 + 3 ^ 40 * 2106813 * 2
def baseEnd_2106813 : Nat := 721205145427313878765633

theorem tailTrace_2106813 : CollatzResearch.WordTrace tailWord_2106813 prefixEnd_2106813 721205145427313878765633 := by
  unfold tailWord_2106813
  simp only [CollatzResearch.WordTrace]
  refine ⟨76841782916383790859173093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51227855277589193906115395 76841782916383790859173093)
  ·
    refine ⟨14407834296821960786094955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76841782916383790859173093 14407834296821960786094955)
    ·
      refine ⟨21611751445232941179142433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14407834296821960786094955 21611751445232941179142433)
      ·
        refine ⟨16208813583924705884356825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21611751445232941179142433 16208813583924705884356825)
        ·
          refine ⟨12156610187943529413267619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16208813583924705884356825 12156610187943529413267619)
          ·
            refine ⟨18234915281915294119901429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12156610187943529413267619 18234915281915294119901429)
            ·
              refine ⟨1709523307679558823740759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18234915281915294119901429 1709523307679558823740759)
              ·
                refine ⟨2564284961519338235611139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709523307679558823740759 2564284961519338235611139)
                ·
                  refine ⟨3846427442279007353416709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564284961519338235611139 3846427442279007353416709)
                  ·
                    refine ⟨721205145427313878765633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3846427442279007353416709 721205145427313878765633)
                    ·
                      rfl

theorem cell22_2106813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_2106813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106813 prefixEnd_2106813 := by exact prefixLift 2106813
  have htrace : WordTrace (prefixWord ++ tailWord_2106813) baseStart_2106813 baseEnd_2106813 := by
    simpa [prefixWord, tailWord_2106813, baseEnd_2106813] using wordTrace_append hprefix tailTrace_2106813
  have hstable : (prefixWord ++ tailWord_2106813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106813).length < 2 ^ (prefixWord ++ tailWord_2106813).sum := by decide
  have hdescent : baseEnd_2106813 < baseStart_2106813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106828 : List Nat := [2, 2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_2106828 : Nat := 118140960795 + 2106828 * 2 ^ 59
def prefixEnd_2106828 : Nat := 4983230072969 + 3 ^ 40 * 2106828 * 2
def baseEnd_2106828 : Nat := 240403426744619613213529

theorem tailTrace_2106828 : CollatzResearch.WordTrace tailWord_2106828 prefixEnd_2106828 240403426744619613213529 := by
  unfold tailWord_2106828
  simp only [CollatzResearch.WordTrace]
  refine ⟨38421165005664724210484569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51228220007552965613979425 38421165005664724210484569)
  ·
    refine ⟨28815873754248543157863427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38421165005664724210484569 28815873754248543157863427)
    ·
      refine ⟨43223810631372814736795141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28815873754248543157863427 43223810631372814736795141)
      ·
        refine ⟨8104464493382402763149089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43223810631372814736795141 8104464493382402763149089)
        ·
          refine ⟨6078348370036802072361817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8104464493382402763149089 6078348370036802072361817)
          ·
            refine ⟨4558761277527601554271363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078348370036802072361817 4558761277527601554271363)
            ·
              refine ⟨6838141916291402331407045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558761277527601554271363 6838141916291402331407045)
              ·
                refine ⟨1282151609304637937138821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6838141916291402331407045 1282151609304637937138821)
                ·
                  refine ⟨240403426744619613213529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282151609304637937138821 240403426744619613213529)
                  ·
                    rfl

theorem cell22_2106828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_2106828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106828 prefixEnd_2106828 := by exact prefixLift 2106828
  have htrace : WordTrace (prefixWord ++ tailWord_2106828) baseStart_2106828 baseEnd_2106828 := by
    simpa [prefixWord, tailWord_2106828, baseEnd_2106828] using wordTrace_append hprefix tailTrace_2106828
  have hstable : (prefixWord ++ tailWord_2106828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106828).length < 2 ^ (prefixWord ++ tailWord_2106828).sum := by decide
  have hdescent : baseEnd_2106828 < baseStart_2106828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106856 : List Nat := [2, 1, 4, 1, 1, 2, 5, 6]
def baseStart_2106856 : Nat := 118140960795 + 2106856 * 2 ^ 59
def prefixEnd_2106856 : Nat := 4983230072969 + 3 ^ 40 * 2106856 * 2
def baseEnd_2106856 : Nat := 80135540578452899993389

theorem tailTrace_2106856 : CollatzResearch.WordTrace tailWord_2106856 prefixEnd_2106856 80135540578452899993389 := by
  unfold tailWord_2106856
  simp only [CollatzResearch.WordTrace]
  refine ⟨38421675627614004601494211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51228900836818672801992281 38421675627614004601494211)
  ·
    refine ⟨57632513441421006902241317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38421675627614004601494211 57632513441421006902241317)
    ·
      refine ⟨10806096270266438794170247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57632513441421006902241317 10806096270266438794170247)
      ·
        refine ⟨16209144405399658191255371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806096270266438794170247 16209144405399658191255371)
        ·
          refine ⟨24313716608099487286883057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16209144405399658191255371 24313716608099487286883057)
          ·
            refine ⟨18235287456074615465162293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24313716608099487286883057 18235287456074615465162293)
            ·
              refine ⟨1709558199006995199858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18235287456074615465162293 1709558199006995199858965)
              ·
                refine ⟨80135540578452899993389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1709558199006995199858965 80135540578452899993389)
                ·
                  rfl

theorem cell22_2106856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_2106856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106856 prefixEnd_2106856 := by exact prefixLift 2106856
  have htrace : WordTrace (prefixWord ++ tailWord_2106856) baseStart_2106856 baseEnd_2106856 := by
    simpa [prefixWord, tailWord_2106856, baseEnd_2106856] using wordTrace_append hprefix tailTrace_2106856
  have hstable : (prefixWord ++ tailWord_2106856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106856).length < 2 ^ (prefixWord ++ tailWord_2106856).sum := by decide
  have hdescent : baseEnd_2106856 < baseStart_2106856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106961 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_2106961 : Nat := 118140960795 + 2106961 * 2 ^ 59
def prefixEnd_2106961 : Nat := 4983230072969 + 3 ^ 40 * 2106961 * 2
def baseEnd_2106961 : Nat := 721255808851890826065179

theorem tailTrace_2106961 : CollatzResearch.WordTrace tailWord_2106961 prefixEnd_2106961 721255808851890826065179 := by
  unfold tailWord_2106961
  simp only [CollatzResearch.WordTrace]
  refine ⟨76847180919847612135560737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51231453946565074757040491 76847180919847612135560737)
  ·
    refine ⟨57635385689885709101670553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76847180919847612135560737 57635385689885709101670553)
    ·
      refine ⟨43226539267414281826252915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57635385689885709101670553 43226539267414281826252915)
      ·
        refine ⟨64839808901121422739379373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43226539267414281826252915 64839808901121422739379373)
        ·
          refine ⟨24314928337920533527267265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64839808901121422739379373 24314928337920533527267265)
          ·
            refine ⟨18236196253440400145450449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24314928337920533527267265 18236196253440400145450449)
            ·
              refine ⟨13677147190080300109087837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18236196253440400145450449 13677147190080300109087837)
              ·
                refine ⟨5128930196280112540907939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13677147190080300109087837 5128930196280112540907939)
                ·
                  refine ⟨7693395294420168811361909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128930196280112540907939 7693395294420168811361909)
                  ·
                    refine ⟨721255808851890826065179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7693395294420168811361909 721255808851890826065179)
                    ·
                      rfl

theorem cell22_2106961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_2106961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106961 prefixEnd_2106961 := by exact prefixLift 2106961
  have htrace : WordTrace (prefixWord ++ tailWord_2106961) baseStart_2106961 baseEnd_2106961 := by
    simpa [prefixWord, tailWord_2106961, baseEnd_2106961] using wordTrace_append hprefix tailTrace_2106961
  have hstable : (prefixWord ++ tailWord_2106961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106961).length < 2 ^ (prefixWord ++ tailWord_2106961).sum := by decide
  have hdescent : baseEnd_2106961 < baseStart_2106961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2106997 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 4]
def baseStart_2106997 : Nat := 118140960795 + 2106997 * 2 ^ 59
def prefixEnd_2106997 : Nat := 4983230072969 + 3 ^ 40 * 2106997 * 2
def baseEnd_2106997 : Nat := 240422710795866244055023

theorem tailTrace_2106997 : CollatzResearch.WordTrace tailWord_2106997 prefixEnd_2106997 240422710795866244055023 := by
  unfold tailWord_2106997
  simp only [CollatzResearch.WordTrace]
  refine ⟨76848493947717190283871245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51232329298478126855914163 76848493947717190283871245)
  ·
    refine ⟨28818185230393946356451717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76848493947717190283871245 28818185230393946356451717)
    ·
      refine ⟨5403409730698864941834697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28818185230393946356451717 5403409730698864941834697)
      ·
        refine ⟨4052557298024148706376023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5403409730698864941834697 4052557298024148706376023)
        ·
          refine ⟨6078835947036223059564035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052557298024148706376023 6078835947036223059564035)
          ·
            refine ⟨9118253920554334589346053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078835947036223059564035 9118253920554334589346053)
            ·
              refine ⟨1709672610103937735502385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9118253920554334589346053 1709672610103937735502385)
              ·
                refine ⟨1282254457577953301626789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709672610103937735502385 1282254457577953301626789)
                ·
                  refine ⟨240422710795866244055023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282254457577953301626789 240422710795866244055023)
                  ·
                    rfl

theorem cell22_2106997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_2106997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2106997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2106997 prefixEnd_2106997 := by exact prefixLift 2106997
  have htrace : WordTrace (prefixWord ++ tailWord_2106997) baseStart_2106997 baseEnd_2106997 := by
    simpa [prefixWord, tailWord_2106997, baseEnd_2106997] using wordTrace_append hprefix tailTrace_2106997
  have hstable : (prefixWord ++ tailWord_2106997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2106997).length < 2 ^ (prefixWord ++ tailWord_2106997).sum := by decide
  have hdescent : baseEnd_2106997 < baseStart_2106997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2106997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107053 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2107053 : Nat := 118140960795 + 2107053 * 2 ^ 59
def prefixEnd_2107053 : Nat := 4983230072969 + 3 ^ 40 * 2107053 * 2
def baseEnd_2107053 : Nat := 240429100777344417588299

theorem tailTrace_2107053 : CollatzResearch.WordTrace tailWord_2107053 prefixEnd_2107053 240429100777344417588299 := by
  unfold tailWord_2107053
  simp only [CollatzResearch.WordTrace]
  refine ⟨76850536435514311847909813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51233690957009541231939875 76850536435514311847909813)
  ·
    refine ⟨7204737790829466735741545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76850536435514311847909813 7204737790829466735741545)
    ·
      refine ⟨5403553343122100051806159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7204737790829466735741545 5403553343122100051806159)
      ·
        refine ⟨8105330014683150077709239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5403553343122100051806159 8105330014683150077709239)
        ·
          refine ⟨12157995022024725116563859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8105330014683150077709239 12157995022024725116563859)
          ·
            refine ⟨18236992533037087674845789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12157995022024725116563859 18236992533037087674845789)
            ·
              refine ⟨6838872199888907878067171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18236992533037087674845789 6838872199888907878067171)
              ·
                refine ⟨10258308299833361817100757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838872199888907878067171 10258308299833361817100757)
                ·
                  refine ⟨240429100777344417588299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10258308299833361817100757 240429100777344417588299)
                  ·
                    rfl

theorem cell22_2107053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2107053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107053 prefixEnd_2107053 := by exact prefixLift 2107053
  have htrace : WordTrace (prefixWord ++ tailWord_2107053) baseStart_2107053 baseEnd_2107053 := by
    simpa [prefixWord, tailWord_2107053, baseEnd_2107053] using wordTrace_append hprefix tailTrace_2107053
  have hstable : (prefixWord ++ tailWord_2107053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107053).length < 2 ^ (prefixWord ++ tailWord_2107053).sum := by decide
  have hdescent : baseEnd_2107053 < baseStart_2107053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107068 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 2, 5]
def baseStart_2107068 : Nat := 118140960795 + 2107068 * 2 ^ 59
def prefixEnd_2107068 : Nat := 4983230072969 + 3 ^ 40 * 2107068 * 2
def baseEnd_2107068 : Nat := 721292437138578213639851

theorem tailTrace_2107068 : CollatzResearch.WordTrace tailWord_2107068 prefixEnd_2107068 721292437138578213639851 := by
  unfold tailWord_2107068
  simp only [CollatzResearch.WordTrace]
  refine ⟨38425541765229984704852929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51234055686973312939803905 38425541765229984704852929)
  ·
    refine ⟨28819156323922488528639697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38425541765229984704852929 28819156323922488528639697)
    ·
      refine ⟨21614367242941866396479773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28819156323922488528639697 21614367242941866396479773)
      ·
        refine ⟨8105387716103199898679915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21614367242941866396479773 8105387716103199898679915)
        ·
          refine ⟨12158081574154799848019873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8105387716103199898679915 12158081574154799848019873)
          ·
            refine ⟨9118561180616099886014905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12158081574154799848019873 9118561180616099886014905)
            ·
              refine ⟨6838920885462074914511179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9118561180616099886014905 6838920885462074914511179)
              ·
                refine ⟨10258381328193112371766769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838920885462074914511179 10258381328193112371766769)
                ·
                  refine ⟨7693785996144834278825077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10258381328193112371766769 7693785996144834278825077)
                  ·
                    refine ⟨721292437138578213639851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7693785996144834278825077 721292437138578213639851)
                    ·
                      rfl

theorem cell22_2107068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_2107068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107068 prefixEnd_2107068 := by exact prefixLift 2107068
  have htrace : WordTrace (prefixWord ++ tailWord_2107068) baseStart_2107068 baseEnd_2107068 := by
    simpa [prefixWord, tailWord_2107068, baseEnd_2107068] using wordTrace_append hprefix tailTrace_2107068
  have hstable : (prefixWord ++ tailWord_2107068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107068).length < 2 ^ (prefixWord ++ tailWord_2107068).sum := by decide
  have hdescent : baseEnd_2107068 < baseStart_2107068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107134 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2107134 : Nat := 118140960795 + 2107134 * 2 ^ 59
def prefixEnd_2107134 : Nat := 4983230072969 + 3 ^ 40 * 2107134 * 2
def baseEnd_2107134 : Nat := 721315030287376041489649

theorem tailTrace_2107134 : CollatzResearch.WordTrace tailWord_2107134 prefixEnd_2107134 721315030287376041489649 := by
  unfold tailWord_2107134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606686343527607835201057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51235660498813908454405637 9606686343527607835201057)
  ·
    refine ⟨7205014757645705876400793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9606686343527607835201057 7205014757645705876400793)
    ·
      refine ⟨5403761068234279407300595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7205014757645705876400793 5403761068234279407300595)
      ·
        refine ⟨8105641602351419110950893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5403761068234279407300595 8105641602351419110950893)
        ·
          refine ⟨3039615600881782166606585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8105641602351419110950893 3039615600881782166606585)
          ·
            refine ⟨2279711700661336624954939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3039615600881782166606585 2279711700661336624954939)
            ·
              refine ⟨3419567550992004937432409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279711700661336624954939 3419567550992004937432409)
              ·
                refine ⟨2564675663244003703074307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419567550992004937432409 2564675663244003703074307)
                ·
                  refine ⟨3847013494866005554611461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564675663244003703074307 3847013494866005554611461)
                  ·
                    refine ⟨721315030287376041489649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847013494866005554611461 721315030287376041489649)
                    ·
                      rfl

theorem cell22_2107134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2107134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107134 prefixEnd_2107134 := by exact prefixLift 2107134
  have htrace : WordTrace (prefixWord ++ tailWord_2107134) baseStart_2107134 baseEnd_2107134 := by
    simpa [prefixWord, tailWord_2107134, baseEnd_2107134] using wordTrace_append hprefix tailTrace_2107134
  have hstable : (prefixWord ++ tailWord_2107134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107134).length < 2 ^ (prefixWord ++ tailWord_2107134).sum := by decide
  have hdescent : baseEnd_2107134 < baseStart_2107134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107166 : List Nat := [4, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_2107166 : Nat := 118140960795 + 2107166 * 2 ^ 59
def prefixEnd_2107166 : Nat := 4983230072969 + 3 ^ 40 * 2107166 * 2
def baseEnd_2107166 : Nat := 240441994847112874896517

theorem tailTrace_2107166 : CollatzResearch.WordTrace tailWord_2107166 prefixEnd_2107166 240441994847112874896517 := by
  unfold tailWord_2107166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606832235513116518346669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51236438589403288097848901 9606832235513116518346669)
  ·
    refine ⟨3602562088317418694380001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9606832235513116518346669 3602562088317418694380001)
    ·
      refine ⟨2701921566238064020785001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3602562088317418694380001 2701921566238064020785001)
      ·
        refine ⟨2026441174678548015588751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701921566238064020785001 2026441174678548015588751)
        ·
          refine ⟨3039661762017822023383127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026441174678548015588751 3039661762017822023383127)
          ·
            refine ⟨4559492643026733035074691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039661762017822023383127 4559492643026733035074691)
            ·
              refine ⟨6839238964540099552612037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559492643026733035074691 6839238964540099552612037)
              ·
                refine ⟨1282357305851268666114757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6839238964540099552612037 1282357305851268666114757)
                ·
                  refine ⟨240441994847112874896517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282357305851268666114757 240441994847112874896517)
                  ·
                    rfl

theorem cell22_2107166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_2107166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107166 prefixEnd_2107166 := by exact prefixLift 2107166
  have htrace : WordTrace (prefixWord ++ tailWord_2107166) baseStart_2107166 baseEnd_2107166 := by
    simpa [prefixWord, tailWord_2107166, baseEnd_2107166] using wordTrace_append hprefix tailTrace_2107166
  have hstable : (prefixWord ++ tailWord_2107166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107166).length < 2 ^ (prefixWord ++ tailWord_2107166).sum := by decide
  have hdescent : baseEnd_2107166 < baseStart_2107166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107173 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_2107173 : Nat := 118140960795 + 2107173 * 2 ^ 59
def prefixEnd_2107173 : Nat := 4983230072969 + 3 ^ 40 * 2107173 * 2
def baseEnd_2107173 : Nat := 721328380784392939764529

theorem tailTrace_2107173 : CollatzResearch.WordTrace tailWord_2107173 prefixEnd_2107173 721328380784392939764529 := by
  unfold tailWord_2107173
  simp only [CollatzResearch.WordTrace]
  refine ⟨76854913195079572342278173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51236608796719714894852115 76854913195079572342278173)
  ·
    refine ⟨28820592448154839628354315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76854913195079572342278173 28820592448154839628354315)
    ·
      refine ⟨43230888672232259442531473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28820592448154839628354315 43230888672232259442531473)
      ·
        refine ⟨32423166504174194581898605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43230888672232259442531473 32423166504174194581898605)
        ·
          refine ⟨12158687439065322968211977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32423166504174194581898605 12158687439065322968211977)
          ·
            refine ⟨9119015579298992226158983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12158687439065322968211977 9119015579298992226158983)
            ·
              refine ⟨13678523368948488339238475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9119015579298992226158983 13678523368948488339238475)
              ·
                refine ⟨20517785053422732508857713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13678523368948488339238475 20517785053422732508857713)
                ·
                  refine ⟨15388338790067049381643285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20517785053422732508857713 15388338790067049381643285)
                  ·
                    refine ⟨721328380784392939764529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15388338790067049381643285 721328380784392939764529)
                    ·
                      rfl

theorem cell22_2107173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_2107173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107173 prefixEnd_2107173 := by exact prefixLift 2107173
  have htrace : WordTrace (prefixWord ++ tailWord_2107173) baseStart_2107173 baseEnd_2107173 := by
    simpa [prefixWord, tailWord_2107173, baseEnd_2107173] using wordTrace_append hprefix tailTrace_2107173
  have hstable : (prefixWord ++ tailWord_2107173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107173).length < 2 ^ (prefixWord ++ tailWord_2107173).sum := by decide
  have hdescent : baseEnd_2107173 < baseStart_2107173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107220 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2107220 : Nat := 118140960795 + 2107220 * 2 ^ 59
def prefixEnd_2107220 : Nat := 4983230072969 + 3 ^ 40 * 2107220 * 2
def baseEnd_2107220 : Nat := 721344469844900483839385

theorem tailTrace_2107220 : CollatzResearch.WordTrace tailWord_2107220 prefixEnd_2107220 721344469844900483839385 := by
  unfold tailWord_2107220
  simp only [CollatzResearch.WordTrace]
  refine ⟨38428313712954649684619557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51237751617272866246159409 38428313712954649684619557)
  ·
    refine ⟨7205308821178996815866167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38428313712954649684619557 7205308821178996815866167)
    ·
      refine ⟨10807963231768495223799251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7205308821178996815866167 10807963231768495223799251)
      ·
        refine ⟨16211944847652742835698877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10807963231768495223799251 16211944847652742835698877)
        ·
          refine ⟨6079479317869778563387079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16211944847652742835698877 6079479317869778563387079)
          ·
            refine ⟨9119218976804667845080619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6079479317869778563387079 9119218976804667845080619)
            ·
              refine ⟨13678828465207001767620929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9119218976804667845080619 13678828465207001767620929)
              ·
                refine ⟨10259121348905251325715697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13678828465207001767620929 10259121348905251325715697)
                ·
                  refine ⟨7694341011678938494286773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10259121348905251325715697 7694341011678938494286773)
                  ·
                    refine ⟨721344469844900483839385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7694341011678938494286773 721344469844900483839385)
                    ·
                      rfl

theorem cell22_2107220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2107220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107220 prefixEnd_2107220 := by exact prefixLift 2107220
  have htrace : WordTrace (prefixWord ++ tailWord_2107220) baseStart_2107220 baseEnd_2107220 := by
    simpa [prefixWord, tailWord_2107220, baseEnd_2107220] using wordTrace_append hprefix tailTrace_2107220
  have hstable : (prefixWord ++ tailWord_2107220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107220).length < 2 ^ (prefixWord ++ tailWord_2107220).sum := by decide
  have hdescent : baseEnd_2107220 < baseStart_2107220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107267 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 4]
def baseStart_2107267 : Nat := 118140960795 + 2107267 * 2 ^ 59
def prefixEnd_2107267 : Nat := 4983230072969 + 3 ^ 40 * 2107267 * 2
def baseEnd_2107267 : Nat := 240453519635136009304747

theorem tailTrace_2107267 : CollatzResearch.WordTrace tailWord_2107267 prefixEnd_2107267 240453519635136009304747 := by
  unfold tailWord_2107267
  simp only [CollatzResearch.WordTrace]
  refine ⟨76858341656739026396200055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51238894437826017597466703 76858341656739026396200055)
  ·
    refine ⟨115287512485108539594300083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76858341656739026396200055 115287512485108539594300083)
    ·
      refine ⟨172931268727662809391450125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115287512485108539594300083 172931268727662809391450125)
      ·
        refine ⟨64849225772873553521793797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172931268727662809391450125 64849225772873553521793797)
        ·
          refine ⟨12159229832413791285336337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64849225772873553521793797 12159229832413791285336337)
          ·
            refine ⟨9119422374310343464002253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12159229832413791285336337 9119422374310343464002253)
            ·
              refine ⟨3419783390366378799000845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9119422374310343464002253 3419783390366378799000845)
              ·
                refine ⟨1282418771387392049625317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3419783390366378799000845 1282418771387392049625317)
                ·
                  refine ⟨240453519635136009304747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282418771387392049625317 240453519635136009304747)
                  ·
                    rfl

theorem cell22_2107267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 4].length) (baseStart_2107267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107267 prefixEnd_2107267 := by exact prefixLift 2107267
  have htrace : WordTrace (prefixWord ++ tailWord_2107267) baseStart_2107267 baseEnd_2107267 := by
    simpa [prefixWord, tailWord_2107267, baseEnd_2107267] using wordTrace_append hprefix tailTrace_2107267
  have hstable : (prefixWord ++ tailWord_2107267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107267).length < 2 ^ (prefixWord ++ tailWord_2107267).sum := by decide
  have hdescent : baseEnd_2107267 < baseStart_2107267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107434 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2107434 : Nat := 118140960795 + 2107434 * 2 ^ 59
def prefixEnd_2107434 : Nat := 4983230072969 + 3 ^ 40 * 2107434 * 2
def baseEnd_2107434 : Nat := 721417726418275258988729

theorem tailTrace_2107434 : CollatzResearch.WordTrace tailWord_2107434 prefixEnd_2107434 721417726418275258988729 := by
  unfold tailWord_2107434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19216108161783503479382339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51242955098089342611686237 19216108161783503479382339)
  ·
    refine ⟨28824162242675255219073509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19216108161783503479382339 28824162242675255219073509)
    ·
      refine ⟨5404530420501610353576283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28824162242675255219073509 5404530420501610353576283)
      ·
        refine ⟨8106795630752415530364425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5404530420501610353576283 8106795630752415530364425)
        ·
          refine ⟨6080096723064311647773319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8106795630752415530364425 6080096723064311647773319)
          ·
            refine ⟨9120145084596467471659979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080096723064311647773319 9120145084596467471659979)
            ·
              refine ⟨13680217626894701207489969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120145084596467471659979 13680217626894701207489969)
              ·
                refine ⟨10260163220171025905617477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13680217626894701207489969 10260163220171025905617477)
                ·
                  refine ⟨1923780603782067357303277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10260163220171025905617477 1923780603782067357303277)
                  ·
                    refine ⟨721417726418275258988729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1923780603782067357303277 721417726418275258988729)
                    ·
                      rfl

theorem cell22_2107434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2107434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107434 prefixEnd_2107434 := by exact prefixLift 2107434
  have htrace : WordTrace (prefixWord ++ tailWord_2107434) baseStart_2107434 baseEnd_2107434 := by
    simpa [prefixWord, tailWord_2107434, baseEnd_2107434] using wordTrace_append hprefix tailTrace_2107434
  have hstable : (prefixWord ++ tailWord_2107434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107434).length < 2 ^ (prefixWord ++ tailWord_2107434).sum := by decide
  have hdescent : baseEnd_2107434 < baseStart_2107434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107449 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_2107449 : Nat := 118140960795 + 2107449 * 2 ^ 59
def prefixEnd_2107449 : Nat := 4983230072969 + 3 ^ 40 * 2107449 * 2
def baseEnd_2107449 : Nat := 721422861224820219863683

theorem tailTrace_2107449 : CollatzResearch.WordTrace tailWord_2107449 prefixEnd_2107449 721422861224820219863683 := by
  unfold tailWord_2107449
  simp only [CollatzResearch.WordTrace]
  refine ⟨76864979742079671479325401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51243319828053114319550267 76864979742079671479325401)
  ·
    refine ⟨57648734806559753609494051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76864979742079671479325401 57648734806559753609494051)
    ·
      refine ⟨86473102209839630414241077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57648734806559753609494051 86473102209839630414241077)
      ·
        refine ⟨8106853332172465351335101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86473102209839630414241077 8106853332172465351335101)
        ·
          refine ⟨3040069999564674506750663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8106853332172465351335101 3040069999564674506750663)
          ·
            refine ⟨4560104999347011760125995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040069999564674506750663 4560104999347011760125995)
            ·
              refine ⟨6840157499020517640188993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560104999347011760125995 6840157499020517640188993)
              ·
                refine ⟨5130118124265388230141745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6840157499020517640188993 5130118124265388230141745)
                ·
                  refine ⟨3847588593199041172606309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5130118124265388230141745 3847588593199041172606309)
                  ·
                    refine ⟨721422861224820219863683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847588593199041172606309 721422861224820219863683)
                    ·
                      rfl

theorem cell22_2107449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_2107449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107449 prefixEnd_2107449 := by exact prefixLift 2107449
  have htrace : WordTrace (prefixWord ++ tailWord_2107449) baseStart_2107449 baseEnd_2107449 := by
    simpa [prefixWord, tailWord_2107449, baseEnd_2107449] using wordTrace_append hprefix tailTrace_2107449
  have hstable : (prefixWord ++ tailWord_2107449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107449).length < 2 ^ (prefixWord ++ tailWord_2107449).sum := by decide
  have hdescent : baseEnd_2107449 < baseStart_2107449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107513 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 1, 3]
def baseStart_2107513 : Nat := 118140960795 + 2107513 * 2 ^ 59
def prefixEnd_2107513 : Nat := 4983230072969 + 3 ^ 40 * 2107513 * 2
def baseEnd_2107513 : Nat := 721444769732745386263487

theorem tailTrace_2107513 : CollatzResearch.WordTrace tailWord_2107513 prefixEnd_2107513 721444769732745386263487 := by
  unfold tailWord_2107513
  simp only [CollatzResearch.WordTrace]
  refine ⟨76867314013847810409655193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51244876009231873606436795 76867314013847810409655193)
  ·
    refine ⟨57650485510385857807241395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76867314013847810409655193 57650485510385857807241395)
    ·
      refine ⟨86475728265578786710862093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57650485510385857807241395 86475728265578786710862093)
      ·
        refine ⟨32428398099592045016573285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86475728265578786710862093 32428398099592045016573285)
        ·
          refine ⟨6080324643673508440607491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32428398099592045016573285 6080324643673508440607491)
          ·
            refine ⟨9120486965510262660911237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080324643673508440607491 9120486965510262660911237)
            ·
              refine ⟨1710091306033174248920857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9120486965510262660911237 1710091306033174248920857)
              ·
                refine ⟨1282568479524880686690643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710091306033174248920857 1282568479524880686690643)
                ·
                  refine ⟨1923852719287321030035965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282568479524880686690643 1923852719287321030035965)
                  ·
                    refine ⟨721444769732745386263487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1923852719287321030035965 721444769732745386263487)
                    ·
                      rfl

theorem cell22_2107513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 1, 3].length) (baseStart_2107513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107513 prefixEnd_2107513 := by exact prefixLift 2107513
  have htrace : WordTrace (prefixWord ++ tailWord_2107513) baseStart_2107513 baseEnd_2107513 := by
    simpa [prefixWord, tailWord_2107513, baseEnd_2107513] using wordTrace_append hprefix tailTrace_2107513
  have hstable : (prefixWord ++ tailWord_2107513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107513).length < 2 ^ (prefixWord ++ tailWord_2107513).sum := by decide
  have hdescent : baseEnd_2107513 < baseStart_2107513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107556 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_2107556 : Nat := 118140960795 + 2107556 * 2 ^ 59
def prefixEnd_2107556 : Nat := 4983230072969 + 3 ^ 40 * 2107556 * 2
def baseEnd_2107556 : Nat := 721459489511507607438355

theorem tailTrace_2107556 : CollatzResearch.WordTrace tailWord_2107556 prefixEnd_2107556 721459489511507607438355 := by
  unfold tailWord_2107556
  simp only [CollatzResearch.WordTrace]
  refine ⟨38434441176346014376735261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51245921568461352502313681 38434441176346014376735261)
  ·
    refine ⟨14412915441129755391275723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38434441176346014376735261 14412915441129755391275723)
    ·
      refine ⟨21619373161694633086913585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14412915441129755391275723 21619373161694633086913585)
      ·
        refine ⟨16214529871270974815185189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21619373161694633086913585 16214529871270974815185189)
        ·
          refine ⟨3040224350863307777847223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16214529871270974815185189 3040224350863307777847223)
          ·
            refine ⟨4560336526294961666770835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040224350863307777847223 4560336526294961666770835)
            ·
              refine ⟨6840504789442442500156253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560336526294961666770835 6840504789442442500156253)
              ·
                refine ⟨2565189296040915937558595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6840504789442442500156253 2565189296040915937558595)
                ·
                  refine ⟨3847783944061373906337893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565189296040915937558595 3847783944061373906337893)
                  ·
                    refine ⟨721459489511507607438355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847783944061373906337893 721459489511507607438355)
                    ·
                      rfl

theorem cell22_2107556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_2107556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107556 prefixEnd_2107556 := by exact prefixLift 2107556
  have htrace : WordTrace (prefixWord ++ tailWord_2107556) baseStart_2107556 baseEnd_2107556 := by
    simpa [prefixWord, tailWord_2107556, baseEnd_2107556] using wordTrace_append hprefix tailTrace_2107556
  have hstable : (prefixWord ++ tailWord_2107556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107556).length < 2 ^ (prefixWord ++ tailWord_2107556).sum := by decide
  have hdescent : baseEnd_2107556 < baseStart_2107556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107567 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_2107567 : Nat := 118140960795 + 2107567 * 2 ^ 59
def prefixEnd_2107567 : Nat := 4983230072969 + 3 ^ 40 * 2107567 * 2
def baseEnd_2107567 : Nat := 721463255036307245413321

theorem tailTrace_2107567 : CollatzResearch.WordTrace tailWord_2107567 prefixEnd_2107567 721463255036307245413321 := by
  unfold tailWord_2107567
  simp only [CollatzResearch.WordTrace]
  refine ⟨76869283555652177632120955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51246189037101451754747303 76869283555652177632120955)
  ·
    refine ⟨115303925333478266448181433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76869283555652177632120955 115303925333478266448181433)
    ·
      refine ⟨86477944000108699836136075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115303925333478266448181433 86477944000108699836136075)
      ·
        refine ⟨129716916000163049754204113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86477944000108699836136075 129716916000163049754204113)
        ·
          refine ⟨97287687000122287315653085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129716916000163049754204113 97287687000122287315653085)
          ·
            refine ⟨36482882625045857743369907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97287687000122287315653085 36482882625045857743369907)
            ·
              refine ⟨54724323937568786615054861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36482882625045857743369907 54724323937568786615054861)
              ·
                refine ⟨20521621476588294980645573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54724323937568786615054861 20521621476588294980645573)
                ·
                  refine ⟨3847804026860305308871045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20521621476588294980645573 3847804026860305308871045)
                  ·
                    refine ⟨721463255036307245413321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847804026860305308871045 721463255036307245413321)
                    ·
                      rfl

theorem cell22_2107567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_2107567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107567 prefixEnd_2107567 := by exact prefixLift 2107567
  have htrace : WordTrace (prefixWord ++ tailWord_2107567) baseStart_2107567 baseEnd_2107567 := by
    simpa [prefixWord, tailWord_2107567, baseEnd_2107567] using wordTrace_append hprefix tailTrace_2107567
  have hstable : (prefixWord ++ tailWord_2107567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107567).length < 2 ^ (prefixWord ++ tailWord_2107567).sum := by decide
  have hdescent : baseEnd_2107567 < baseStart_2107567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107605 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 4]
def baseStart_2107605 : Nat := 118140960795 + 2107605 * 2 ^ 59
def prefixEnd_2107605 : Nat := 4983230072969 + 3 ^ 40 * 2107605 * 2
def baseEnd_2107605 : Nat := 240492087737629270987735

theorem tailTrace_2107605 : CollatzResearch.WordTrace tailWord_2107605 prefixEnd_2107605 240492087737629270987735 := by
  unfold tailWord_2107605
  simp only [CollatzResearch.WordTrace]
  refine ⟨76870669529514510122004269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51247113019676340081336179 76870669529514510122004269)
  ·
    refine ⟨28826501073567941295751601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76870669529514510122004269 28826501073567941295751601)
    ·
      refine ⟨21619875805175955971813701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28826501073567941295751601 21619875805175955971813701)
      ·
        refine ⟨4053726713470491744715069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21619875805175955971813701 4053726713470491744715069)
        ·
          refine ⟨1520147517551434404268151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4053726713470491744715069 1520147517551434404268151)
          ·
            refine ⟨2280221276327151606402227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520147517551434404268151 2280221276327151606402227)
            ·
              refine ⟨3420331914490727409603341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280221276327151606402227 3420331914490727409603341)
              ·
                refine ⟨1282624467934022778601253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3420331914490727409603341 1282624467934022778601253)
                ·
                  refine ⟨240492087737629270987735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282624467934022778601253 240492087737629270987735)
                  ·
                    rfl

theorem cell22_2107605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_2107605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107605 prefixEnd_2107605 := by exact prefixLift 2107605
  have htrace : WordTrace (prefixWord ++ tailWord_2107605) baseStart_2107605 baseEnd_2107605 := by
    simpa [prefixWord, tailWord_2107605, baseEnd_2107605] using wordTrace_append hprefix tailTrace_2107605
  have hstable : (prefixWord ++ tailWord_2107605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107605).length < 2 ^ (prefixWord ++ tailWord_2107605).sum := by decide
  have hdescent : baseEnd_2107605 < baseStart_2107605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107627 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 7]
def baseStart_2107627 : Nat := 118140960795 + 2107627 * 2 ^ 59
def prefixEnd_2107627 : Nat := 4983230072969 + 3 ^ 40 * 2107627 * 2
def baseEnd_2107627 : Nat := 240494598087495696304379

theorem tailTrace_2107627 : CollatzResearch.WordTrace tailWord_2107627 prefixEnd_2107627 240494598087495696304379 := by
  unfold tailWord_2107627
  simp only [CollatzResearch.WordTrace]
  refine ⟨76871471935434807879305135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51247647956956538586203423 76871471935434807879305135)
  ·
    refine ⟨115307207903152211818957703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76871471935434807879305135 115307207903152211818957703)
    ·
      refine ⟨172960811854728317728436555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115307207903152211818957703 172960811854728317728436555)
      ·
        refine ⟨259441217782092476592654833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172960811854728317728436555 259441217782092476592654833)
        ·
          refine ⟨194580913336569357444491125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259441217782092476592654833 194580913336569357444491125)
          ·
            refine ⟨18241960625303377260421043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194580913336569357444491125 18241960625303377260421043)
            ·
              refine ⟨27362940937955065890631565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18241960625303377260421043 27362940937955065890631565)
              ·
                refine ⟨10261102851733149708986837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27362940937955065890631565 10261102851733149708986837)
                ·
                  refine ⟨240494598087495696304379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10261102851733149708986837 240494598087495696304379)
                  ·
                    rfl

theorem cell22_2107627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_2107627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107627 prefixEnd_2107627 := by exact prefixLift 2107627
  have htrace : WordTrace (prefixWord ++ tailWord_2107627) baseStart_2107627 baseEnd_2107627 := by
    simpa [prefixWord, tailWord_2107627, baseEnd_2107627] using wordTrace_append hprefix tailTrace_2107627
  have hstable : (prefixWord ++ tailWord_2107627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107627).length < 2 ^ (prefixWord ++ tailWord_2107627).sum := by decide
  have hdescent : baseEnd_2107627 < baseStart_2107627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107631 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 3, 3]
def baseStart_2107631 : Nat := 118140960795 + 2107631 * 2 ^ 59
def prefixEnd_2107631 : Nat := 4983230072969 + 3 ^ 40 * 2107631 * 2
def baseEnd_2107631 : Nat := 721485163544232411813125

theorem tailTrace_2107631 : CollatzResearch.WordTrace tailWord_2107631 prefixEnd_2107631 721485163544232411813125 := by
  unfold tailWord_2107631
  simp only [CollatzResearch.WordTrace]
  refine ⟨76871617827420316562450747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51247745218280211041633831 76871617827420316562450747)
  ·
    refine ⟨115307426741130474843676121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76871617827420316562450747 115307426741130474843676121)
    ·
      refine ⟨86480570055847856132757091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115307426741130474843676121 86480570055847856132757091)
      ·
        refine ⟨129720855083771784199135637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86480570055847856132757091 129720855083771784199135637)
        ·
          refine ⟨6080665082051802384334483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129720855083771784199135637 6080665082051802384334483)
          ·
            refine ⟨9120997623077703576501725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080665082051802384334483 9120997623077703576501725)
            ·
              refine ⟨3420374108654138841188147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9120997623077703576501725 3420374108654138841188147)
              ·
                refine ⟨5130561162981208261782221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420374108654138841188147 5130561162981208261782221)
                ·
                  refine ⟨1923960436117953098168333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5130561162981208261782221 1923960436117953098168333)
                  ·
                    refine ⟨721485163544232411813125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1923960436117953098168333 721485163544232411813125)
                    ·
                      rfl

theorem cell22_2107631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_2107631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107631 prefixEnd_2107631 := by exact prefixLift 2107631
  have htrace : WordTrace (prefixWord ++ tailWord_2107631) baseStart_2107631 baseEnd_2107631 := by
    simpa [prefixWord, tailWord_2107631, baseEnd_2107631] using wordTrace_append hprefix tailTrace_2107631
  have hstable : (prefixWord ++ tailWord_2107631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107631).length < 2 ^ (prefixWord ++ tailWord_2107631).sum := by decide
  have hdescent : baseEnd_2107631 < baseStart_2107631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107678 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2107678 : Nat := 118140960795 + 2107678 * 2 ^ 59
def prefixEnd_2107678 : Nat := 4983230072969 + 3 ^ 40 * 2107678 * 2
def baseEnd_2107678 : Nat := 240500417534913318629327

theorem tailTrace_2107678 : CollatzResearch.WordTrace tailWord_2107678 prefixEnd_2107678 240500417534913318629327 := by
  unfold tailWord_2107678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609166507281255448676461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51248888038833362392941125 9609166507281255448676461)
  ·
    refine ⟨3603437440230470793253673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9609166507281255448676461 3603437440230470793253673)
    ·
      refine ⟨2702578080172853094940255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3603437440230470793253673 2702578080172853094940255)
      ·
        refine ⟨4053867120259279642410383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702578080172853094940255 4053867120259279642410383)
        ·
          refine ⟨6080800680388919463615575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053867120259279642410383 6080800680388919463615575)
          ·
            refine ⟨9121201020583379195423363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080800680388919463615575 9121201020583379195423363)
            ·
              refine ⟨13681801530875068793135045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9121201020583379195423363 13681801530875068793135045)
              ·
                refine ⟨2565337787039075398712821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13681801530875068793135045 2565337787039075398712821)
                ·
                  refine ⟨240500417534913318629327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2565337787039075398712821 240500417534913318629327)
                  ·
                    rfl

theorem cell22_2107678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2107678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107678 prefixEnd_2107678 := by exact prefixLift 2107678
  have htrace : WordTrace (prefixWord ++ tailWord_2107678) baseStart_2107678 baseEnd_2107678 := by
    simpa [prefixWord, tailWord_2107678, baseEnd_2107678] using wordTrace_append hprefix tailTrace_2107678
  have hstable : (prefixWord ++ tailWord_2107678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107678).length < 2 ^ (prefixWord ++ tailWord_2107678).sum := by decide
  have hdescent : baseEnd_2107678 < baseStart_2107678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107682 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2107682 : Nat := 118140960795 + 2107682 * 2 ^ 59
def prefixEnd_2107682 : Nat := 4983230072969 + 3 ^ 40 * 2107682 * 2
def baseEnd_2107682 : Nat := 721502621886485278787969

theorem tailTrace_2107682 : CollatzResearch.WordTrace tailWord_2107682 prefixEnd_2107682 721502621886485278787969 := by
  unfold tailWord_2107682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19218369487558888068139325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51248985300157034848371533 19218369487558888068139325)
  ·
    refine ⟨7206888557834583025552247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19218369487558888068139325 7206888557834583025552247)
    ·
      refine ⟨10810332836751874538328371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7206888557834583025552247 10810332836751874538328371)
      ·
        refine ⟨16215499255127811807492557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10810332836751874538328371 16215499255127811807492557)
        ·
          refine ⟨6080812220672929427809709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16215499255127811807492557 6080812220672929427809709)
          ·
            refine ⟨2280304582752348535428641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6080812220672929427809709 2280304582752348535428641)
            ·
              refine ⟨1710228437064261401571481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280304582752348535428641 1710228437064261401571481)
              ·
                refine ⟨1282671327798196051178611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710228437064261401571481 1282671327798196051178611)
                ·
                  refine ⟨1924006991697294076767917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282671327798196051178611 1924006991697294076767917)
                  ·
                    refine ⟨721502621886485278787969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924006991697294076767917 721502621886485278787969)
                    ·
                      rfl

theorem cell22_2107682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2107682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107682 prefixEnd_2107682 := by exact prefixLift 2107682
  have htrace : WordTrace (prefixWord ++ tailWord_2107682) baseStart_2107682 baseEnd_2107682 := by
    simpa [prefixWord, tailWord_2107682, baseEnd_2107682] using wordTrace_append hprefix tailTrace_2107682
  have hstable : (prefixWord ++ tailWord_2107682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107682).length < 2 ^ (prefixWord ++ tailWord_2107682).sum := by decide
  have hdescent : baseEnd_2107682 < baseStart_2107682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107693 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2107693 : Nat := 118140960795 + 2107693 * 2 ^ 59
def prefixEnd_2107693 : Nat := 4983230072969 + 3 ^ 40 * 2107693 * 2
def baseEnd_2107693 : Nat := 721506387411284916762935

theorem tailTrace_2107693 : CollatzResearch.WordTrace tailWord_2107693 prefixEnd_2107693 721506387411284916762935 := by
  unfold tailWord_2107693
  simp only [CollatzResearch.WordTrace]
  refine ⟨76873879153195701151207733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51249252768797134100805155 76873879153195701151207733)
  ·
    refine ⟨7206926170612096982925725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76873879153195701151207733 7206926170612096982925725)
    ·
      refine ⟨2702597313979536368597147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7206926170612096982925725 2702597313979536368597147)
      ·
        refine ⟨4053895970969304552895721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702597313979536368597147 4053895970969304552895721)
        ·
          refine ⟨3040421978226978414671791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4053895970969304552895721 3040421978226978414671791)
          ·
            refine ⟨4560632967340467622007687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040421978226978414671791 4560632967340467622007687)
            ·
              refine ⟨6840949451010701433011531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560632967340467622007687 6840949451010701433011531)
              ·
                refine ⟨10261424176516052149517297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840949451010701433011531 10261424176516052149517297)
                ·
                  refine ⟨7696068132387039112137973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10261424176516052149517297 7696068132387039112137973)
                  ·
                    refine ⟨721506387411284916762935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7696068132387039112137973 721506387411284916762935)
                    ·
                      rfl

theorem cell22_2107693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2107693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107693 prefixEnd_2107693 := by exact prefixLift 2107693
  have htrace : WordTrace (prefixWord ++ tailWord_2107693) baseStart_2107693 baseEnd_2107693 := by
    simpa [prefixWord, tailWord_2107693, baseEnd_2107693] using wordTrace_append hprefix tailTrace_2107693
  have hstable : (prefixWord ++ tailWord_2107693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107693).length < 2 ^ (prefixWord ++ tailWord_2107693).sum := by decide
  have hdescent : baseEnd_2107693 < baseStart_2107693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107704 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 1, 5]
def baseStart_2107704 : Nat := 118140960795 + 2107704 * 2 ^ 59
def prefixEnd_2107704 : Nat := 4983230072969 + 3 ^ 40 * 2107704 * 2
def baseEnd_2107704 : Nat := 721510152936084554737901

theorem tailTrace_2107704 : CollatzResearch.WordTrace tailWord_2107704 prefixEnd_2107704 721510152936084554737901 := by
  unfold tailWord_2107704
  simp only [CollatzResearch.WordTrace]
  refine ⟨38437140178077925014929083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51249520237437233353238777 38437140178077925014929083)
  ·
    refine ⟨57655710267116887522393625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38437140178077925014929083 57655710267116887522393625)
    ·
      refine ⟨43241782700337665641795219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57655710267116887522393625 43241782700337665641795219)
      ·
        refine ⟨64862674050506498462692829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43241782700337665641795219 64862674050506498462692829)
        ·
          refine ⟨24323502768939936923509811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64862674050506498462692829 24323502768939936923509811)
          ·
            refine ⟨36485254153409905385264717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24323502768939936923509811 36485254153409905385264717)
            ·
              refine ⟨13681970307528714519474269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36485254153409905385264717 13681970307528714519474269)
              ·
                refine ⟨5130738865323267944802851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13681970307528714519474269 5130738865323267944802851)
                ·
                  refine ⟨7696108297984901917204277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130738865323267944802851 7696108297984901917204277)
                  ·
                    refine ⟨721510152936084554737901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7696108297984901917204277 721510152936084554737901)
                    ·
                      rfl

theorem cell22_2107704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_2107704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107704 prefixEnd_2107704 := by exact prefixLift 2107704
  have htrace : WordTrace (prefixWord ++ tailWord_2107704) baseStart_2107704 baseEnd_2107704 := by
    simpa [prefixWord, tailWord_2107704, baseEnd_2107704] using wordTrace_append hprefix tailTrace_2107704
  have hstable : (prefixWord ++ tailWord_2107704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107704).length < 2 ^ (prefixWord ++ tailWord_2107704).sum := by decide
  have hdescent : baseEnd_2107704 < baseStart_2107704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107719 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2107719 : Nat := 118140960795 + 2107719 * 2 ^ 59
def prefixEnd_2107719 : Nat := 4983230072969 + 3 ^ 40 * 2107719 * 2
def baseEnd_2107719 : Nat := 721515287742629515612855

theorem tailTrace_2107719 : CollatzResearch.WordTrace tailWord_2107719 prefixEnd_2107719 721515287742629515612855 := by
  unfold tailWord_2107719
  simp only [CollatzResearch.WordTrace]
  refine ⟨76874827451101507591654211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51249884967401005061102807 76874827451101507591654211)
  ·
    refine ⟨115312241176652261387481317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76874827451101507591654211 115312241176652261387481317)
    ·
      refine ⟨21621045220622299010152747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115312241176652261387481317 21621045220622299010152747)
      ·
        refine ⟨32431567830933448515229121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21621045220622299010152747 32431567830933448515229121)
        ·
          refine ⟨24323675873200086386421841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32431567830933448515229121 24323675873200086386421841)
          ·
            refine ⟨18242756904900064789816381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24323675873200086386421841 18242756904900064789816381)
            ·
              refine ⟨6841033839337524296181143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18242756904900064789816381 6841033839337524296181143)
              ·
                refine ⟨10261550759006286444271715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841033839337524296181143 10261550759006286444271715)
                ·
                  refine ⟨15392326138509429666407573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10261550759006286444271715 15392326138509429666407573)
                  ·
                    refine ⟨721515287742629515612855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15392326138509429666407573 721515287742629515612855)
                    ·
                      rfl

theorem cell22_2107719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2107719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107719 prefixEnd_2107719 := by exact prefixLift 2107719
  have htrace : WordTrace (prefixWord ++ tailWord_2107719) baseStart_2107719 baseEnd_2107719 := by
    simpa [prefixWord, tailWord_2107719, baseEnd_2107719] using wordTrace_append hprefix tailTrace_2107719
  have hstable : (prefixWord ++ tailWord_2107719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107719).length < 2 ^ (prefixWord ++ tailWord_2107719).sum := by decide
  have hdescent : baseEnd_2107719 < baseStart_2107719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107800 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 3, 3]
def baseStart_2107800 : Nat := 118140960795 + 2107800 * 2 ^ 59
def prefixEnd_2107800 : Nat := 4983230072969 + 3 ^ 40 * 2107800 * 2
def baseEnd_2107800 : Nat := 721543015697972304337607

theorem tailTrace_2107800 : CollatzResearch.WordTrace tailWord_2107800 prefixEnd_2107800 721543015697972304337607 := by
  unfold tailWord_2107800
  simp only [CollatzResearch.WordTrace]
  refine ⟨38438890881904029212676427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51251854509205372283568569 38438890881904029212676427)
  ·
    refine ⟨57658336322856043819014641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38438890881904029212676427 57658336322856043819014641)
    ·
      refine ⟨43243752242142032864260981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57658336322856043819014641 43243752242142032864260981)
      ·
        refine ⟨4054101772700815581024467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43243752242142032864260981 4054101772700815581024467)
        ·
          refine ⟨6081152659051223371536701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054101772700815581024467 6081152659051223371536701)
          ·
            refine ⟨2280432247144208764326263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6081152659051223371536701 2280432247144208764326263)
            ·
              refine ⟨3420648370716313146489395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280432247144208764326263 3420648370716313146489395)
              ·
                refine ⟨5130972556074469719734093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3420648370716313146489395 5130972556074469719734093)
                ·
                  refine ⟨1924114708527926144900285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5130972556074469719734093 1924114708527926144900285)
                  ·
                    refine ⟨721543015697972304337607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924114708527926144900285 721543015697972304337607)
                    ·
                      rfl

theorem cell22_2107800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_2107800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107800 prefixEnd_2107800 := by exact prefixLift 2107800
  have htrace : WordTrace (prefixWord ++ tailWord_2107800) baseStart_2107800 baseEnd_2107800 := by
    simpa [prefixWord, tailWord_2107800, baseEnd_2107800] using wordTrace_append hprefix tailTrace_2107800
  have hstable : (prefixWord ++ tailWord_2107800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107800).length < 2 ^ (prefixWord ++ tailWord_2107800).sum := by decide
  have hdescent : baseEnd_2107800 < baseStart_2107800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107826 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2107826 : Nat := 118140960795 + 2107826 * 2 ^ 59
def prefixEnd_2107826 : Nat := 4983230072969 + 3 ^ 40 * 2107826 * 2
def baseEnd_2107826 : Nat := 721551916029316903187527

theorem tailTrace_2107826 : CollatzResearch.WordTrace tailWord_2107826 prefixEnd_2107826 721551916029316903187527 := by
  unfold tailWord_2107826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19219682515428466216449833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51252486707809243243866221 19219682515428466216449833)
  ·
    refine ⟨14414761886571349662337375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19219682515428466216449833 14414761886571349662337375)
    ·
      refine ⟨21622142829857024493506063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14414761886571349662337375 21622142829857024493506063)
      ·
        refine ⟨32433214244785536740259095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21622142829857024493506063 32433214244785536740259095)
        ·
          refine ⟨48649821367178305110388643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32433214244785536740259095 48649821367178305110388643)
          ·
            refine ⟨72974732050767457665582965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48649821367178305110388643 72974732050767457665582965)
            ·
              refine ⟨6841381129759449156148403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72974732050767457665582965 6841381129759449156148403)
              ·
                refine ⟨10262071694639173734222605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6841381129759449156148403 10262071694639173734222605)
                ·
                  refine ⟨3848276885489690150333477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10262071694639173734222605 3848276885489690150333477)
                  ·
                    refine ⟨721551916029316903187527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3848276885489690150333477 721551916029316903187527)
                    ·
                      rfl

theorem cell22_2107826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2107826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107826 prefixEnd_2107826 := by exact prefixLift 2107826
  have htrace : WordTrace (prefixWord ++ tailWord_2107826) baseStart_2107826 baseEnd_2107826 := by
    simpa [prefixWord, tailWord_2107826, baseEnd_2107826] using wordTrace_append hprefix tailTrace_2107826
  have hstable : (prefixWord ++ tailWord_2107826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107826).length < 2 ^ (prefixWord ++ tailWord_2107826).sum := by decide
  have hdescent : baseEnd_2107826 < baseStart_2107826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107873 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_2107873 : Nat := 118140960795 + 2107873 * 2 ^ 59
def prefixEnd_2107873 : Nat := 4983230072969 + 3 ^ 40 * 2107873 * 2
def baseEnd_2107873 : Nat := 721568005089824447262383

theorem tailTrace_2107873 : CollatzResearch.WordTrace tailWord_2107873 prefixEnd_2107873 721568005089824447262383 := by
  unfold tailWord_2107873
  simp only [CollatzResearch.WordTrace]
  refine ⟨76880444292543591892760273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51253629528362394595173515 76880444292543591892760273)
  ·
    refine ⟨57660333219407693919570205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76880444292543591892760273 57660333219407693919570205)
    ·
      refine ⟨21622624957277885219838827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57660333219407693919570205 21622624957277885219838827)
      ·
        refine ⟨32433937435916827829758241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21622624957277885219838827 32433937435916827829758241)
        ·
          refine ⟨24325453076937620872318681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32433937435916827829758241 24325453076937620872318681)
          ·
            refine ⟨18244089807703215654239011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24325453076937620872318681 18244089807703215654239011)
            ·
              refine ⟨27366134711554823481358517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18244089807703215654239011 27366134711554823481358517)
              ·
                refine ⟨2565575129208264701377361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27366134711554823481358517 2565575129208264701377361)
                ·
                  refine ⟨1924181346906198526033021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565575129208264701377361 1924181346906198526033021)
                  ·
                    refine ⟨721568005089824447262383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924181346906198526033021 721568005089824447262383)
                    ·
                      rfl

theorem cell22_2107873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_2107873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107873 prefixEnd_2107873 := by exact prefixLift 2107873
  have htrace : WordTrace (prefixWord ++ tailWord_2107873) baseStart_2107873 baseEnd_2107873 := by
    simpa [prefixWord, tailWord_2107873, baseEnd_2107873] using wordTrace_append hprefix tailTrace_2107873
  have hstable : (prefixWord ++ tailWord_2107873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107873).length < 2 ^ (prefixWord ++ tailWord_2107873).sum := by decide
  have hdescent : baseEnd_2107873 < baseStart_2107873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107924 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_2107924 : Nat := 118140960795 + 2107924 * 2 ^ 59
def prefixEnd_2107924 : Nat := 4983230072969 + 3 ^ 40 * 2107924 * 2
def baseEnd_2107924 : Nat := 721585463432077314237227

theorem tailTrace_2107924 : CollatzResearch.WordTrace tailWord_2107924 prefixEnd_2107924 721585463432077314237227 := by
  unfold tailWord_2107924
  simp only [CollatzResearch.WordTrace]
  refine ⟨38441152207679413801433413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51254869610239218401911217 38441152207679413801433413)
  ·
    refine ⟨7207716038939890087768765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38441152207679413801433413 7207716038939890087768765)
    ·
      refine ⟨2702893514602458782913287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7207716038939890087768765 2702893514602458782913287)
      ·
        refine ⟨4054340271903688174369931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2702893514602458782913287 4054340271903688174369931)
        ·
          refine ⟨6081510407855532261554897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054340271903688174369931 6081510407855532261554897)
          ·
            refine ⟨4561132805891649196166173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6081510407855532261554897 4561132805891649196166173)
            ·
              refine ⟨1710424802209368448562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4561132805891649196166173 1710424802209368448562315)
              ·
                refine ⟨2565637203314052672843473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710424802209368448562315 2565637203314052672843473)
                ·
                  refine ⟨1924227902485539504632605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565637203314052672843473 1924227902485539504632605)
                  ·
                    refine ⟨721585463432077314237227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924227902485539504632605 721585463432077314237227)
                    ·
                      rfl

theorem cell22_2107924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_2107924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107924 prefixEnd_2107924 := by exact prefixLift 2107924
  have htrace : WordTrace (prefixWord ++ tailWord_2107924) baseStart_2107924 baseEnd_2107924 := by
    simpa [prefixWord, tailWord_2107924, baseEnd_2107924] using wordTrace_append hprefix tailTrace_2107924
  have hstable : (prefixWord ++ tailWord_2107924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107924).length < 2 ^ (prefixWord ++ tailWord_2107924).sum := by decide
  have hdescent : baseEnd_2107924 < baseStart_2107924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2107969 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2107969 : Nat := 118140960795 + 2107969 * 2 ^ 59
def prefixEnd_2107969 : Nat := 4983230072969 + 3 ^ 40 * 2107969 * 2
def baseEnd_2107969 : Nat := 721600867851712196862089

theorem tailTrace_2107969 : CollatzResearch.WordTrace tailWord_2107969 prefixEnd_2107969 721600867851712196862089 := by
  unfold tailWord_2107969
  simp only [CollatzResearch.WordTrace]
  refine ⟨76883945700195800288254961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51255963800130533525503307 76883945700195800288254961)
  ·
    refine ⟨57662959275146850216191221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76883945700195800288254961 57662959275146850216191221)
    ·
      refine ⟨5405902432045017207767927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57662959275146850216191221 5405902432045017207767927)
      ·
        refine ⟨8108853648067525811651891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405902432045017207767927 8108853648067525811651891)
        ·
          refine ⟨12163280472101288717477837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8108853648067525811651891 12163280472101288717477837)
          ·
            refine ⟨4561230177037983269054189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12163280472101288717477837 4561230177037983269054189)
            ·
              refine ⟨1710461316389243725895321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4561230177037983269054189 1710461316389243725895321)
              ·
                refine ⟨1282845987291932794421491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710461316389243725895321 1282845987291932794421491)
                ·
                  refine ⟨1924268980937899191632237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282845987291932794421491 1924268980937899191632237)
                  ·
                    refine ⟨721600867851712196862089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924268980937899191632237 721600867851712196862089)
                    ·
                      rfl

theorem cell22_2107969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2107969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2107969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2107969 prefixEnd_2107969 := by exact prefixLift 2107969
  have htrace : WordTrace (prefixWord ++ tailWord_2107969) baseStart_2107969 baseEnd_2107969 := by
    simpa [prefixWord, tailWord_2107969, baseEnd_2107969] using wordTrace_append hprefix tailTrace_2107969
  have hstable : (prefixWord ++ tailWord_2107969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2107969).length < 2 ^ (prefixWord ++ tailWord_2107969).sum := by decide
  have hdescent : baseEnd_2107969 < baseStart_2107969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2107969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108010 : List Nat := [3, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_2108010 : Nat := 118140960795 + 2108010 * 2 ^ 59
def prefixEnd_2108010 : Nat := 4983230072969 + 3 ^ 40 * 2108010 * 2
def baseEnd_2108010 : Nat := 240538300996533918862321

theorem tailTrace_2108010 : CollatzResearch.WordTrace tailWord_2108010 prefixEnd_2108010 240538300996533918862321 := by
  unfold tailWord_2108010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19221360273261816072624371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51256960728698176193664989 19221360273261816072624371)
  ·
    refine ⟨28832040409892724108936557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19221360273261816072624371 28832040409892724108936557)
    ·
      refine ⟨10812015153709771540851209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28832040409892724108936557 10812015153709771540851209)
      ·
        refine ⟨8109011365282328655638407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10812015153709771540851209 8109011365282328655638407)
        ·
          refine ⟨12163517047923492983457611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8109011365282328655638407 12163517047923492983457611)
          ·
            refine ⟨18245275571885239475186417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12163517047923492983457611 18245275571885239475186417)
            ·
              refine ⟨13683956678913929606389813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18245275571885239475186417 13683956678913929606389813)
              ·
                refine ⟨1282870938648180900599045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13683956678913929606389813 1282870938648180900599045)
                ·
                  refine ⟨240538300996533918862321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282870938648180900599045 240538300996533918862321)
                  ·
                    rfl

theorem cell22_2108010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_2108010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108010 prefixEnd_2108010 := by exact prefixLift 2108010
  have htrace : WordTrace (prefixWord ++ tailWord_2108010) baseStart_2108010 baseEnd_2108010 := by
    simpa [prefixWord, tailWord_2108010, baseEnd_2108010] using wordTrace_append hprefix tailTrace_2108010
  have hstable : (prefixWord ++ tailWord_2108010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108010).length < 2 ^ (prefixWord ++ tailWord_2108010).sum := by decide
  have hdescent : baseEnd_2108010 < baseStart_2108010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108023 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2108023 : Nat := 118140960795 + 2108023 * 2 ^ 59
def prefixEnd_2108023 : Nat := 4983230072969 + 3 ^ 40 * 2108023 * 2
def baseEnd_2108023 : Nat := 721619353155274056011923

theorem tailTrace_2108023 : CollatzResearch.WordTrace tailWord_2108023 prefixEnd_2108023 721619353155274056011923 := by
  unfold tailWord_2108023
  simp only [CollatzResearch.WordTrace]
  refine ⟨76885915242000167510720723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51257276828000111673813815 76885915242000167510720723)
  ·
    refine ⟨115328872863000251266081085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76885915242000167510720723 115328872863000251266081085)
    ·
      refine ⟨43248327323625094224780407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115328872863000251266081085 43248327323625094224780407)
      ·
        refine ⟨64872490985437641337170611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43248327323625094224780407 64872490985437641337170611)
        ·
          refine ⟨97308736478156462005755917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64872490985437641337170611 97308736478156462005755917)
          ·
            refine ⟨36490776179308673252158469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97308736478156462005755917 36490776179308673252158469)
            ·
              refine ⟨6842020533620376234779713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36490776179308673252158469 6842020533620376234779713)
              ·
                refine ⟨5131515400215282176084785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6842020533620376234779713 5131515400215282176084785)
                ·
                  refine ⟨3848636550161461632063589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131515400215282176084785 3848636550161461632063589)
                  ·
                    refine ⟨721619353155274056011923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3848636550161461632063589 721619353155274056011923)
                    ·
                      rfl

theorem cell22_2108023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2108023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108023 prefixEnd_2108023 := by exact prefixLift 2108023
  have htrace : WordTrace (prefixWord ++ tailWord_2108023) baseStart_2108023 baseEnd_2108023 := by
    simpa [prefixWord, tailWord_2108023, baseEnd_2108023] using wordTrace_append hprefix tailTrace_2108023
  have hstable : (prefixWord ++ tailWord_2108023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108023).length < 2 ^ (prefixWord ++ tailWord_2108023).sum := by decide
  have hdescent : baseEnd_2108023 < baseStart_2108023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108025 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_2108025 : Nat := 118140960795 + 2108025 * 2 ^ 59
def prefixEnd_2108025 : Nat := 4983230072969 + 3 ^ 40 * 2108025 * 2
def baseEnd_2108025 : Nat := 721620037796146717461917

theorem tailTrace_2108025 : CollatzResearch.WordTrace tailWord_2108025 prefixEnd_2108025 721620037796146717461917 := by
  unfold tailWord_2108025
  simp only [CollatzResearch.WordTrace]
  refine ⟨76885988187992921852293529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51257325458661947901529019 76885988187992921852293529)
  ·
    refine ⟨57664491140994691389220147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76885988187992921852293529 57664491140994691389220147)
    ·
      refine ⟨86496736711492037083830221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57664491140994691389220147 86496736711492037083830221)
      ·
        refine ⟨32436276266809513906436333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86496736711492037083830221 32436276266809513906436333)
        ·
          refine ⟨12163603600053567714913625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32436276266809513906436333 12163603600053567714913625)
          ·
            refine ⟨9122702700040175786185219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12163603600053567714913625 9122702700040175786185219)
            ·
              refine ⟨13684054050060263679277829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9122702700040175786185219 13684054050060263679277829)
              ·
                refine ⟨2565760134386299439864593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13684054050060263679277829 2565760134386299439864593)
                ·
                  refine ⟨1924320100789724579898445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565760134386299439864593 1924320100789724579898445)
                  ·
                    refine ⟨721620037796146717461917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924320100789724579898445 721620037796146717461917)
                    ·
                      rfl

theorem cell22_2108025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_2108025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108025 prefixEnd_2108025 := by exact prefixLift 2108025
  have htrace : WordTrace (prefixWord ++ tailWord_2108025) baseStart_2108025 baseEnd_2108025 := by
    simpa [prefixWord, tailWord_2108025, baseEnd_2108025] using wordTrace_append hprefix tailTrace_2108025
  have hstable : (prefixWord ++ tailWord_2108025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108025).length < 2 ^ (prefixWord ++ tailWord_2108025).sum := by decide
  have hdescent : baseEnd_2108025 < baseStart_2108025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108083 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 7]
def baseStart_2108083 : Nat := 118140960795 + 2108083 * 2 ^ 59
def prefixEnd_2108083 : Nat := 4983230072969 + 3 ^ 40 * 2108083 * 2
def baseEnd_2108083 : Nat := 240546630793817966503913

theorem tailTrace_2108083 : CollatzResearch.WordTrace tailWord_2108083 prefixEnd_2108083 240546630793817966503913 := by
  unfold tailWord_2108083
  simp only [CollatzResearch.WordTrace]
  refine ⟨76888103621782797757904903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51258735747855198505269935 76888103621782797757904903)
  ·
    refine ⟨115332155432674196636857355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76888103621782797757904903 115332155432674196636857355)
    ·
      refine ⟨172998233149011294955286033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115332155432674196636857355 172998233149011294955286033)
      ·
        refine ⟨129748674861758471216464525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172998233149011294955286033 129748674861758471216464525)
        ·
          refine ⟨48655753073159426706174197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129748674861758471216464525 48655753073159426706174197)
          ·
            refine ⟨4561476850608696253703831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48655753073159426706174197 4561476850608696253703831)
            ·
              refine ⟨6842215275913044380555747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561476850608696253703831 6842215275913044380555747)
              ·
                refine ⟨10263322913869566570833621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842215275913044380555747 10263322913869566570833621)
                ·
                  refine ⟨240546630793817966503913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10263322913869566570833621 240546630793817966503913)
                  ·
                    rfl

theorem cell22_2108083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_2108083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108083 prefixEnd_2108083 := by exact prefixLift 2108083
  have htrace : WordTrace (prefixWord ++ tailWord_2108083) baseStart_2108083 baseEnd_2108083 := by
    simpa [prefixWord, tailWord_2108083, baseEnd_2108083] using wordTrace_append hprefix tailTrace_2108083
  have hstable : (prefixWord ++ tailWord_2108083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108083).length < 2 ^ (prefixWord ++ tailWord_2108083).sum := by decide
  have hdescent : baseEnd_2108083 < baseStart_2108083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108087 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 3, 3]
def baseStart_2108087 : Nat := 118140960795 + 2108087 * 2 ^ 59
def prefixEnd_2108087 : Nat := 4983230072969 + 3 ^ 40 * 2108087 * 2
def baseEnd_2108087 : Nat := 721641261663199222411727

theorem tailTrace_2108087 : CollatzResearch.WordTrace tailWord_2108087 prefixEnd_2108087 721641261663199222411727 := by
  unfold tailWord_2108087
  simp only [CollatzResearch.WordTrace]
  refine ⟨76888249513768306441050515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51258833009178870960700343 76888249513768306441050515)
  ·
    refine ⟨115332374270652459661575773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76888249513768306441050515 115332374270652459661575773)
    ·
      refine ⟨43249640351494672373090915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115332374270652459661575773 43249640351494672373090915)
      ·
        refine ⟨64874460527242008559636373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43249640351494672373090915 64874460527242008559636373)
        ·
          refine ⟨3040990337214469151232955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64874460527242008559636373 3040990337214469151232955)
          ·
            refine ⟨4561485505821703726849433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040990337214469151232955 4561485505821703726849433)
            ·
              refine ⟨3421114129366277795137075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561485505821703726849433 3421114129366277795137075)
              ·
                refine ⟨5131671194049416692705613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421114129366277795137075 5131671194049416692705613)
                ·
                  refine ⟨1924376697768531259764605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5131671194049416692705613 1924376697768531259764605)
                  ·
                    refine ⟨721641261663199222411727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924376697768531259764605 721641261663199222411727)
                    ·
                      rfl

theorem cell22_2108087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_2108087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108087 prefixEnd_2108087 := by exact prefixLift 2108087
  have htrace : WordTrace (prefixWord ++ tailWord_2108087) baseStart_2108087 baseEnd_2108087 := by
    simpa [prefixWord, tailWord_2108087, baseEnd_2108087] using wordTrace_append hprefix tailTrace_2108087
  have hstable : (prefixWord ++ tailWord_2108087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108087).length < 2 ^ (prefixWord ++ tailWord_2108087).sum := by decide
  have hdescent : baseEnd_2108087 < baseStart_2108087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108175 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 2, 4]
def baseStart_2108175 : Nat := 118140960795 + 2108175 * 2 ^ 59
def prefixEnd_2108175 : Nat := 4983230072969 + 3 ^ 40 * 2108175 * 2
def baseEnd_2108175 : Nat := 721671385861596326211457

theorem tailTrace_2108175 : CollatzResearch.WordTrace tailWord_2108175 prefixEnd_2108175 721671385861596326211457 := by
  unfold tailWord_2108175
  simp only [CollatzResearch.WordTrace]
  refine ⟨76891459137449497470253979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51260972758299664980169319 76891459137449497470253979)
  ·
    refine ⟨115337188706174246205380969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76891459137449497470253979 115337188706174246205380969)
    ·
      refine ⟨86502891529630684654035727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115337188706174246205380969 86502891529630684654035727)
      ·
        refine ⟨129754337294446026981053591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86502891529630684654035727 129754337294446026981053591)
        ·
          refine ⟨194631505941669040471580387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129754337294446026981053591 194631505941669040471580387)
          ·
            refine ⟨291947258912503560707370581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194631505941669040471580387 291947258912503560707370581)
            ·
              refine ⟨3421256940380901102039499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 291947258912503560707370581 3421256940380901102039499)
              ·
                refine ⟨5131885410571351653059249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421256940380901102039499 5131885410571351653059249)
                ·
                  refine ⟨3848914057928513739794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5131885410571351653059249 3848914057928513739794437)
                  ·
                    refine ⟨721671385861596326211457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3848914057928513739794437 721671385861596326211457)
                    ·
                      rfl

theorem cell22_2108175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_2108175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108175 prefixEnd_2108175 := by exact prefixLift 2108175
  have htrace : WordTrace (prefixWord ++ tailWord_2108175) baseStart_2108175 baseEnd_2108175 := by
    simpa [prefixWord, tailWord_2108175, baseEnd_2108175] using wordTrace_append hprefix tailTrace_2108175
  have hstable : (prefixWord ++ tailWord_2108175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108175).length < 2 ^ (prefixWord ++ tailWord_2108175).sum := by decide
  have hdescent : baseEnd_2108175 < baseStart_2108175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108190 : List Nat := [4, 3, 2, 13]
def baseStart_2108190 : Nat := 118140960795 + 2108190 * 2 ^ 59
def prefixEnd_2108190 : Nat := 4983230072969 + 3 ^ 40 * 2108190 * 2
def baseEnd_2108190 : Nat := 989954074990591614659

theorem tailTrace_2108190 : CollatzResearch.WordTrace tailWord_2108190 prefixEnd_2108190 989954074990591614659 := by
  unfold tailWord_2108190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9611500779049394379006253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51261337488263436688033349 9611500779049394379006253)
  ·
    refine ⟨3604312792143522892127345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9611500779049394379006253 3604312792143522892127345)
    ·
      refine ⟨2703234594107642169095509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3604312792143522892127345 2703234594107642169095509)
      ·
        refine ⟨989954074990591614659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2703234594107642169095509 989954074990591614659)
        ·
          rfl

theorem cell22_2108190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 13].length) (baseStart_2108190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108190 prefixEnd_2108190 := by exact prefixLift 2108190
  have htrace : WordTrace (prefixWord ++ tailWord_2108190) baseStart_2108190 baseEnd_2108190 := by
    simpa [prefixWord, tailWord_2108190, baseEnd_2108190] using wordTrace_append hprefix tailTrace_2108190
  have hstable : (prefixWord ++ tailWord_2108190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108190).length < 2 ^ (prefixWord ++ tailWord_2108190).sum := by decide
  have hdescent : baseEnd_2108190 < baseStart_2108190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108194 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2108194 : Nat := 118140960795 + 2108194 * 2 ^ 59
def prefixEnd_2108194 : Nat := 4983230072969 + 3 ^ 40 * 2108194 * 2
def baseEnd_2108194 : Nat := 721677889949886609986399

theorem tailTrace_2108194 : CollatzResearch.WordTrace tailWord_2108194 prefixEnd_2108194 721677889949886609986399 := by
  unfold tailWord_2108194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223038031095165928798909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51261434749587109143463757 19223038031095165928798909)
  ·
    refine ⟨7208639261660687223299591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19223038031095165928798909 7208639261660687223299591)
    ·
      refine ⟨10812958892491030834949387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7208639261660687223299591 10812958892491030834949387)
      ·
        refine ⟨16219438338736546252424081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10812958892491030834949387 16219438338736546252424081)
        ·
          refine ⟨12164578754052409689318061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16219438338736546252424081 12164578754052409689318061)
          ·
            refine ⟨4561717032769653633494273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12164578754052409689318061 4561717032769653633494273)
            ·
              refine ⟨3421287774577240225120705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4561717032769653633494273 3421287774577240225120705)
              ·
                refine ⟨2565965830932930168840529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421287774577240225120705 2565965830932930168840529)
                ·
                  refine ⟨1924474373199697626630397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565965830932930168840529 1924474373199697626630397)
                  ·
                    refine ⟨721677889949886609986399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924474373199697626630397 721677889949886609986399)
                    ·
                      rfl

theorem cell22_2108194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2108194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108194 prefixEnd_2108194 := by exact prefixLift 2108194
  have htrace : WordTrace (prefixWord ++ tailWord_2108194) baseStart_2108194 baseEnd_2108194 := by
    simpa [prefixWord, tailWord_2108194, baseEnd_2108194] using wordTrace_append hprefix tailTrace_2108194
  have hstable : (prefixWord ++ tailWord_2108194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108194).length < 2 ^ (prefixWord ++ tailWord_2108194).sum := by decide
  have hdescent : baseEnd_2108194 < baseStart_2108194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108196 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_2108196 : Nat := 118140960795 + 2108196 * 2 ^ 59
def prefixEnd_2108196 : Nat := 4983230072969 + 3 ^ 40 * 2108196 * 2
def baseEnd_2108196 : Nat := 240559524863586423812131

theorem tailTrace_2108196 : CollatzResearch.WordTrace tailWord_2108196 prefixEnd_2108196 240559524863586423812131 := by
  unfold tailWord_2108196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38446112535186709028384221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51261483380248945371178961 38446112535186709028384221)
  ·
    refine ⟨14417292200695015885644083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38446112535186709028384221 14417292200695015885644083)
    ·
      refine ⟨21625938301042523828466125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14417292200695015885644083 21625938301042523828466125)
      ·
        refine ⟨8109726862890946435674797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21625938301042523828466125 8109726862890946435674797)
        ·
          refine ⟨3041147573584104913378049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8109726862890946435674797 3041147573584104913378049)
          ·
            refine ⟨2280860680188078685033537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041147573584104913378049 2280860680188078685033537)
            ·
              refine ⟨1710645510141059013775153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280860680188078685033537 1710645510141059013775153)
              ·
                refine ⟨1282984132605794260331365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710645510141059013775153 1282984132605794260331365)
                ·
                  refine ⟨240559524863586423812131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1282984132605794260331365 240559524863586423812131)
                  ·
                    rfl

theorem cell22_2108196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_2108196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108196 prefixEnd_2108196 := by exact prefixLift 2108196
  have htrace : WordTrace (prefixWord ++ tailWord_2108196) baseStart_2108196 baseEnd_2108196 := by
    simpa [prefixWord, tailWord_2108196, baseEnd_2108196] using wordTrace_append hprefix tailTrace_2108196
  have hstable : (prefixWord ++ tailWord_2108196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108196).length < 2 ^ (prefixWord ++ tailWord_2108196).sum := by decide
  have hdescent : baseEnd_2108196 < baseStart_2108196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108203 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_2108203 : Nat := 118140960795 + 2108203 * 2 ^ 59
def prefixEnd_2108203 : Nat := 4983230072969 + 3 ^ 40 * 2108203 * 2
def baseEnd_2108203 : Nat := 721680970833813586511371

theorem tailTrace_2108203 : CollatzResearch.WordTrace tailWord_2108203 prefixEnd_2108203 721680970833813586511371 := by
  unfold tailWord_2108203
  simp only [CollatzResearch.WordTrace]
  refine ⟨76892480381348058252273263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51261653587565372168182175 76892480381348058252273263)
  ·
    refine ⟨115338720572022087378409895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76892480381348058252273263 115338720572022087378409895)
    ·
      refine ⟨173008080858033131067614843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115338720572022087378409895 173008080858033131067614843)
      ·
        refine ⟨259512121287049696601422265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173008080858033131067614843 259512121287049696601422265)
        ·
          refine ⟨194634090965287272451066699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259512121287049696601422265 194634090965287272451066699)
          ·
            refine ⟨291951136447930908676600049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194634090965287272451066699 291951136447930908676600049)
            ·
              refine ⟨218963352335948181507450037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291951136447930908676600049 218963352335948181507450037)
              ·
                refine ⟨20527814281495142016323441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218963352335948181507450037 20527814281495142016323441)
                ·
                  refine ⟨15395860711121356512242581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20527814281495142016323441 15395860711121356512242581)
                  ·
                    refine ⟨721680970833813586511371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15395860711121356512242581 721680970833813586511371)
                    ·
                      rfl

theorem cell22_2108203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_2108203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108203 prefixEnd_2108203 := by exact prefixLift 2108203
  have htrace : WordTrace (prefixWord ++ tailWord_2108203) baseStart_2108203 baseEnd_2108203 := by
    simpa [prefixWord, tailWord_2108203, baseEnd_2108203] using wordTrace_append hprefix tailTrace_2108203
  have hstable : (prefixWord ++ tailWord_2108203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108203).length < 2 ^ (prefixWord ++ tailWord_2108203).sum := by decide
  have hdescent : baseEnd_2108203 < baseStart_2108203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108250 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_2108250 : Nat := 118140960795 + 2108250 * 2 ^ 59
def prefixEnd_2108250 : Nat := 4983230072969 + 3 ^ 40 * 2108250 * 2
def baseEnd_2108250 : Nat := 721697059894321130586227

theorem tailTrace_2108250 : CollatzResearch.WordTrace tailWord_2108250 prefixEnd_2108250 721697059894321130586227 := by
  unfold tailWord_2108250
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223548653044446319808551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51262796408118523519489469 19223548653044446319808551)
  ·
    refine ⟨28835322979566669479712827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19223548653044446319808551 28835322979566669479712827)
    ·
      refine ⟨43252984469350004219569241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28835322979566669479712827 43252984469350004219569241)
      ·
        refine ⟨32439738352012503164676931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43252984469350004219569241 32439738352012503164676931)
        ·
          refine ⟨48659607528018754747015397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32439738352012503164676931 48659607528018754747015397)
          ·
            refine ⟨9123676411503516515065387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48659607528018754747015397 9123676411503516515065387)
            ·
              refine ⟨13685514617255274772598081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9123676411503516515065387 13685514617255274772598081)
              ·
                refine ⟨10264135962941456079448561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13685514617255274772598081 10264135962941456079448561)
                ·
                  refine ⟨7698101972206092059586421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10264135962941456079448561 7698101972206092059586421)
                  ·
                    refine ⟨721697059894321130586227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7698101972206092059586421 721697059894321130586227)
                    ·
                      rfl

theorem cell22_2108250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_2108250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108250 prefixEnd_2108250 := by exact prefixLift 2108250
  have htrace : WordTrace (prefixWord ++ tailWord_2108250) baseStart_2108250 baseEnd_2108250 := by
    simpa [prefixWord, tailWord_2108250, baseEnd_2108250] using wordTrace_append hprefix tailTrace_2108250
  have hstable : (prefixWord ++ tailWord_2108250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108250).length < 2 ^ (prefixWord ++ tailWord_2108250).sum := by decide
  have hdescent : baseEnd_2108250 < baseStart_2108250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108252 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_2108252 : Nat := 118140960795 + 2108252 * 2 ^ 59
def prefixEnd_2108252 : Nat := 4983230072969 + 3 ^ 40 * 2108252 * 2
def baseEnd_2108252 : Nat := 240565914845064597345407

theorem tailTrace_2108252 : CollatzResearch.WordTrace tailWord_2108252 prefixEnd_2108252 240565914845064597345407 := by
  unfold tailWord_2108252
  simp only [CollatzResearch.WordTrace]
  refine ⟨38447133779085269810403505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51262845038780359747204673 38447133779085269810403505)
  ·
    refine ⟨28835350334313952357802629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38447133779085269810403505 28835350334313952357802629)
    ·
      refine ⟨5406628187683866067087993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28835350334313952357802629 5406628187683866067087993)
      ·
        refine ⟨4054971140762899550315995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5406628187683866067087993 4054971140762899550315995)
        ·
          refine ⟨6082456711144349325473993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054971140762899550315995 6082456711144349325473993)
          ·
            refine ⟨4561842533358261994105495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6082456711144349325473993 4561842533358261994105495)
            ·
              refine ⟨6842763800037392991158243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561842533358261994105495 6842763800037392991158243)
              ·
                refine ⟨10264145700056089486737365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842763800037392991158243 10264145700056089486737365)
                ·
                  refine ⟨240565914845064597345407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10264145700056089486737365 240565914845064597345407)
                  ·
                    rfl

theorem cell22_2108252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_2108252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108252 prefixEnd_2108252 := by exact prefixLift 2108252
  have htrace : WordTrace (prefixWord ++ tailWord_2108252) baseStart_2108252 baseEnd_2108252 := by
    simpa [prefixWord, tailWord_2108252, baseEnd_2108252] using wordTrace_append hprefix tailTrace_2108252
  have hstable : (prefixWord ++ tailWord_2108252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108252).length < 2 ^ (prefixWord ++ tailWord_2108252).sum := by decide
  have hdescent : baseEnd_2108252 < baseStart_2108252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108314 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_2108314 : Nat := 118140960795 + 2108314 * 2 ^ 59
def prefixEnd_2108314 : Nat := 4983230072969 + 3 ^ 40 * 2108314 * 2
def baseEnd_2108314 : Nat := 240572989467415432328677

theorem tailTrace_2108314 : CollatzResearch.WordTrace tailWord_2108314 prefixEnd_2108314 240572989467415432328677 := by
  unfold tailWord_2108314
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224132220986481052390999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51264352589297282806375997 19224132220986481052390999)
  ·
    refine ⟨28836198331479721578586499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224132220986481052390999 28836198331479721578586499)
    ·
      refine ⟨43254297497219582367879749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28836198331479721578586499 43254297497219582367879749)
      ·
        refine ⟨8110180780728671693977453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43254297497219582367879749 8110180780728671693977453)
        ·
          refine ⟨3041317792773251885241545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8110180780728671693977453 3041317792773251885241545)
          ·
            refine ⟨2280988344579938913931159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041317792773251885241545 2280988344579938913931159)
            ·
              refine ⟨3421482516869908370896739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280988344579938913931159 3421482516869908370896739)
              ·
                refine ⟨5132223775304862556345109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3421482516869908370896739 5132223775304862556345109)
                ·
                  refine ⟨240572989467415432328677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5132223775304862556345109 240572989467415432328677)
                  ·
                    rfl

theorem cell22_2108314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_2108314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108314 prefixEnd_2108314 := by exact prefixLift 2108314
  have htrace : WordTrace (prefixWord ++ tailWord_2108314) baseStart_2108314 baseEnd_2108314 := by
    simpa [prefixWord, tailWord_2108314, baseEnd_2108314] using wordTrace_append hprefix tailTrace_2108314
  have hstable : (prefixWord ++ tailWord_2108314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108314).length < 2 ^ (prefixWord ++ tailWord_2108314).sum := by decide
  have hdescent : baseEnd_2108314 < baseStart_2108314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108333 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2108333 : Nat := 118140960795 + 2108333 * 2 ^ 59
def prefixEnd_2108333 : Nat := 4983230072969 + 3 ^ 40 * 2108333 * 2
def baseEnd_2108333 : Nat := 721725472490536580760973

theorem tailTrace_2108333 : CollatzResearch.WordTrace tailWord_2108333 prefixEnd_2108333 721725472490536580760973 := by
  unfold tailWord_2108333
  simp only [CollatzResearch.WordTrace]
  refine ⟨76897221870877090454505653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51264814580584726969670435 76897221870877090454505653)
  ·
    refine ⟨7209114550394727230109905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76897221870877090454505653 7209114550394727230109905)
    ·
      refine ⟨5406835912796045422582429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7209114550394727230109905 5406835912796045422582429)
      ·
        refine ⟨2027563467298517033468411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5406835912796045422582429 2027563467298517033468411)
        ·
          refine ⟨3041345200947775550202617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027563467298517033468411 3041345200947775550202617)
          ·
            refine ⟨2281008900710831662651963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3041345200947775550202617 2281008900710831662651963)
            ·
              refine ⟨3421513351066247493977945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281008900710831662651963 3421513351066247493977945)
              ·
                refine ⟨2566135013299685620483459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421513351066247493977945 2566135013299685620483459)
                ·
                  refine ⟨3849202519949528430725189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566135013299685620483459 3849202519949528430725189)
                  ·
                    refine ⟨721725472490536580760973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849202519949528430725189 721725472490536580760973)
                    ·
                      rfl

theorem cell22_2108333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2108333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108333 prefixEnd_2108333 := by exact prefixLift 2108333
  have htrace : WordTrace (prefixWord ++ tailWord_2108333) baseStart_2108333 baseEnd_2108333 := by
    simpa [prefixWord, tailWord_2108333, baseEnd_2108333] using wordTrace_append hprefix tailTrace_2108333
  have hstable : (prefixWord ++ tailWord_2108333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108333).length < 2 ^ (prefixWord ++ tailWord_2108333).sum := by decide
  have hdescent : baseEnd_2108333 < baseStart_2108333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108365 : List Nat := [1, 6, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2108365 : Nat := 118140960795 + 2108365 * 2 ^ 59
def prefixEnd_2108365 : Nat := 4983230072969 + 3 ^ 40 * 2108365 * 2
def baseEnd_2108365 : Nat := 240578808914833054653625

theorem tailTrace_2108365 : CollatzResearch.WordTrace tailWord_2108365 prefixEnd_2108365 240578808914833054653625 := by
  unfold tailWord_2108365
  simp only [CollatzResearch.WordTrace]
  refine ⟨76898389006761159919670549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51265592671174106613113699 76898389006761159919670549)
  ·
    refine ⟨3604611984691929371234557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76898389006761159919670549 3604611984691929371234557)
    ·
      refine ⟨1351729494259473514212959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3604611984691929371234557 1351729494259473514212959)
      ·
        refine ⟨2027594241389210271319439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351729494259473514212959 2027594241389210271319439)
        ·
          refine ⟨3041391362083815406979159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027594241389210271319439 3041391362083815406979159)
          ·
            refine ⟨4562087043125723110468739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041391362083815406979159 4562087043125723110468739)
            ·
              refine ⟨6843130564688584665703109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562087043125723110468739 6843130564688584665703109)
              ·
                refine ⟨1283086980879109624819333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6843130564688584665703109 1283086980879109624819333)
                ·
                  refine ⟨240578808914833054653625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283086980879109624819333 240578808914833054653625)
                  ·
                    rfl

theorem cell22_2108365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2108365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108365 prefixEnd_2108365 := by exact prefixLift 2108365
  have htrace : WordTrace (prefixWord ++ tailWord_2108365) baseStart_2108365 baseEnd_2108365 := by
    simpa [prefixWord, tailWord_2108365, baseEnd_2108365] using wordTrace_append hprefix tailTrace_2108365
  have hstable : (prefixWord ++ tailWord_2108365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108365).length < 2 ^ (prefixWord ++ tailWord_2108365).sum := by decide
  have hdescent : baseEnd_2108365 < baseStart_2108365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108372 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2108372 : Nat := 118140960795 + 2108372 * 2 ^ 59
def prefixEnd_2108372 : Nat := 4983230072969 + 3 ^ 40 * 2108372 * 2
def baseEnd_2108372 : Nat := 721738822987553479035853

theorem tailTrace_2108372 : CollatzResearch.WordTrace tailWord_2108372 prefixEnd_2108372 721738822987553479035853 := by
  unfold tailWord_2108372
  simp only [CollatzResearch.WordTrace]
  refine ⟨38449322158867900057587685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51265762878490533410116913 38449322158867900057587685)
  ·
    refine ⟨7209247904787731260797691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38449322158867900057587685 7209247904787731260797691)
    ·
      refine ⟨10813871857181596891196537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7209247904787731260797691 10813871857181596891196537)
      ·
        refine ⟨8110403892886197668397403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10813871857181596891196537 8110403892886197668397403)
        ·
          refine ⟨12165605839329296502596105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8110403892886197668397403 12165605839329296502596105)
          ·
            refine ⟨9124204379496972376947079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12165605839329296502596105 9124204379496972376947079)
            ·
              refine ⟨13686306569245458565420619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9124204379496972376947079 13686306569245458565420619)
              ·
                refine ⟨20529459853868187848130929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13686306569245458565420619 20529459853868187848130929)
                ·
                  refine ⟨15397094890401140886098197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20529459853868187848130929 15397094890401140886098197)
                  ·
                    refine ⟨721738822987553479035853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15397094890401140886098197 721738822987553479035853)
                    ·
                      rfl

theorem cell22_2108372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2108372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108372 prefixEnd_2108372 := by exact prefixLift 2108372
  have htrace : WordTrace (prefixWord ++ tailWord_2108372) baseStart_2108372 baseEnd_2108372 := by
    simpa [prefixWord, tailWord_2108372, baseEnd_2108372] using wordTrace_append hprefix tailTrace_2108372
  have hstable : (prefixWord ++ tailWord_2108372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108372).length < 2 ^ (prefixWord ++ tailWord_2108372).sum := by decide
  have hdescent : baseEnd_2108372 < baseStart_2108372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108387 : List Nat := [1, 1, 1, 6, 1, 1, 1, 5, 5]
def baseStart_2108387 : Nat := 118140960795 + 2108387 * 2 ^ 59
def prefixEnd_2108387 : Nat := 4983230072969 + 3 ^ 40 * 2108387 * 2
def baseEnd_2108387 : Nat := 240581319264699479970269

theorem tailTrace_2108387 : CollatzResearch.WordTrace tailWord_2108387 prefixEnd_2108387 240581319264699479970269 := by
  unfold tailWord_2108387
  simp only [CollatzResearch.WordTrace]
  refine ⟨76899191412681457676971415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51266127608454305117980943 76899191412681457676971415)
  ·
    refine ⟨115348787119022186515457123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76899191412681457676971415 115348787119022186515457123)
    ·
      refine ⟨173023180678533279773185685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115348787119022186515457123 173023180678533279773185685)
      ·
        refine ⟨8110461594306247489368079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 173023180678533279773185685 8110461594306247489368079)
        ·
          refine ⟨12165692391459371234052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8110461594306247489368079 12165692391459371234052119)
          ·
            refine ⟨18248538587189056851078179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12165692391459371234052119 18248538587189056851078179)
            ·
              refine ⟨27372807880783585276617269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18248538587189056851078179 27372807880783585276617269)
              ·
                refine ⟨2566200738823461119682869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27372807880783585276617269 2566200738823461119682869)
                ·
                  refine ⟨240581319264699479970269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2566200738823461119682869 240581319264699479970269)
                  ·
                    rfl

theorem cell22_2108387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 5].length) (baseStart_2108387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108387 prefixEnd_2108387 := by exact prefixLift 2108387
  have htrace : WordTrace (prefixWord ++ tailWord_2108387) baseStart_2108387 baseEnd_2108387 := by
    simpa [prefixWord, tailWord_2108387, baseEnd_2108387] using wordTrace_append hprefix tailTrace_2108387
  have hstable : (prefixWord ++ tailWord_2108387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108387).length < 2 ^ (prefixWord ++ tailWord_2108387).sum := by decide
  have hdescent : baseEnd_2108387 < baseStart_2108387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108477 : List Nat := [1, 4, 1, 3, 1, 2, 10]
def baseStart_2108477 : Nat := 118140960795 + 2108477 * 2 ^ 59
def prefixEnd_2108477 : Nat := 4983230072969 + 3 ^ 40 * 2108477 * 2
def baseEnd_2108477 : Nat := 26732398764198822413353

theorem tailTrace_2108477 : CollatzResearch.WordTrace tailWord_2108477 prefixEnd_2108477 26732398764198822413353 := by
  unfold tailWord_2108477
  simp only [CollatzResearch.WordTrace]
  refine ⟨76902473982355403047747685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51268315988236935365165123 76902473982355403047747685)
  ·
    refine ⟨14419213871691638071452691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76902473982355403047747685 14419213871691638071452691)
    ·
      refine ⟨21628820807537457107179037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14419213871691638071452691 21628820807537457107179037)
      ·
        refine ⟨8110807802826546415192139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21628820807537457107179037 8110807802826546415192139)
        ·
          refine ⟨12166211704239819622788209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8110807802826546415192139 12166211704239819622788209)
          ·
            refine ⟨9124658778179864717091157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12166211704239819622788209 9124658778179864717091157)
            ·
              refine ⟨26732398764198822413353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9124658778179864717091157 26732398764198822413353)
              ·
                rfl

theorem cell22_2108477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 10].length) (baseStart_2108477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108477 prefixEnd_2108477 := by exact prefixLift 2108477
  have htrace : WordTrace (prefixWord ++ tailWord_2108477) baseStart_2108477 baseEnd_2108477 := by
    simpa [prefixWord, tailWord_2108477, baseEnd_2108477] using wordTrace_append hprefix tailTrace_2108477
  have hstable : (prefixWord ++ tailWord_2108477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108477).length < 2 ^ (prefixWord ++ tailWord_2108477).sum := by decide
  have hdescent : baseEnd_2108477 < baseStart_2108477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108498 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_2108498 : Nat := 118140960795 + 2108498 * 2 ^ 59
def prefixEnd_2108498 : Nat := 4983230072969 + 3 ^ 40 * 2108498 * 2
def baseEnd_2108498 : Nat := 721781955362531150385467

theorem tailTrace_2108498 : CollatzResearch.WordTrace tailWord_2108498 prefixEnd_2108498 721781955362531150385467 := by
  unfold tailWord_2108498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19225809978819830908565537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51268826610186215756174765 19225809978819830908565537)
  ·
    refine ⟨14419357484114873181424153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19225809978819830908565537 14419357484114873181424153)
    ·
      refine ⟨10814518113086154886068115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14419357484114873181424153 10814518113086154886068115)
      ·
        refine ⟨16221777169629232329102173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10814518113086154886068115 16221777169629232329102173)
        ·
          refine ⟨6083166438610962123413315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16221777169629232329102173 6083166438610962123413315)
          ·
            refine ⟨9124749657916443185119973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083166438610962123413315 9124749657916443185119973)
            ·
              refine ⟨1710890560859333097209995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9124749657916443185119973 1710890560859333097209995)
              ·
                refine ⟨2566335841288999645814993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710890560859333097209995 2566335841288999645814993)
                ·
                  refine ⟨1924751880966749734361245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566335841288999645814993 1924751880966749734361245)
                  ·
                    refine ⟨721781955362531150385467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924751880966749734361245 721781955362531150385467)
                    ·
                      rfl

theorem cell22_2108498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_2108498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108498 prefixEnd_2108498 := by exact prefixLift 2108498
  have htrace : WordTrace (prefixWord ++ tailWord_2108498) baseStart_2108498 baseEnd_2108498 := by
    simpa [prefixWord, tailWord_2108498, baseEnd_2108498] using wordTrace_append hprefix tailTrace_2108498
  have hstable : (prefixWord ++ tailWord_2108498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108498).length < 2 ^ (prefixWord ++ tailWord_2108498).sum := by decide
  have hdescent : baseEnd_2108498 < baseStart_2108498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108502 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2108502 : Nat := 118140960795 + 2108502 * 2 ^ 59
def prefixEnd_2108502 : Nat := 4983230072969 + 3 ^ 40 * 2108502 * 2
def baseEnd_2108502 : Nat := 721783324644276473285455

theorem tailTrace_2108502 : CollatzResearch.WordTrace tailWord_2108502 prefixEnd_2108502 721783324644276473285455 := by
  unfold tailWord_2108502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4806461612954052019837985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51268923871509888211605173 4806461612954052019837985)
  ·
    refine ⟨3604846209715539014878489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4806461612954052019837985 3604846209715539014878489)
    ·
      refine ⟨2703634657286654261158867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3604846209715539014878489 2703634657286654261158867)
      ·
        refine ⟨4055451985929981391738301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2703634657286654261158867 4055451985929981391738301)
        ·
          refine ⟨1520794494723743021901863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4055451985929981391738301 1520794494723743021901863)
          ·
            refine ⟨2281191742085614532852795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520794494723743021901863 2281191742085614532852795)
            ·
              refine ⟨3421787613128421799279193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281191742085614532852795 3421787613128421799279193)
              ·
                refine ⟨2566340709846316349459395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3421787613128421799279193 2566340709846316349459395)
                ·
                  refine ⟨3849511064769474524189093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566340709846316349459395 3849511064769474524189093)
                  ·
                    refine ⟨721783324644276473285455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849511064769474524189093 721783324644276473285455)
                    ·
                      rfl

theorem cell22_2108502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2108502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108502 prefixEnd_2108502 := by exact prefixLift 2108502
  have htrace : WordTrace (prefixWord ++ tailWord_2108502) baseStart_2108502 baseEnd_2108502 := by
    simpa [prefixWord, tailWord_2108502, baseEnd_2108502] using wordTrace_append hprefix tailTrace_2108502
  have hstable : (prefixWord ++ tailWord_2108502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108502).length < 2 ^ (prefixWord ++ tailWord_2108502).sum := by decide
  have hdescent : baseEnd_2108502 < baseStart_2108502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108554 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2108554 : Nat := 118140960795 + 2108554 * 2 ^ 59
def prefixEnd_2108554 : Nat := 4983230072969 + 3 ^ 40 * 2108554 * 2
def baseEnd_2108554 : Nat := 721801125306965670985295

theorem tailTrace_2108554 : CollatzResearch.WordTrace tailWord_2108554 prefixEnd_2108554 721801125306965670985295 := by
  unfold tailWord_2108554
  simp only [CollatzResearch.WordTrace]
  refine ⟨19226320600769111299575179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51270188268717630132200477 19226320600769111299575179)
  ·
    refine ⟨28839480901153666949362769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19226320600769111299575179 28839480901153666949362769)
    ·
      refine ⟨21629610675865250212022077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28839480901153666949362769 21629610675865250212022077)
      ·
        refine ⟨8111104003449468829508279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21629610675865250212022077 8111104003449468829508279)
        ·
          refine ⟨12166656005174203244262419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8111104003449468829508279 12166656005174203244262419)
          ·
            refine ⟨18249984007761304866393629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12166656005174203244262419 18249984007761304866393629)
            ·
              refine ⟨6843744002910489324897611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18249984007761304866393629 6843744002910489324897611)
              ·
                refine ⟨10265616004365733987346417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6843744002910489324897611 10265616004365733987346417)
                ·
                  refine ⟨7699212003274300490509813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10265616004365733987346417 7699212003274300490509813)
                  ·
                    refine ⟨721801125306965670985295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7699212003274300490509813 721801125306965670985295)
                    ·
                      rfl

theorem cell22_2108554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2108554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108554 prefixEnd_2108554 := by exact prefixLift 2108554
  have htrace : WordTrace (prefixWord ++ tailWord_2108554) baseStart_2108554 baseEnd_2108554 := by
    simpa [prefixWord, tailWord_2108554, baseEnd_2108554] using wordTrace_append hprefix tailTrace_2108554
  have hstable : (prefixWord ++ tailWord_2108554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108554).length < 2 ^ (prefixWord ++ tailWord_2108554).sum := by decide
  have hdescent : baseEnd_2108554 < baseStart_2108554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108601 : List Nat := [1, 2, 1, 4, 1, 3, 2, 4, 4]
def baseStart_2108601 : Nat := 118140960795 + 2108601 * 2 ^ 59
def prefixEnd_2108601 : Nat := 4983230072969 + 3 ^ 40 * 2108601 * 2
def baseEnd_2108601 : Nat := 240605738122491071686717

theorem tailTrace_2108601 : CollatzResearch.WordTrace tailWord_2108601 prefixEnd_2108601 240605738122491071686717 := by
  unfold tailWord_2108601
  simp only [CollatzResearch.WordTrace]
  refine ⟨76906996633906172225261657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51271331089270781483507771 76906996633906172225261657)
  ·
    refine ⟨57680247475429629168946243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76906996633906172225261657 57680247475429629168946243)
    ·
      refine ⟨86520371213144443753419365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57680247475429629168946243 86520371213144443753419365)
      ·
        refine ⟨16222569602464583203766131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86520371213144443753419365 16222569602464583203766131)
        ·
          refine ⟨24333854403696874805649197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16222569602464583203766131 24333854403696874805649197)
          ·
            refine ⟨9125195401386328052118449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24333854403696874805649197 9125195401386328052118449)
            ·
              refine ⟨6843896551039746039088837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9125195401386328052118449 6843896551039746039088837)
              ·
                refine ⟨1283230603319952382329157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6843896551039746039088837 1283230603319952382329157)
                ·
                  refine ⟨240605738122491071686717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283230603319952382329157 240605738122491071686717)
                  ·
                    rfl

theorem cell22_2108601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_2108601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108601 prefixEnd_2108601 := by exact prefixLift 2108601
  have htrace : WordTrace (prefixWord ++ tailWord_2108601) baseStart_2108601 baseEnd_2108601 := by
    simpa [prefixWord, tailWord_2108601, baseEnd_2108601] using wordTrace_append hprefix tailTrace_2108601
  have hstable : (prefixWord ++ tailWord_2108601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108601).length < 2 ^ (prefixWord ++ tailWord_2108601).sum := by decide
  have hdescent : baseEnd_2108601 < baseStart_2108601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108616 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2108616 : Nat := 118140960795 + 2108616 * 2 ^ 59
def prefixEnd_2108616 : Nat := 4983230072969 + 3 ^ 40 * 2108616 * 2
def baseEnd_2108616 : Nat := 721822349174018175935105

theorem tailTrace_2108616 : CollatzResearch.WordTrace tailWord_2108616 prefixEnd_2108616 721822349174018175935105 := by
  unfold tailWord_2108616
  simp only [CollatzResearch.WordTrace]
  refine ⟨38453771864425914893528851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51271695819234553191371801 38453771864425914893528851)
  ·
    refine ⟨57680657796638872340293277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38453771864425914893528851 57680657796638872340293277)
    ·
      refine ⟨21630246673739577127609979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57680657796638872340293277 21630246673739577127609979)
      ·
        refine ⟨32445370010609365691414969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21630246673739577127609979 32445370010609365691414969)
        ·
          refine ⟨24334027507957024268561227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32445370010609365691414969 24334027507957024268561227)
          ·
            refine ⟨36501041261935536402841841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24334027507957024268561227 36501041261935536402841841)
            ·
              refine ⟨27375780946451652302131381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36501041261935536402841841 27375780946451652302131381)
              ·
                refine ⟨2566479463729842403324817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27375780946451652302131381 2566479463729842403324817)
                ·
                  refine ⟨1924859597797381802493613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2566479463729842403324817 1924859597797381802493613)
                  ·
                    refine ⟨721822349174018175935105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924859597797381802493613 721822349174018175935105)
                    ·
                      rfl

theorem cell22_2108616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2108616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108616 prefixEnd_2108616 := by exact prefixLift 2108616
  have htrace : WordTrace (prefixWord ++ tailWord_2108616) baseStart_2108616 baseEnd_2108616 := by
    simpa [prefixWord, tailWord_2108616, baseEnd_2108616] using wordTrace_append hprefix tailTrace_2108616
  have hstable : (prefixWord ++ tailWord_2108616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108616).length < 2 ^ (prefixWord ++ tailWord_2108616).sum := by decide
  have hdescent : baseEnd_2108616 < baseStart_2108616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108712 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2108712 : Nat := 118140960795 + 2108712 * 2 ^ 59
def prefixEnd_2108712 : Nat := 4983230072969 + 3 ^ 40 * 2108712 * 2
def baseEnd_2108712 : Nat := 721855211935905925534811

theorem tailTrace_2108712 : CollatzResearch.WordTrace tailWord_2108712 prefixEnd_2108712 721855211935905925534811 := by
  unfold tailWord_2108712
  simp only [CollatzResearch.WordTrace]
  refine ⟨38455522568252019091276195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51274030091002692121701593 38455522568252019091276195)
  ·
    refine ⟨57683283852378028636914293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38455522568252019091276195 57683283852378028636914293)
    ·
      refine ⟨5407807861160440184710715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57683283852378028636914293 5407807861160440184710715)
      ·
        refine ⟨8111711791740660277066073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5407807861160440184710715 8111711791740660277066073)
        ·
          refine ⟨6083783843805495207799555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8111711791740660277066073 6083783843805495207799555)
          ·
            refine ⟨9125675765708242811699333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083783843805495207799555 9125675765708242811699333)
            ·
              refine ⟨1711064206070295527193625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9125675765708242811699333 1711064206070295527193625)
              ·
                refine ⟨1283298154552721645395219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1711064206070295527193625 1283298154552721645395219)
                ·
                  refine ⟨1924947231829082468092829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283298154552721645395219 1924947231829082468092829)
                  ·
                    refine ⟨721855211935905925534811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924947231829082468092829 721855211935905925534811)
                    ·
                      rfl

theorem cell22_2108712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2108712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108712 prefixEnd_2108712 := by exact prefixLift 2108712
  have htrace : WordTrace (prefixWord ++ tailWord_2108712) baseStart_2108712 baseEnd_2108712 := by
    simpa [prefixWord, tailWord_2108712, baseEnd_2108712] using wordTrace_append hprefix tailTrace_2108712
  have hstable : (prefixWord ++ tailWord_2108712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108712).length < 2 ^ (prefixWord ++ tailWord_2108712).sum := by decide
  have hdescent : baseEnd_2108712 < baseStart_2108712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108719 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 6]
def baseStart_2108719 : Nat := 118140960795 + 2108719 * 2 ^ 59
def prefixEnd_2108719 : Nat := 4983230072969 + 3 ^ 40 * 2108719 * 2
def baseEnd_2108719 : Nat := 240619202726320080203263

theorem tailTrace_2108719 : CollatzResearch.WordTrace tailWord_2108719 prefixEnd_2108719 240619202726320080203263 := by
  unfold tailWord_2108719
  simp only [CollatzResearch.WordTrace]
  refine ⟨76911300447478678378057211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51274200298319118918704807 76911300447478678378057211)
  ·
    refine ⟨115366950671218017567085817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76911300447478678378057211 115366950671218017567085817)
    ·
      refine ⟨86525213003413513175314363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115366950671218017567085817 86525213003413513175314363)
      ·
        refine ⟨129787819505120269762971545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86525213003413513175314363 129787819505120269762971545)
        ·
          refine ⟨97340864628840202322228659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129787819505120269762971545 97340864628840202322228659)
          ·
            refine ⟨146011296943260303483342989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97340864628840202322228659 146011296943260303483342989)
            ·
              refine ⟨54754236353722613806253621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146011296943260303483342989 54754236353722613806253621)
              ·
                refine ⟨5133209658161495044336277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54754236353722613806253621 5133209658161495044336277)
                ·
                  refine ⟨240619202726320080203263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5133209658161495044336277 240619202726320080203263)
                  ·
                    rfl

theorem cell22_2108719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_2108719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108719 prefixEnd_2108719 := by exact prefixLift 2108719
  have htrace : WordTrace (prefixWord ++ tailWord_2108719) baseStart_2108719 baseEnd_2108719 := by
    simpa [prefixWord, tailWord_2108719, baseEnd_2108719] using wordTrace_append hprefix tailTrace_2108719
  have hstable : (prefixWord ++ tailWord_2108719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108719).length < 2 ^ (prefixWord ++ tailWord_2108719).sum := by decide
  have hdescent : baseEnd_2108719 < baseStart_2108719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108721 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_2108721 : Nat := 118140960795 + 2108721 * 2 ^ 59
def prefixEnd_2108721 : Nat := 4983230072969 + 3 ^ 40 * 2108721 * 2
def baseEnd_2108721 : Nat := 721858292819832902059783

theorem tailTrace_2108721 : CollatzResearch.WordTrace tailWord_2108721 prefixEnd_2108721 721858292819832902059783 := by
  unfold tailWord_2108721
  simp only [CollatzResearch.WordTrace]
  refine ⟨76911373393471432719630017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51274248928980955146420011 76911373393471432719630017)
  ·
    refine ⟨57683530045103574539722513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76911373393471432719630017 57683530045103574539722513)
    ·
      refine ⟨43262647533827680904791885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57683530045103574539722513 43262647533827680904791885)
      ·
        refine ⟨16223492825185380339296957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43262647533827680904791885 16223492825185380339296957)
        ·
          refine ⟨6083809809444517627236359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16223492825185380339296957 6083809809444517627236359)
          ·
            refine ⟨9125714714166776440854539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6083809809444517627236359 9125714714166776440854539)
            ·
              refine ⟨13688572071250164661281809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9125714714166776440854539 13688572071250164661281809)
              ·
                refine ⟨10266429053437623495961357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13688572071250164661281809 10266429053437623495961357)
                ·
                  refine ⟨3849910895039108810985509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10266429053437623495961357 3849910895039108810985509)
                  ·
                    refine ⟨721858292819832902059783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3849910895039108810985509 721858292819832902059783)
                    ·
                      rfl

theorem cell22_2108721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_2108721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108721 prefixEnd_2108721 := by exact prefixLift 2108721
  have htrace : WordTrace (prefixWord ++ tailWord_2108721) baseStart_2108721 baseEnd_2108721 := by
    simpa [prefixWord, tailWord_2108721, baseEnd_2108721] using wordTrace_append hprefix tailTrace_2108721
  have hstable : (prefixWord ++ tailWord_2108721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108721).length < 2 ^ (prefixWord ++ tailWord_2108721).sum := by decide
  have hdescent : baseEnd_2108721 < baseStart_2108721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108753 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 4]
def baseStart_2108753 : Nat := 118140960795 + 2108753 * 2 ^ 59
def prefixEnd_2108753 : Nat := 4983230072969 + 3 ^ 40 * 2108753 * 2
def baseEnd_2108753 : Nat := 240623082357931828419895

theorem tailTrace_2108753 : CollatzResearch.WordTrace tailWord_2108753 prefixEnd_2108753 240623082357931828419895 := by
  unfold tailWord_2108753
  simp only [CollatzResearch.WordTrace]
  refine ⟨76912540529355502184794913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51275027019570334789863275 76912540529355502184794913)
  ·
    refine ⟨57684405397016626638596185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76912540529355502184794913 57684405397016626638596185)
    ·
      refine ⟨43263304047762469978947139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57684405397016626638596185 43263304047762469978947139)
      ·
        refine ⟨64894956071643704968420709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43263304047762469978947139 64894956071643704968420709)
        ·
          refine ⟨12167804263433194681578883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64894956071643704968420709 12167804263433194681578883)
          ·
            refine ⟨18251706395149792022368325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12167804263433194681578883 18251706395149792022368325)
            ·
              refine ⟨3422194949090586004194061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18251706395149792022368325 3422194949090586004194061)
              ·
                refine ⟨1283323105908969751572773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3422194949090586004194061 1283323105908969751572773)
                ·
                  refine ⟨240623082357931828419895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283323105908969751572773 240623082357931828419895)
                  ·
                    rfl

theorem cell22_2108753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_2108753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108753 prefixEnd_2108753 := by exact prefixLift 2108753
  have htrace : WordTrace (prefixWord ++ tailWord_2108753) baseStart_2108753 baseEnd_2108753 := by
    simpa [prefixWord, tailWord_2108753, baseEnd_2108753] using wordTrace_append hprefix tailTrace_2108753
  have hstable : (prefixWord ++ tailWord_2108753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108753).length < 2 ^ (prefixWord ++ tailWord_2108753).sum := by decide
  have hdescent : baseEnd_2108753 < baseStart_2108753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108768 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_2108768 : Nat := 118140960795 + 2108768 * 2 ^ 59
def prefixEnd_2108768 : Nat := 4983230072969 + 3 ^ 40 * 2108768 * 2
def baseEnd_2108768 : Nat := 721874381880340446134639

theorem tailTrace_2108768 : CollatzResearch.WordTrace tailWord_2108768 prefixEnd_2108768 721874381880340446134639 := by
  unfold tailWord_2108768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38456543812150579873295479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51275391749534106497727305 38456543812150579873295479)
  ·
    refine ⟨57684815718225869809943219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38456543812150579873295479 57684815718225869809943219)
    ·
      refine ⟨86527223577338804714914829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57684815718225869809943219 86527223577338804714914829)
      ·
        refine ⟨32447708841502051768093061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86527223577338804714914829 32447708841502051768093061)
        ·
          refine ⟨6083945407781634706517449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32447708841502051768093061 6083945407781634706517449)
          ·
            refine ⟨4562959055836226029888087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6083945407781634706517449 4562959055836226029888087)
            ·
              refine ⟨6844438583754339044832131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4562959055836226029888087 6844438583754339044832131)
              ·
                refine ⟨10266657875631508567248197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6844438583754339044832131 10266657875631508567248197)
                ·
                  refine ⟨1924998351680907856359037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10266657875631508567248197 1924998351680907856359037)
                  ·
                    refine ⟨721874381880340446134639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1924998351680907856359037 721874381880340446134639)
                    ·
                      rfl

theorem cell22_2108768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_2108768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108768 prefixEnd_2108768 := by exact prefixLift 2108768
  have htrace : WordTrace (prefixWord ++ tailWord_2108768) baseStart_2108768 baseEnd_2108768 := by
    simpa [prefixWord, tailWord_2108768, baseEnd_2108768] using wordTrace_append hprefix tailTrace_2108768
  have hstable : (prefixWord ++ tailWord_2108768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108768).length < 2 ^ (prefixWord ++ tailWord_2108768).sum := by decide
  have hdescent : baseEnd_2108768 < baseStart_2108768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108779 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_2108779 : Nat := 118140960795 + 2108779 * 2 ^ 59
def prefixEnd_2108779 : Nat := 4983230072969 + 3 ^ 40 * 2108779 * 2
def baseEnd_2108779 : Nat := 721878147405140084109605

theorem tailTrace_2108779 : CollatzResearch.WordTrace tailWord_2108779 prefixEnd_2108779 721878147405140084109605 := by
  unfold tailWord_2108779
  simp only [CollatzResearch.WordTrace]
  refine ⟨76913488827261308625241391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51275659218174205750160927 76913488827261308625241391)
  ·
    refine ⟨115370233240891962937862087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76913488827261308625241391 115370233240891962937862087)
    ·
      refine ⟨173055349861337944406793131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115370233240891962937862087 173055349861337944406793131)
      ·
        refine ⟨259583024792006916610189697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173055349861337944406793131 259583024792006916610189697)
        ·
          refine ⟨194687268594005187457642273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259583024792006916610189697 194687268594005187457642273)
          ·
            refine ⟨146015451445503890593231705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194687268594005187457642273 146015451445503890593231705)
            ·
              refine ⟨109511588584127917944923779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146015451445503890593231705 109511588584127917944923779)
              ·
                refine ⟨164267382876191876917385669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109511588584127917944923779 164267382876191876917385669)
                ·
                  refine ⟨30800134289285976922009813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164267382876191876917385669 30800134289285976922009813)
                  ·
                    refine ⟨721878147405140084109605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30800134289285976922009813 721878147405140084109605)
                    ·
                      rfl

theorem cell22_2108779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_2108779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108779 prefixEnd_2108779 := by exact prefixLift 2108779
  have htrace : WordTrace (prefixWord ++ tailWord_2108779) baseStart_2108779 baseEnd_2108779 := by
    simpa [prefixWord, tailWord_2108779, baseEnd_2108779] using wordTrace_append hprefix tailTrace_2108779
  have hstable : (prefixWord ++ tailWord_2108779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108779).length < 2 ^ (prefixWord ++ tailWord_2108779).sum := by decide
  have hdescent : baseEnd_2108779 < baseStart_2108779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108826 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_2108826 : Nat := 118140960795 + 2108826 * 2 ^ 59
def prefixEnd_2108826 : Nat := 4983230072969 + 3 ^ 40 * 2108826 * 2
def baseEnd_2108826 : Nat := 240631412155215876061487

theorem tailTrace_2108826 : CollatzResearch.WordTrace tailWord_2108826 prefixEnd_2108826 240631412155215876061487 := by
  unfold tailWord_2108826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19228800764522758913050583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51276802038727357101468221 19228800764522758913050583)
  ·
    refine ⟨28843201146784138369575875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19228800764522758913050583 28843201146784138369575875)
    ·
      refine ⟨43264801720176207554363813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28843201146784138369575875 43264801720176207554363813)
      ·
        refine ⟨8112150322533038916443215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43264801720176207554363813 8112150322533038916443215)
        ·
          refine ⟨12168225483799558374664823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8112150322533038916443215 12168225483799558374664823)
          ·
            refine ⟨18252338225699337561997235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12168225483799558374664823 18252338225699337561997235)
            ·
              refine ⟨27378507338549006342995853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18252338225699337561997235 27378507338549006342995853)
              ·
                refine ⟨10266940251955877378623445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27378507338549006342995853 10266940251955877378623445)
                ·
                  refine ⟨240631412155215876061487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10266940251955877378623445 240631412155215876061487)
                  ·
                    rfl

theorem cell22_2108826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_2108826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108826 prefixEnd_2108826 := by exact prefixLift 2108826
  have htrace : WordTrace (prefixWord ++ tailWord_2108826) baseStart_2108826 baseEnd_2108826 := by
    simpa [prefixWord, tailWord_2108826, baseEnd_2108826] using wordTrace_append hprefix tailTrace_2108826
  have hstable : (prefixWord ++ tailWord_2108826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108826).length < 2 ^ (prefixWord ++ tailWord_2108826).sum := by decide
  have hdescent : baseEnd_2108826 < baseStart_2108826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108903 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2108903 : Nat := 118140960795 + 2108903 * 2 ^ 59
def prefixEnd_2108903 : Nat := 4983230072969 + 3 ^ 40 * 2108903 * 2
def baseEnd_2108903 : Nat := 721920595139245094009225

theorem tailTrace_2108903 : CollatzResearch.WordTrace tailWord_2108903 prefixEnd_2108903 721920595139245094009225 := by
  unfold tailWord_2108903
  simp only [CollatzResearch.WordTrace]
  refine ⟨76918011478812077802755363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51278674319208051868503575 76918011478812077802755363)
  ·
    refine ⟨115377017218218116704133045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76918011478812077802755363 115377017218218116704133045)
    ·
      refine ⟨10816595364207948441012473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115377017218218116704133045 10816595364207948441012473)
      ·
        refine ⟨8112446523155961330759355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10816595364207948441012473 8112446523155961330759355)
        ·
          refine ⟨12168669784733941996139033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8112446523155961330759355 12168669784733941996139033)
          ·
            refine ⟨9126502338550456497104275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12168669784733941996139033 9126502338550456497104275)
            ·
              refine ⟨13689753507825684745656413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9126502338550456497104275 13689753507825684745656413)
              ·
                refine ⟨5133657565434631779621155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13689753507825684745656413 5133657565434631779621155)
                ·
                  refine ⟨7700486348151947669431733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133657565434631779621155 7700486348151947669431733)
                  ·
                    refine ⟨721920595139245094009225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7700486348151947669431733 721920595139245094009225)
                    ·
                      rfl

theorem cell22_2108903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2108903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108903 prefixEnd_2108903 := by exact prefixLift 2108903
  have htrace : WordTrace (prefixWord ++ tailWord_2108903) baseStart_2108903 baseEnd_2108903 := by
    simpa [prefixWord, tailWord_2108903, baseEnd_2108903] using wordTrace_append hprefix tailTrace_2108903
  have hstable : (prefixWord ++ tailWord_2108903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108903).length < 2 ^ (prefixWord ++ tailWord_2108903).sum := by decide
  have hdescent : baseEnd_2108903 < baseStart_2108903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2108999 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2108999 : Nat := 118140960795 + 2108999 * 2 ^ 59
def prefixEnd_2108999 : Nat := 4983230072969 + 3 ^ 40 * 2108999 * 2
def baseEnd_2108999 : Nat := 721953457901132843608931

theorem tailTrace_2108999 : CollatzResearch.WordTrace tailWord_2108999 prefixEnd_2108999 721953457901132843608931 := by
  unfold tailWord_2108999
  simp only [CollatzResearch.WordTrace]
  refine ⟨76921512886464286198250051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51281008590976190798833367 76921512886464286198250051)
  ·
    refine ⟨115382269329696429297375077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76921512886464286198250051 115382269329696429297375077)
    ·
      refine ⟨21634175499318080493257827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115382269329696429297375077 21634175499318080493257827)
      ·
        refine ⟨32451263248977120739886741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21634175499318080493257827 32451263248977120739886741)
        ·
          refine ⟨1521152964795802534682191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32451263248977120739886741 1521152964795802534682191)
          ·
            refine ⟨2281729447193703802023287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521152964795802534682191 2281729447193703802023287)
            ·
              refine ⟨3422594170790555703034931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281729447193703802023287 3422594170790555703034931)
              ·
                refine ⟨5133891256185833554552397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422594170790555703034931 5133891256185833554552397)
                ·
                  refine ⟨1925209221069687582957149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5133891256185833554552397 1925209221069687582957149)
                  ·
                    refine ⟨721953457901132843608931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925209221069687582957149 721953457901132843608931)
                    ·
                      rfl

theorem cell22_2108999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2108999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2108999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2108999 prefixEnd_2108999 := by exact prefixLift 2108999
  have htrace : WordTrace (prefixWord ++ tailWord_2108999) baseStart_2108999 baseEnd_2108999 := by
    simpa [prefixWord, tailWord_2108999, baseEnd_2108999] using wordTrace_append hprefix tailTrace_2108999
  have hstable : (prefixWord ++ tailWord_2108999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2108999).length < 2 ^ (prefixWord ++ tailWord_2108999).sum := by decide
  have hdescent : baseEnd_2108999 < baseStart_2108999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2108999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109008 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_2109008 : Nat := 118140960795 + 2109008 * 2 ^ 59
def prefixEnd_2109008 : Nat := 4983230072969 + 3 ^ 40 * 2109008 * 2
def baseEnd_2109008 : Nat := 721956538785059820133903

theorem tailTrace_2109008 : CollatzResearch.WordTrace tailWord_2109008 prefixEnd_2109008 721956538785059820133903 := by
  unfold tailWord_2109008
  simp only [CollatzResearch.WordTrace]
  refine ⟨38460920571715840367663839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51281227428954453823551785 38460920571715840367663839)
  ·
    refine ⟨57691380857573760551495759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38460920571715840367663839 57691380857573760551495759)
    ·
      refine ⟨86537071286360640827243639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57691380857573760551495759 86537071286360640827243639)
      ·
        refine ⟨129805606929540961240865459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86537071286360640827243639 129805606929540961240865459)
        ·
          refine ⟨194708410394311441861298189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129805606929540961240865459 194708410394311441861298189)
          ·
            refine ⟨73015653897866790697986821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194708410394311441861298189 73015653897866790697986821)
            ·
              refine ⟨13690435105850023255872529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73015653897866790697986821 13690435105850023255872529)
              ·
                refine ⟨10267826329387517441904397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13690435105850023255872529 10267826329387517441904397)
                ·
                  refine ⟨3850434873520319040714149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10267826329387517441904397 3850434873520319040714149)
                  ·
                    refine ⟨721956538785059820133903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3850434873520319040714149 721956538785059820133903)
                    ·
                      rfl

theorem cell22_2109008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_2109008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109008 prefixEnd_2109008 := by exact prefixLift 2109008
  have htrace : WordTrace (prefixWord ++ tailWord_2109008) baseStart_2109008 baseEnd_2109008 := by
    simpa [prefixWord, tailWord_2109008, baseEnd_2109008] using wordTrace_append hprefix tailTrace_2109008
  have hstable : (prefixWord ++ tailWord_2109008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109008).length < 2 ^ (prefixWord ++ tailWord_2109008).sum := by decide
  have hdescent : baseEnd_2109008 < baseStart_2109008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109057 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 4]
def baseStart_2109057 : Nat := 118140960795 + 2109057 * 2 ^ 59
def prefixEnd_2109057 : Nat := 4983230072969 + 3 ^ 40 * 2109057 * 2
def baseEnd_2109057 : Nat := 240657770828813341886251

theorem tailTrace_2109057 : CollatzResearch.WordTrace tailWord_2109057 prefixEnd_2109057 240657770828813341886251 := by
  unfold tailWord_2109057
  simp only [CollatzResearch.WordTrace]
  refine ⟨76923628320254162103861425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51282418880169441402574283 76923628320254162103861425)
  ·
    refine ⟨57692721240190621577896069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76923628320254162103861425 57692721240190621577896069)
    ·
      refine ⟨10817385232535741545855513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57692721240190621577896069 10817385232535741545855513)
      ·
        refine ⟨8113038924401806159391635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10817385232535741545855513 8113038924401806159391635)
        ·
          refine ⟨12169558386602709239087453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8113038924401806159391635 12169558386602709239087453)
          ·
            refine ⟨4563584394976015964657795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12169558386602709239087453 4563584394976015964657795)
            ·
              refine ⟨6845376592464023946986693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563584394976015964657795 6845376592464023946986693)
              ·
                refine ⟨1283508111087004490060005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6845376592464023946986693 1283508111087004490060005)
                ·
                  refine ⟨240657770828813341886251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283508111087004490060005 240657770828813341886251)
                  ·
                    rfl

theorem cell22_2109057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_2109057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109057 prefixEnd_2109057 := by exact prefixLift 2109057
  have htrace : WordTrace (prefixWord ++ tailWord_2109057) baseStart_2109057 baseEnd_2109057 := by
    simpa [prefixWord, tailWord_2109057, baseEnd_2109057] using wordTrace_append hprefix tailTrace_2109057
  have hstable : (prefixWord ++ tailWord_2109057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109057).length < 2 ^ (prefixWord ++ tailWord_2109057).sum := by decide
  have hdescent : baseEnd_2109057 < baseStart_2109057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109087 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 1, 6]
def baseStart_2109087 : Nat := 118140960795 + 2109087 * 2 ^ 59
def prefixEnd_2109087 : Nat := 4983230072969 + 3 ^ 40 * 2109087 * 2
def baseEnd_2109087 : Nat := 721983582099529947408661

theorem tailTrace_2109087 : CollatzResearch.WordTrace tailWord_2109087 prefixEnd_2109087 721983582099529947408661 := by
  unfold tailWord_2109087
  simp only [CollatzResearch.WordTrace]
  refine ⟨76924722510145477227453515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51283148340096984818302343 76924722510145477227453515)
  ·
    refine ⟨115387083765218215841180273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76924722510145477227453515 115387083765218215841180273)
    ·
      refine ⟨86540312823913661880885205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115387083765218215841180273 86540312823913661880885205)
      ·
        refine ⟨2028288581810476450333247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 86540312823913661880885205 2028288581810476450333247)
        ·
          refine ⟨3042432872715714675499871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028288581810476450333247 3042432872715714675499871)
          ·
            refine ⟨4563649309073572013249807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042432872715714675499871 4563649309073572013249807)
            ·
              refine ⟨6845473963610358019874711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563649309073572013249807 6845473963610358019874711)
              ·
                refine ⟨10268210945415537029812067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6845473963610358019874711 10268210945415537029812067)
                ·
                  refine ⟨15402316418123305544718101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10268210945415537029812067 15402316418123305544718101)
                  ·
                    refine ⟨721983582099529947408661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15402316418123305544718101 721983582099529947408661)
                    ·
                      rfl

theorem cell22_2109087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_2109087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109087 prefixEnd_2109087 := by exact prefixLift 2109087
  have htrace : WordTrace (prefixWord ++ tailWord_2109087) baseStart_2109087 baseEnd_2109087 := by
    simpa [prefixWord, tailWord_2109087, baseEnd_2109087] using wordTrace_append hprefix tailTrace_2109087
  have hstable : (prefixWord ++ tailWord_2109087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109087).length < 2 ^ (prefixWord ++ tailWord_2109087).sum := by decide
  have hdescent : baseEnd_2109087 < baseStart_2109087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109102 : List Nat := [4, 1, 4, 1, 2, 1, 9]
def baseStart_2109102 : Nat := 118140960795 + 2109102 * 2 ^ 59
def prefixEnd_2109102 : Nat := 4983230072969 + 3 ^ 40 * 2109102 * 2
def baseEnd_2109102 : Nat := 26740322848373144751245

theorem tailTrace_2109102 : CollatzResearch.WordTrace tailWord_2109102 prefixEnd_2109102 26740322848373144751245 := by
  unfold tailWord_2109102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9615658700636391848656195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51283513070060756526166373 9615658700636391848656195)
  ·
    refine ⟨14423488050954587772984293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9615658700636391848656195 14423488050954587772984293)
    ·
      refine ⟨2704404009553985207434555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14423488050954587772984293 2704404009553985207434555)
      ·
        refine ⟨4056606014330977811151833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704404009553985207434555 4056606014330977811151833)
        ·
          refine ⟨3042454510748233358363875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4056606014330977811151833 3042454510748233358363875)
          ·
            refine ⟨4563681766122350037545813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3042454510748233358363875 4563681766122350037545813)
            ·
              refine ⟨26740322848373144751245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4563681766122350037545813 26740322848373144751245)
              ·
                rfl

theorem cell22_2109102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 9].length) (baseStart_2109102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109102 prefixEnd_2109102 := by exact prefixLift 2109102
  have htrace : WordTrace (prefixWord ++ tailWord_2109102) baseStart_2109102 baseEnd_2109102 := by
    simpa [prefixWord, tailWord_2109102, baseEnd_2109102] using wordTrace_append hprefix tailTrace_2109102
  have hstable : (prefixWord ++ tailWord_2109102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109102).length < 2 ^ (prefixWord ++ tailWord_2109102).sum := by decide
  have hdescent : baseEnd_2109102 < baseStart_2109102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109117 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_2109117 : Nat := 118140960795 + 2109117 * 2 ^ 59
def prefixEnd_2109117 : Nat := 4983230072969 + 3 ^ 40 * 2109117 * 2
def baseEnd_2109117 : Nat := 721993851712619869158569

theorem tailTrace_2109117 : CollatzResearch.WordTrace tailWord_2109117 prefixEnd_2109117 721993851712619869158569 := by
  unfold tailWord_2109117
  simp only [CollatzResearch.WordTrace]
  refine ⟨76925816700036792351045605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51283877800024528234030403 76925816700036792351045605)
  ·
    refine ⟨14423590631256898565821051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76925816700036792351045605 14423590631256898565821051)
    ·
      refine ⟨21635385946885347848731577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14423590631256898565821051 21635385946885347848731577)
      ·
        refine ⟨16226539460164010886548683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21635385946885347848731577 16226539460164010886548683)
        ·
          refine ⟨24339809190246016329823025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16226539460164010886548683 24339809190246016329823025)
          ·
            refine ⟨18254856892684512247367269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24339809190246016329823025 18254856892684512247367269)
            ·
              refine ⟨3422785667378346046381363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18254856892684512247367269 3422785667378346046381363)
              ·
                refine ⟨5134178501067519069572045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422785667378346046381363 5134178501067519069572045)
                ·
                  refine ⟨1925316937900319651089517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5134178501067519069572045 1925316937900319651089517)
                  ·
                    refine ⟨721993851712619869158569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925316937900319651089517 721993851712619869158569)
                    ·
                      rfl

theorem cell22_2109117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_2109117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109117 prefixEnd_2109117 := by exact prefixLift 2109117
  have htrace : WordTrace (prefixWord ++ tailWord_2109117) baseStart_2109117 baseEnd_2109117 := by
    simpa [prefixWord, tailWord_2109117, baseEnd_2109117] using wordTrace_append hprefix tailTrace_2109117
  have hstable : (prefixWord ++ tailWord_2109117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109117).length < 2 ^ (prefixWord ++ tailWord_2109117).sum := by decide
  have hdescent : baseEnd_2109117 < baseStart_2109117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109175 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 6]
def baseStart_2109175 : Nat := 118140960795 + 2109175 * 2 ^ 59
def prefixEnd_2109175 : Nat := 4983230072969 + 3 ^ 40 * 2109175 * 2
def baseEnd_2109175 : Nat := 240671235432642350402797

theorem tailTrace_2109175 : CollatzResearch.WordTrace tailWord_2109175 prefixEnd_2109175 240671235432642350402797 := by
  unfold tailWord_2109175
  simp only [CollatzResearch.WordTrace]
  refine ⟨76927932133826668256656979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51285288089217778837771319 76927932133826668256656979)
  ·
    refine ⟨115391898200740002384985469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76927932133826668256656979 115391898200740002384985469)
    ·
      refine ⟨43271961825277500894369551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115391898200740002384985469 43271961825277500894369551)
      ·
        refine ⟨64907942737916251341554327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43271961825277500894369551 64907942737916251341554327)
        ·
          refine ⟨97361914106874377012331491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64907942737916251341554327 97361914106874377012331491)
          ·
            refine ⟨146042871160311565518497237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97361914106874377012331491 146042871160311565518497237)
            ·
              refine ⟨3422879792819802316839779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 146042871160311565518497237 3422879792819802316839779)
              ·
                refine ⟨5134319689229703475259669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3422879792819802316839779 5134319689229703475259669)
                ·
                  refine ⟨240671235432642350402797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5134319689229703475259669 240671235432642350402797)
                  ·
                    rfl

theorem cell22_2109175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 6].length) (baseStart_2109175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109175 prefixEnd_2109175 := by exact prefixLift 2109175
  have htrace : WordTrace (prefixWord ++ tailWord_2109175) baseStart_2109175 baseEnd_2109175 := by
    simpa [prefixWord, tailWord_2109175, baseEnd_2109175] using wordTrace_append hprefix tailTrace_2109175
  have hstable : (prefixWord ++ tailWord_2109175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109175).length < 2 ^ (prefixWord ++ tailWord_2109175).sum := by decide
  have hdescent : baseEnd_2109175 < baseStart_2109175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109194 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_2109194 : Nat := 118140960795 + 2109194 * 2 ^ 59
def prefixEnd_2109194 : Nat := 4983230072969 + 3 ^ 40 * 2109194 * 2
def baseEnd_2109194 : Nat := 722020210386217334983333

theorem tailTrace_2109194 : CollatzResearch.WordTrace tailWord_2109194 prefixEnd_2109194 722020210386217334983333 := by
  unfold tailWord_2109194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19232156280189458625399659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51285750080505223001065757 19232156280189458625399659)
  ·
    refine ⟨28848234420284187938099489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19232156280189458625399659 28848234420284187938099489)
    ·
      refine ⟨21636175815213140953574617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28848234420284187938099489 21636175815213140953574617)
      ·
        refine ⟨16227131861409855715180963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21636175815213140953574617 16227131861409855715180963)
        ·
          refine ⟨24340697792114783572771445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16227131861409855715180963 24340697792114783572771445)
          ·
            refine ⟨2281940418010760959947323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24340697792114783572771445 2281940418010760959947323)
            ·
              refine ⟨3422910627016141439920985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281940418010760959947323 3422910627016141439920985)
              ·
                refine ⟨2567182970262106079940739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3422910627016141439920985 2567182970262106079940739)
                ·
                  refine ⟨3850774455393159119911109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2567182970262106079940739 3850774455393159119911109)
                  ·
                    refine ⟨722020210386217334983333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3850774455393159119911109 722020210386217334983333)
                    ·
                      rfl

theorem cell22_2109194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_2109194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109194 prefixEnd_2109194 := by exact prefixLift 2109194
  have htrace : WordTrace (prefixWord ++ tailWord_2109194) baseStart_2109194 baseEnd_2109194 := by
    simpa [prefixWord, tailWord_2109194, baseEnd_2109194] using wordTrace_append hprefix tailTrace_2109194
  have hstable : (prefixWord ++ tailWord_2109194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109194).length < 2 ^ (prefixWord ++ tailWord_2109194).sum := by decide
  have hdescent : baseEnd_2109194 < baseStart_2109194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109207 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2109207 : Nat := 118140960795 + 2109207 * 2 ^ 59
def prefixEnd_2109207 : Nat := 4983230072969 + 3 ^ 40 * 2109207 * 2
def baseEnd_2109207 : Nat := 722024660551889634408293

theorem tailTrace_2109207 : CollatzResearch.WordTrace tailWord_2109207 prefixEnd_2109207 722024660551889634408293 := by
  unfold tailWord_2109207
  simp only [CollatzResearch.WordTrace]
  refine ⟨76929099269710737721821875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51286066179807158481214583 76929099269710737721821875)
  ·
    refine ⟨115393648904566106582732813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76929099269710737721821875 115393648904566106582732813)
    ·
      refine ⟨43272618339212289968524805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115393648904566106582732813 43272618339212289968524805)
      ·
        refine ⟨8113615938602304369098401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43272618339212289968524805 8113615938602304369098401)
        ·
          refine ⟨6085211953951728276823801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8113615938602304369098401 6085211953951728276823801)
          ·
            refine ⟨4563908965463796207617851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6085211953951728276823801 4563908965463796207617851)
            ·
              refine ⟨6845863448195694311426777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4563908965463796207617851 6845863448195694311426777)
              ·
                refine ⟨5134397586146770733570083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6845863448195694311426777 5134397586146770733570083)
                ·
                  refine ⟨7701596379220156100355125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5134397586146770733570083 7701596379220156100355125)
                  ·
                    refine ⟨722024660551889634408293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7701596379220156100355125 722024660551889634408293)
                    ·
                      rfl

theorem cell22_2109207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2109207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109207 prefixEnd_2109207 := by exact prefixLift 2109207
  have htrace : WordTrace (prefixWord ++ tailWord_2109207) baseStart_2109207 baseEnd_2109207 := by
    simpa [prefixWord, tailWord_2109207, baseEnd_2109207] using wordTrace_append hprefix tailTrace_2109207
  have hstable : (prefixWord ++ tailWord_2109207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109207).length < 2 ^ (prefixWord ++ tailWord_2109207).sum := by decide
  have hdescent : baseEnd_2109207 < baseStart_2109207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109220 : List Nat := [2, 3, 1, 3, 2, 11]
def baseStart_2109220 : Nat := 118140960795 + 2109220 * 2 ^ 59
def prefixEnd_2109220 : Nat := 4983230072969 + 3 ^ 40 * 2109220 * 2
def baseEnd_2109220 : Nat := 8913939638488418936213

theorem tailTrace_2109220 : CollatzResearch.WordTrace tailWord_2109220 prefixEnd_2109220 8913939638488418936213 := by
  unfold tailWord_2109220
  simp only [CollatzResearch.WordTrace]
  refine ⟨38464786709331820471022557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51286382279109093961363409 38464786709331820471022557)
  ·
    refine ⟨14424295015999432676633459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38464786709331820471022557 14424295015999432676633459)
    ·
      refine ⟨21636442523999149014950189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14424295015999432676633459 21636442523999149014950189)
      ·
        refine ⟨8113665946499680880606321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21636442523999149014950189 8113665946499680880606321)
        ·
          refine ⟨6085249459874760660454741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8113665946499680880606321 6085249459874760660454741)
          ·
            refine ⟨8913939638488418936213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6085249459874760660454741 8913939638488418936213)
            ·
              rfl

theorem cell22_2109220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 11].length) (baseStart_2109220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109220 prefixEnd_2109220 := by exact prefixLift 2109220
  have htrace : WordTrace (prefixWord ++ tailWord_2109220) baseStart_2109220 baseEnd_2109220 := by
    simpa [prefixWord, tailWord_2109220, baseEnd_2109220] using wordTrace_append hprefix tailTrace_2109220
  have hstable : (prefixWord ++ tailWord_2109220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109220).length < 2 ^ (prefixWord ++ tailWord_2109220).sum := by decide
  have hdescent : baseEnd_2109220 < baseStart_2109220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109224 : List Nat := [2, 1, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_2109224 : Nat := 118140960795 + 2109224 * 2 ^ 59
def prefixEnd_2109224 : Nat := 4983230072969 + 3 ^ 40 * 2109224 * 2
def baseEnd_2109224 : Nat := 722030479999307256733241

theorem tailTrace_2109224 : CollatzResearch.WordTrace tailWord_2109224 prefixEnd_2109224 722030479999307256733241 := by
  unfold tailWord_2109224
  simp only [CollatzResearch.WordTrace]
  refine ⟨38464859655324574812595363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51286479540432766416793817 38464859655324574812595363)
  ·
    refine ⟨57697289482986862218893045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38464859655324574812595363 57697289482986862218893045)
    ·
      refine ⟨5409120889030018333021223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57697289482986862218893045 5409120889030018333021223)
      ·
        refine ⟨8113681333545027499531835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5409120889030018333021223 8113681333545027499531835)
        ·
          refine ⟨12170522000317541249297753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8113681333545027499531835 12170522000317541249297753)
          ·
            refine ⟨9127891500238155936973315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12170522000317541249297753 9127891500238155936973315)
            ·
              refine ⟨13691837250357233905459973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9127891500238155936973315 13691837250357233905459973)
              ·
                refine ⟨2567219484441981357273745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13691837250357233905459973 2567219484441981357273745)
                ·
                  refine ⟨1925414613331486017955309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567219484441981357273745 1925414613331486017955309)
                  ·
                    refine ⟨722030479999307256733241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925414613331486017955309 722030479999307256733241)
                    ·
                      rfl

theorem cell22_2109224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_2109224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109224 prefixEnd_2109224 := by exact prefixLift 2109224
  have htrace : WordTrace (prefixWord ++ tailWord_2109224) baseStart_2109224 baseEnd_2109224 := by
    simpa [prefixWord, tailWord_2109224, baseEnd_2109224] using wordTrace_append hprefix tailTrace_2109224
  have hstable : (prefixWord ++ tailWord_2109224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109224).length < 2 ^ (prefixWord ++ tailWord_2109224).sum := by decide
  have hdescent : baseEnd_2109224 < baseStart_2109224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109320 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 1, 3]
def baseStart_2109320 : Nat := 118140960795 + 2109320 * 2 ^ 59
def prefixEnd_2109320 : Nat := 4983230072969 + 3 ^ 40 * 2109320 * 2
def baseEnd_2109320 : Nat := 722063342761195006332947

theorem tailTrace_2109320 : CollatzResearch.WordTrace tailWord_2109320 prefixEnd_2109320 722063342761195006332947 := by
  unfold tailWord_2109320
  simp only [CollatzResearch.WordTrace]
  refine ⟨38466610359150679010342707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51288813812200905347123609 38466610359150679010342707)
  ·
    refine ⟨57699915538726018515514061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38466610359150679010342707 57699915538726018515514061)
    ·
      refine ⟨21637468327022256943317773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57699915538726018515514061 21637468327022256943317773)
      ·
        refine ⟨8114050622633346353744165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21637468327022256943317773 8114050622633346353744165)
        ·
          refine ⟨1521384491743752441327031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8114050622633346353744165 1521384491743752441327031)
          ·
            refine ⟨2282076737615628661990547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521384491743752441327031 2282076737615628661990547)
            ·
              refine ⟨3423115106423442992985821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282076737615628661990547 3423115106423442992985821)
              ·
                refine ⟨1283668164908791122369683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423115106423442992985821 1283668164908791122369683)
                ·
                  refine ⟨1925502247363186683554525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283668164908791122369683 1925502247363186683554525)
                  ·
                    refine ⟨722063342761195006332947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925502247363186683554525 722063342761195006332947)
                    ·
                      rfl

theorem cell22_2109320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_2109320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109320 prefixEnd_2109320 := by exact prefixLift 2109320
  have htrace : WordTrace (prefixWord ++ tailWord_2109320) baseStart_2109320 baseEnd_2109320 := by
    simpa [prefixWord, tailWord_2109320, baseEnd_2109320] using wordTrace_append hprefix tailTrace_2109320
  have hstable : (prefixWord ++ tailWord_2109320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109320).length < 2 ^ (prefixWord ++ tailWord_2109320).sum := by decide
  have hdescent : baseEnd_2109320 < baseStart_2109320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109359 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 2, 3]
def baseStart_2109359 : Nat := 118140960795 + 2109359 * 2 ^ 59
def prefixEnd_2109359 : Nat := 4983230072969 + 3 ^ 40 * 2109359 * 2
def baseEnd_2109359 : Nat := 722076693258211904607827

theorem tailTrace_2109359 : CollatzResearch.WordTrace tailWord_2109359 prefixEnd_2109359 722076693258211904607827 := by
  unfold tailWord_2109359
  simp only [CollatzResearch.WordTrace]
  refine ⟨76934643165160067681355131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51289762110106711787570087 76934643165160067681355131)
  ·
    refine ⟨115401964747740101522032697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76934643165160067681355131 115401964747740101522032697)
    ·
      refine ⟨86551473560805076141524523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115401964747740101522032697 86551473560805076141524523)
      ·
        refine ⟨129827210341207614212286785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86551473560805076141524523 129827210341207614212286785)
        ·
          refine ⟨97370407755905710659215089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129827210341207614212286785 97370407755905710659215089)
          ·
            refine ⟨73027805816929282994411317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97370407755905710659215089 73027805816929282994411317)
            ·
              refine ⟨6846356795337120280726061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73027805816929282994411317 6846356795337120280726061)
              ·
                refine ⟨2567383798251420105272273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6846356795337120280726061 2567383798251420105272273)
                ·
                  refine ⟨1925537848688565078954205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567383798251420105272273 1925537848688565078954205)
                  ·
                    refine ⟨722076693258211904607827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925537848688565078954205 722076693258211904607827)
                    ·
                      rfl

theorem cell22_2109359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_2109359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109359 prefixEnd_2109359 := by exact prefixLift 2109359
  have htrace : WordTrace (prefixWord ++ tailWord_2109359) baseStart_2109359 baseEnd_2109359 := by
    simpa [prefixWord, tailWord_2109359, baseEnd_2109359] using wordTrace_append hprefix tailTrace_2109359
  have hstable : (prefixWord ++ tailWord_2109359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109359).length < 2 ^ (prefixWord ++ tailWord_2109359).sum := by decide
  have hdescent : baseEnd_2109359 < baseStart_2109359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109374 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2109374 : Nat := 118140960795 + 2109374 * 2 ^ 59
def prefixEnd_2109374 : Nat := 4983230072969 + 3 ^ 40 * 2109374 * 2
def baseEnd_2109374 : Nat := 722081828064756865482781

theorem tailTrace_2109374 : CollatzResearch.WordTrace tailWord_2109374 prefixEnd_2109374 722081828064756865482781 := by
  unfold tailWord_2109374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9616898782513215655393897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51290126840070483495434117 9616898782513215655393897)
  ·
    refine ⟨7212674086884911741545423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9616898782513215655393897 7212674086884911741545423)
    ·
      refine ⟨10819011130327367612318135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7212674086884911741545423 10819011130327367612318135)
      ·
        refine ⟨16228516695491051418477203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10819011130327367612318135 16228516695491051418477203)
        ·
          refine ⟨24342775043236577127715805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16228516695491051418477203 24342775043236577127715805)
          ·
            refine ⟨9128540641213716422893427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24342775043236577127715805 9128540641213716422893427)
            ·
              refine ⟨13692810961820574634340141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9128540641213716422893427 13692810961820574634340141)
              ·
                refine ⟨5134804110682715487877553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13692810961820574634340141 5134804110682715487877553)
                ·
                  refine ⟨3851103083012036615908165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5134804110682715487877553 3851103083012036615908165)
                  ·
                    refine ⟨722081828064756865482781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3851103083012036615908165 722081828064756865482781)
                    ·
                      rfl

theorem cell22_2109374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2109374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109374 prefixEnd_2109374 := by exact prefixLift 2109374
  have htrace : WordTrace (prefixWord ++ tailWord_2109374) baseStart_2109374 baseEnd_2109374 := by
    simpa [prefixWord, tailWord_2109374, baseEnd_2109374] using wordTrace_append hprefix tailTrace_2109374
  have hstable : (prefixWord ++ tailWord_2109374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109374).length < 2 ^ (prefixWord ++ tailWord_2109374).sum := by decide
  have hdescent : baseEnd_2109374 < baseStart_2109374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109389 : List Nat := [1, 6, 3, 12]
def baseStart_2109389 : Nat := 118140960795 + 2109389 * 2 ^ 59
def prefixEnd_2109389 : Nat := 4983230072969 + 3 ^ 40 * 2109389 * 2
def baseEnd_2109389 : Nat := 990517095845407169215

theorem tailTrace_2109389 : CollatzResearch.WordTrace tailWord_2109389 prefixEnd_2109389 990517095845407169215 := by
  unfold tailWord_2109389
  simp only [CollatzResearch.WordTrace]
  refine ⟨76935737355051382804947221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51290491570034255203298147 76935737355051382804947221)
  ·
    refine ⟨3606362688518033568981901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76935737355051382804947221 3606362688518033568981901)
    ·
      refine ⟨1352386008194262588368213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3606362688518033568981901 1352386008194262588368213)
      ·
        refine ⟨990517095845407169215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1352386008194262588368213 990517095845407169215)
        ·
          rfl

theorem cell22_2109389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 12].length) (baseStart_2109389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109389 prefixEnd_2109389 := by exact prefixLift 2109389
  have htrace : WordTrace (prefixWord ++ tailWord_2109389) baseStart_2109389 baseEnd_2109389 := by
    simpa [prefixWord, tailWord_2109389, baseEnd_2109389] using wordTrace_append hprefix tailTrace_2109389
  have hstable : (prefixWord ++ tailWord_2109389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109389).length < 2 ^ (prefixWord ++ tailWord_2109389).sum := by decide
  have hdescent : baseEnd_2109389 < baseStart_2109389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109511 : List Nat := [1, 1, 4, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2109511 : Nat := 118140960795 + 2109511 * 2 ^ 59
def prefixEnd_2109511 : Nat := 4983230072969 + 3 ^ 40 * 2109511 * 2
def baseEnd_2109511 : Nat := 722128725964534174807361

theorem tailTrace_2109511 : CollatzResearch.WordTrace tailWord_2109511 prefixEnd_2109511 722128725964534174807361 := by
  unfold tailWord_2109511
  simp only [CollatzResearch.WordTrace]
  refine ⟨76940187060609397640888387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51293458040406265093925591 76940187060609397640888387)
  ·
    refine ⟨115410280590914096461332581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76940187060609397640888387 115410280590914096461332581)
    ·
      refine ⟨21639427610796393086499859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115410280590914096461332581 21639427610796393086499859)
      ·
        refine ⟨32459141416194589629749789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21639427610796393086499859 32459141416194589629749789)
        ·
          refine ⟨12172178031072971111156171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32459141416194589629749789 12172178031072971111156171)
          ·
            refine ⟨18258267046609456666734257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12172178031072971111156171 18258267046609456666734257)
            ·
              refine ⟨13693700284957092500050693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18258267046609456666734257 13693700284957092500050693)
              ·
                refine ⟨2567568803429454843759505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13693700284957092500050693 2567568803429454843759505)
                ·
                  refine ⟨1925676602572091132819629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567568803429454843759505 1925676602572091132819629)
                  ·
                    refine ⟨722128725964534174807361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925676602572091132819629 722128725964534174807361)
                    ·
                      rfl

theorem cell22_2109511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2109511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109511 prefixEnd_2109511 := by exact prefixLift 2109511
  have htrace : WordTrace (prefixWord ++ tailWord_2109511) baseStart_2109511 baseEnd_2109511 := by
    simpa [prefixWord, tailWord_2109511, baseEnd_2109511] using wordTrace_append hprefix tailTrace_2109511
  have hstable : (prefixWord ++ tailWord_2109511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109511).length < 2 ^ (prefixWord ++ tailWord_2109511).sum := by decide
  have hdescent : baseEnd_2109511 < baseStart_2109511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109528 : List Nat := [2, 1, 2, 2, 1, 4, 4, 1, 2, 3]
def baseStart_2109528 : Nat := 118140960795 + 2109528 * 2 ^ 59
def prefixEnd_2109528 : Nat := 4983230072969 + 3 ^ 40 * 2109528 * 2
def baseEnd_2109528 : Nat := 722134545411951797132309

theorem tailTrace_2109528 : CollatzResearch.WordTrace tailWord_2109528 prefixEnd_2109528 722134545411951797132309 := by
  unfold tailWord_2109528
  simp only [CollatzResearch.WordTrace]
  refine ⟨38470403550773904772128619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51293871401031873029504825 38470403550773904772128619)
  ·
    refine ⟨57705605326160857158192929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38470403550773904772128619 57705605326160857158192929)
    ·
      refine ⟨43279203994620642868644697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57705605326160857158192929 43279203994620642868644697)
      ·
        refine ⟨32459402995965482151483523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43279203994620642868644697 32459402995965482151483523)
        ·
          refine ⟨48689104493948223227225285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32459402995965482151483523 48689104493948223227225285)
          ·
            refine ⟨9129207092615291855104741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48689104493948223227225285 9129207092615291855104741)
            ·
              refine ⟨1711726329865367222832139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9129207092615291855104741 1711726329865367222832139)
              ·
                refine ⟨2567589494798050834248209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711726329865367222832139 2567589494798050834248209)
                ·
                  refine ⟨1925692121098538125686157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567589494798050834248209 1925692121098538125686157)
                  ·
                    refine ⟨722134545411951797132309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925692121098538125686157 722134545411951797132309)
                    ·
                      rfl

theorem cell22_2109528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_2109528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109528 prefixEnd_2109528 := by exact prefixLift 2109528
  have htrace : WordTrace (prefixWord ++ tailWord_2109528) baseStart_2109528 baseEnd_2109528 := by
    simpa [prefixWord, tailWord_2109528, baseEnd_2109528] using wordTrace_append hprefix tailTrace_2109528
  have hstable : (prefixWord ++ tailWord_2109528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109528).length < 2 ^ (prefixWord ++ tailWord_2109528).sum := by decide
  have hdescent : baseEnd_2109528 < baseStart_2109528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109584 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_2109584 : Nat := 118140960795 + 2109584 * 2 ^ 59
def prefixEnd_2109584 : Nat := 4983230072969 + 3 ^ 40 * 2109584 * 2
def baseEnd_2109584 : Nat := 722153715356386317732137

theorem tailTrace_2109584 : CollatzResearch.WordTrace tailWord_2109584 prefixEnd_2109584 722153715356386317732137 := by
  unfold tailWord_2109584
  simp only [CollatzResearch.WordTrace]
  refine ⟨38471424794672465554147903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51295233059563287405530537 38471424794672465554147903)
  ·
    refine ⟨57707137192008698331221855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38471424794672465554147903 57707137192008698331221855)
    ·
      refine ⟨86560705788013047496832783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57707137192008698331221855 86560705788013047496832783)
      ·
        refine ⟨129841058682019571245249175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86560705788013047496832783 129841058682019571245249175)
        ·
          refine ⟨194761588023029356867873763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129841058682019571245249175 194761588023029356867873763)
          ·
            refine ⟨292142382034544035301810645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194761588023029356867873763 292142382034544035301810645)
            ·
              refine ⟨6847087078934625827386187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 292142382034544035301810645 6847087078934625827386187)
              ·
                refine ⟨10270630618401938741079281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6847087078934625827386187 10270630618401938741079281)
                ·
                  refine ⟨7702972963801454055809461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10270630618401938741079281 7702972963801454055809461)
                  ·
                    refine ⟨722153715356386317732137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7702972963801454055809461 722153715356386317732137)
                    ·
                      rfl

theorem cell22_2109584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_2109584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109584 prefixEnd_2109584 := by exact prefixLift 2109584
  have htrace : WordTrace (prefixWord ++ tailWord_2109584) baseStart_2109584 baseEnd_2109584 := by
    simpa [prefixWord, tailWord_2109584, baseEnd_2109584] using wordTrace_append hprefix tailTrace_2109584
  have hstable : (prefixWord ++ tailWord_2109584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109584).length < 2 ^ (prefixWord ++ tailWord_2109584).sum := by decide
  have hdescent : baseEnd_2109584 < baseStart_2109584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109586 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_2109586 : Nat := 118140960795 + 2109586 * 2 ^ 59
def prefixEnd_2109586 : Nat := 4983230072969 + 3 ^ 40 * 2109586 * 2
def baseEnd_2109586 : Nat := 240718133332419659727377

theorem tailTrace_2109586 : CollatzResearch.WordTrace tailWord_2109586 prefixEnd_2109586 240718133332419659727377 := by
  unfold tailWord_2109586
  simp only [CollatzResearch.WordTrace]
  refine ⟨19235730633834421362467153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51295281690225123633245741 19235730633834421362467153)
  ·
    refine ⟨14426797975375816021850365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19235730633834421362467153 14426797975375816021850365)
    ·
      refine ⟨5410049240765931008193887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14426797975375816021850365 5410049240765931008193887)
      ·
        refine ⟨8115073861148896512290831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410049240765931008193887 8115073861148896512290831)
        ·
          refine ⟨12172610791723344768436247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8115073861148896512290831 12172610791723344768436247)
          ·
            refine ⟨18258916187585017152654371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12172610791723344768436247 18258916187585017152654371)
            ·
              refine ⟨27388374281377525728981557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18258916187585017152654371 27388374281377525728981557)
              ·
                refine ⟨2567660088879143037092021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27388374281377525728981557 2567660088879143037092021)
                ·
                  refine ⟨240718133332419659727377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2567660088879143037092021 240718133332419659727377)
                  ·
                    rfl

theorem cell22_2109586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_2109586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109586 prefixEnd_2109586 := by exact prefixLift 2109586
  have htrace : WordTrace (prefixWord ++ tailWord_2109586) baseStart_2109586 baseEnd_2109586 := by
    simpa [prefixWord, tailWord_2109586, baseEnd_2109586] using wordTrace_append hprefix tailTrace_2109586
  have hstable : (prefixWord ++ tailWord_2109586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109586).length < 2 ^ (prefixWord ++ tailWord_2109586).sum := by decide
  have hdescent : baseEnd_2109586 < baseStart_2109586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109607 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2109607 : Nat := 118140960795 + 2109607 * 2 ^ 59
def prefixEnd_2109607 : Nat := 4983230072969 + 3 ^ 40 * 2109607 * 2
def baseEnd_2109607 : Nat := 722161588726421924407067

theorem tailTrace_2109607 : CollatzResearch.WordTrace tailWord_2109607 prefixEnd_2109607 722161588726421924407067 := by
  unfold tailWord_2109607
  simp only [CollatzResearch.WordTrace]
  refine ⟨76943688468261606036383075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51295792312174404024255383 76943688468261606036383075)
  ·
    refine ⟨115415532702392409054574613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76943688468261606036383075 115415532702392409054574613)
    ·
      refine ⟨5410103095424644174433185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 115415532702392409054574613 5410103095424644174433185)
      ·
        refine ⟨4057577321568483130824889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410103095424644174433185 4057577321568483130824889)
        ·
          refine ⟨3043182991176362348118667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4057577321568483130824889 3043182991176362348118667)
          ·
            refine ⟨4564774486764543522178001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043182991176362348118667 4564774486764543522178001)
            ·
              refine ⟨3423580865073407641633501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4564774486764543522178001 3423580865073407641633501)
              ·
                refine ⟨1283842824402527865612563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423580865073407641633501 1283842824402527865612563)
                ·
                  refine ⟨1925764236603791798418845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283842824402527865612563 1925764236603791798418845)
                  ·
                    refine ⟨722161588726421924407067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925764236603791798418845 722161588726421924407067)
                    ·
                      rfl

theorem cell22_2109607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2109607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109607 prefixEnd_2109607 := by exact prefixLift 2109607
  have htrace : WordTrace (prefixWord ++ tailWord_2109607) baseStart_2109607 baseEnd_2109607 := by
    simpa [prefixWord, tailWord_2109607, baseEnd_2109607] using wordTrace_append hprefix tailTrace_2109607
  have hstable : (prefixWord ++ tailWord_2109607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109607).length < 2 ^ (prefixWord ++ tailWord_2109607).sum := by decide
  have hdescent : baseEnd_2109607 < baseStart_2109607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109753 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_2109753 : Nat := 118140960795 + 2109753 * 2 ^ 59
def prefixEnd_2109753 : Nat := 4983230072969 + 3 ^ 40 * 2109753 * 2
def baseEnd_2109753 : Nat := 722211567510126210256619

theorem tailTrace_2109753 : CollatzResearch.WordTrace tailWord_2109753 prefixEnd_2109753 722211567510126210256619 := by
  unfold tailWord_2109753
  simp only [CollatzResearch.WordTrace]
  refine ⟨76949013525732672971197913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51299342350488448647465275 76949013525732672971197913)
  ·
    refine ⟨57711760144299504728398435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76949013525732672971197913 57711760144299504728398435)
    ·
      refine ⟨86567640216449257092597653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57711760144299504728398435 86567640216449257092597653)
      ·
        refine ⟨4057858135146058926215515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86567640216449257092597653 4057858135146058926215515)
        ·
          refine ⟨6086787202719088389323273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4057858135146058926215515 6086787202719088389323273)
          ·
            refine ⟨4565090402039316291992455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6086787202719088389323273 4565090402039316291992455)
            ·
              refine ⟨6847635603058974437988683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565090402039316291992455 6847635603058974437988683)
              ·
                refine ⟨10271453404588461656983025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6847635603058974437988683 10271453404588461656983025)
                ·
                  refine ⟨7703590053441346242737269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10271453404588461656983025 7703590053441346242737269)
                  ·
                    refine ⟨722211567510126210256619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7703590053441346242737269 722211567510126210256619)
                    ·
                      rfl

theorem cell22_2109753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_2109753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109753 prefixEnd_2109753 := by exact prefixLift 2109753
  have htrace : WordTrace (prefixWord ++ tailWord_2109753) baseStart_2109753 baseEnd_2109753 := by
    simpa [prefixWord, tailWord_2109753, baseEnd_2109753] using wordTrace_append hprefix tailTrace_2109753
  have hstable : (prefixWord ++ tailWord_2109753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109753).length < 2 ^ (prefixWord ++ tailWord_2109753).sum := by decide
  have hdescent : baseEnd_2109753 < baseStart_2109753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109800 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_2109800 : Nat := 118140960795 + 2109800 * 2 ^ 59
def prefixEnd_2109800 : Nat := 4983230072969 + 3 ^ 40 * 2109800 * 2
def baseEnd_2109800 : Nat := 240742552190211251443825

theorem tailTrace_2109800 : CollatzResearch.WordTrace tailWord_2109800 prefixEnd_2109800 240742552190211251443825 := by
  unfold tailWord_2109800
  simp only [CollatzResearch.WordTrace]
  refine ⟨38475363878281199999079427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51300485171041599998772569 38475363878281199999079427)
  ·
    refine ⟨57713045817421799998619141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38475363878281199999079427 57713045817421799998619141)
    ·
      refine ⟨10821196090766587499741089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57713045817421799998619141 10821196090766587499741089)
      ·
        refine ⟨8115897068074940624805817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10821196090766587499741089 8115897068074940624805817)
        ·
          refine ⟨6086922801056205468604363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8115897068074940624805817 6086922801056205468604363)
          ·
            refine ⟨9130384201584308202906545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6086922801056205468604363 9130384201584308202906545)
            ·
              refine ⟨6847788151188231152179909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9130384201584308202906545 6847788151188231152179909)
              ·
                refine ⟨1283960278347793341033733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6847788151188231152179909 1283960278347793341033733)
                ·
                  refine ⟨240742552190211251443825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283960278347793341033733 240742552190211251443825)
                  ·
                    rfl

theorem cell22_2109800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_2109800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109800 prefixEnd_2109800 := by exact prefixLift 2109800
  have htrace : WordTrace (prefixWord ++ tailWord_2109800) baseStart_2109800 baseEnd_2109800 := by
    simpa [prefixWord, tailWord_2109800, baseEnd_2109800] using wordTrace_append hprefix tailTrace_2109800
  have hstable : (prefixWord ++ tailWord_2109800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109800).length < 2 ^ (prefixWord ++ tailWord_2109800).sum := by decide
  have hdescent : baseEnd_2109800 < baseStart_2109800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109813 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2109813 : Nat := 118140960795 + 2109813 * 2 ^ 59
def prefixEnd_2109813 : Nat := 4983230072969 + 3 ^ 40 * 2109813 * 2
def baseEnd_2109813 : Nat := 722232106736306053756435

theorem tailTrace_2109813 : CollatzResearch.WordTrace tailWord_2109813 prefixEnd_2109813 722232106736306053756435 := by
  unfold tailWord_2109813
  simp only [CollatzResearch.WordTrace]
  refine ⟨76951201905515303218382093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51300801270343535478921395 76951201905515303218382093)
  ·
    refine ⟨28856700714568238706893285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76951201905515303218382093 28856700714568238706893285)
    ·
      refine ⟨5410631383981544757542491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28856700714568238706893285 5410631383981544757542491)
      ·
        refine ⟨8115947075972317136313737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410631383981544757542491 8115947075972317136313737)
        ·
          refine ⟨6086960306979237852235303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8115947075972317136313737 6086960306979237852235303)
          ·
            refine ⟨9130440460468856778352955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6086960306979237852235303 9130440460468856778352955)
            ·
              refine ⟨13695660690703285167529433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9130440460468856778352955 13695660690703285167529433)
              ·
                refine ⟨10271745518027463875647075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13695660690703285167529433 10271745518027463875647075)
                ·
                  refine ⟨15407618277041195813470613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10271745518027463875647075 15407618277041195813470613)
                  ·
                    refine ⟨722232106736306053756435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15407618277041195813470613 722232106736306053756435)
                    ·
                      rfl

theorem cell22_2109813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2109813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109813 prefixEnd_2109813 := by exact prefixLift 2109813
  have htrace : WordTrace (prefixWord ++ tailWord_2109813) baseStart_2109813 baseEnd_2109813 := by
    simpa [prefixWord, tailWord_2109813, baseEnd_2109813] using wordTrace_append hprefix tailTrace_2109813
  have hstable : (prefixWord ++ tailWord_2109813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109813).length < 2 ^ (prefixWord ++ tailWord_2109813).sum := by decide
  have hdescent : baseEnd_2109813 < baseStart_2109813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109834 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_2109834 : Nat := 118140960795 + 2109834 * 2 ^ 59
def prefixEnd_2109834 : Nat := 4983230072969 + 3 ^ 40 * 2109834 * 2
def baseEnd_2109834 : Nat := 240746431821822999660457

theorem tailTrace_2109834 : CollatzResearch.WordTrace tailWord_2109834 prefixEnd_2109834 240746431821822999660457 := by
  unfold tailWord_2109834
  simp only [CollatzResearch.WordTrace]
  refine ⟨19237991959609805951224139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51301311892292815869931037 19237991959609805951224139)
  ·
    refine ⟨28856987939414708926836209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19237991959609805951224139 28856987939414708926836209)
    ·
      refine ⟨21642740954561031695127157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28856987939414708926836209 21642740954561031695127157)
      ·
        refine ⟨2029006964490096721418171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21642740954561031695127157 2029006964490096721418171)
        ·
          refine ⟨3043510446735145082127257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029006964490096721418171 3043510446735145082127257)
          ·
            refine ⟨2282632835051358811595443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3043510446735145082127257 2282632835051358811595443)
            ·
              refine ⟨3423949252577038217393165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282632835051358811595443 3423949252577038217393165)
              ·
                refine ⟨1283980969716389331522437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3423949252577038217393165 1283980969716389331522437)
                ·
                  refine ⟨240746431821822999660457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1283980969716389331522437 240746431821822999660457)
                  ·
                    rfl

theorem cell22_2109834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_2109834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109834 prefixEnd_2109834 := by exact prefixLift 2109834
  have htrace : WordTrace (prefixWord ++ tailWord_2109834) baseStart_2109834 baseEnd_2109834 := by
    simpa [prefixWord, tailWord_2109834, baseEnd_2109834] using wordTrace_append hprefix tailTrace_2109834
  have hstable : (prefixWord ++ tailWord_2109834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109834).length < 2 ^ (prefixWord ++ tailWord_2109834).sum := by decide
  have hdescent : baseEnd_2109834 < baseStart_2109834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109858 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_2109858 : Nat := 118140960795 + 2109858 * 2 ^ 59
def prefixEnd_2109858 : Nat := 4983230072969 + 3 ^ 40 * 2109858 * 2
def baseEnd_2109858 : Nat := 722247511155940936381297

theorem tailTrace_2109858 : CollatzResearch.WordTrace tailWord_2109858 prefixEnd_2109858 722247511155940936381297 := by
  unfold tailWord_2109858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19238210797588068975942557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51301895460234850602513485 19238210797588068975942557)
  ·
    refine ⟨7214329049095525865978459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19238210797588068975942557 7214329049095525865978459)
    ·
      refine ⟨10821493573643288798967689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214329049095525865978459 10821493573643288798967689)
      ·
        refine ⟨8116120180232466599225767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10821493573643288798967689 8116120180232466599225767)
        ·
          refine ⟨12174180270348699898838651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8116120180232466599225767 12174180270348699898838651)
          ·
            refine ⟨18261270405523049848257977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12174180270348699898838651 18261270405523049848257977)
            ·
              refine ⟨13695952804142287386193483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18261270405523049848257977 13695952804142287386193483)
              ·
                refine ⟨20543929206213431079290225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13695952804142287386193483 20543929206213431079290225)
                ·
                  refine ⟨15407946904660073309467669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20543929206213431079290225 15407946904660073309467669)
                  ·
                    refine ⟨722247511155940936381297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15407946904660073309467669 722247511155940936381297)
                    ·
                      rfl

theorem cell22_2109858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_2109858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109858 prefixEnd_2109858 := by exact prefixLift 2109858
  have htrace : WordTrace (prefixWord ++ tailWord_2109858) baseStart_2109858 baseEnd_2109858 := by
    simpa [prefixWord, tailWord_2109858, baseEnd_2109858] using wordTrace_append hprefix tailTrace_2109858
  have hstable : (prefixWord ++ tailWord_2109858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109858).length < 2 ^ (prefixWord ++ tailWord_2109858).sum := by decide
  have hdescent : baseEnd_2109858 < baseStart_2109858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109860 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_2109860 : Nat := 118140960795 + 2109860 * 2 ^ 59
def prefixEnd_2109860 : Nat := 4983230072969 + 3 ^ 40 * 2109860 * 2
def baseEnd_2109860 : Nat := 722248195796813597831291

theorem tailTrace_2109860 : CollatzResearch.WordTrace tailWord_2109860 prefixEnd_2109860 722248195796813597831291 := by
  unfold tailWord_2109860
  simp only [CollatzResearch.WordTrace]
  refine ⟨38476458068172515122671517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51301944090896686830228689 38476458068172515122671517)
  ·
    refine ⟨14428671775564693171001819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38476458068172515122671517 14428671775564693171001819)
    ·
      refine ⟨21643007663347039756502729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14428671775564693171001819 21643007663347039756502729)
      ·
        refine ⟨16232255747510279817377047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21643007663347039756502729 16232255747510279817377047)
        ·
          refine ⟨24348383621265419726065571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16232255747510279817377047 24348383621265419726065571)
          ·
            refine ⟨36522575431898129589098357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24348383621265419726065571 36522575431898129589098357)
            ·
              refine ⟨3423991446740449648977971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36522575431898129589098357 3423991446740449648977971)
              ·
                refine ⟨5135987170110674473466957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3423991446740449648977971 5135987170110674473466957)
                ·
                  refine ⟨1925995188791502927550109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5135987170110674473466957 1925995188791502927550109)
                  ·
                    refine ⟨722248195796813597831291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1925995188791502927550109 722248195796813597831291)
                    ·
                      rfl

theorem cell22_2109860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_2109860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109860 prefixEnd_2109860 := by exact prefixLift 2109860
  have htrace : WordTrace (prefixWord ++ tailWord_2109860) baseStart_2109860 baseEnd_2109860 := by
    simpa [prefixWord, tailWord_2109860, baseEnd_2109860] using wordTrace_append hprefix tailTrace_2109860
  have hstable : (prefixWord ++ tailWord_2109860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109860).length < 2 ^ (prefixWord ++ tailWord_2109860).sum := by decide
  have hdescent : baseEnd_2109860 < baseStart_2109860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109866 : List Nat := [3, 1, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2109866 : Nat := 118140960795 + 2109866 * 2 ^ 59
def prefixEnd_2109866 : Nat := 4983230072969 + 3 ^ 40 * 2109866 * 2
def baseEnd_2109866 : Nat := 722250249719431582181273

theorem tailTrace_2109866 : CollatzResearch.WordTrace tailWord_2109866 prefixEnd_2109866 722250249719431582181273 := by
  unfold tailWord_2109866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19238283743580823317515363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51302089982882195513374301 19238283743580823317515363)
  ·
    refine ⟨28857425615371234976273045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19238283743580823317515363 28857425615371234976273045)
    ·
      refine ⟨1352691825720526639512799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28857425615371234976273045 1352691825720526639512799)
      ·
        refine ⟨2029037738580789959269199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352691825720526639512799 2029037738580789959269199)
        ·
          refine ⟨3043556607871184938903799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029037738580789959269199 3043556607871184938903799)
          ·
            refine ⟨4565334911806777408355699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043556607871184938903799 4565334911806777408355699)
            ·
              refine ⟨6848002367710166112533549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565334911806777408355699 6848002367710166112533549)
              ·
                refine ⟨2568000887891312292200081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6848002367710166112533549 2568000887891312292200081)
                ·
                  refine ⟨1926000665918484219150061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2568000887891312292200081 1926000665918484219150061)
                  ·
                    refine ⟨722250249719431582181273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926000665918484219150061 722250249719431582181273)
                    ·
                      rfl

theorem cell22_2109866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2109866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109866 prefixEnd_2109866 := by exact prefixLift 2109866
  have htrace : WordTrace (prefixWord ++ tailWord_2109866) baseStart_2109866 baseEnd_2109866 := by
    simpa [prefixWord, tailWord_2109866, baseEnd_2109866] using wordTrace_append hprefix tailTrace_2109866
  have hstable : (prefixWord ++ tailWord_2109866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109866).length < 2 ^ (prefixWord ++ tailWord_2109866).sum := by decide
  have hdescent : baseEnd_2109866 < baseStart_2109866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109954 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2109954 : Nat := 118140960795 + 2109954 * 2 ^ 59
def prefixEnd_2109954 : Nat := 4983230072969 + 3 ^ 40 * 2109954 * 2
def baseEnd_2109954 : Nat := 722280373917828685981003

theorem tailTrace_2109954 : CollatzResearch.WordTrace tailWord_2109954 prefixEnd_2109954 722280373917828685981003 := by
  unfold tailWord_2109954
  simp only [CollatzResearch.WordTrace]
  refine ⟨19239086149501121074816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51304229732002989532843277 19239086149501121074816229)
  ·
    refine ⟨3607328653031460201528043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19239086149501121074816229 3607328653031460201528043)
    ·
      refine ⟨5410992979547190302292065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607328653031460201528043 5410992979547190302292065)
      ·
        refine ⟨4058244734660392726719049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410992979547190302292065 4058244734660392726719049)
        ·
          refine ⟨3043683550995294545039287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4058244734660392726719049 3043683550995294545039287)
          ·
            refine ⟨4565525326492941817558931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043683550995294545039287 4565525326492941817558931)
            ·
              refine ⟨6848287989739412726338397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565525326492941817558931 6848287989739412726338397)
              ·
                refine ⟨2568107996152279772376899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6848287989739412726338397 2568107996152279772376899)
                ·
                  refine ⟨3852161994228419658565349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568107996152279772376899 3852161994228419658565349)
                  ·
                    refine ⟨722280373917828685981003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852161994228419658565349 722280373917828685981003)
                    ·
                      rfl

theorem cell22_2109954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2109954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109954 prefixEnd_2109954 := by exact prefixLift 2109954
  have htrace : WordTrace (prefixWord ++ tailWord_2109954) baseStart_2109954 baseEnd_2109954 := by
    simpa [prefixWord, tailWord_2109954, baseEnd_2109954] using wordTrace_append hprefix tailTrace_2109954
  have hstable : (prefixWord ++ tailWord_2109954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109954).length < 2 ^ (prefixWord ++ tailWord_2109954).sum := by decide
  have hdescent : baseEnd_2109954 < baseStart_2109954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109963 : List Nat := [1, 1, 1, 1, 7, 2, 9]
def baseStart_2109963 : Nat := 118140960795 + 2109963 * 2 ^ 59
def prefixEnd_2109963 : Nat := 4983230072969 + 3 ^ 40 * 2109963 * 2
def baseEnd_2109963 : Nat := 26751239066731691203925

theorem tailTrace_2109963 : CollatzResearch.WordTrace tailWord_2109963 prefixEnd_2109963 26751239066731691203925 := by
  unfold tailWord_2109963
  simp only [CollatzResearch.WordTrace]
  refine ⟨76956672854971878836342543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51304448569981252557561695 76956672854971878836342543)
  ·
    refine ⟨115435009282457818254513815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76956672854971878836342543 115435009282457818254513815)
    ·
      refine ⟨173152513923686727381770723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115435009282457818254513815 173152513923686727381770723)
      ·
        refine ⟨259728770885530091072656085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173152513923686727381770723 259728770885530091072656085)
        ·
          refine ⟨6087393067629611509515377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 259728770885530091072656085 6087393067629611509515377)
          ·
            refine ⟨4565544800722208632136533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6087393067629611509515377 4565544800722208632136533)
            ·
              refine ⟨26751239066731691203925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4565544800722208632136533 26751239066731691203925)
              ·
                rfl

theorem cell22_2109963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 9].length) (baseStart_2109963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109963 prefixEnd_2109963 := by exact prefixLift 2109963
  have htrace : WordTrace (prefixWord ++ tailWord_2109963) baseStart_2109963 baseEnd_2109963 := by
    simpa [prefixWord, tailWord_2109963, baseEnd_2109963] using wordTrace_append hprefix tailTrace_2109963
  have hstable : (prefixWord ++ tailWord_2109963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109963).length < 2 ^ (prefixWord ++ tailWord_2109963).sum := by decide
  have hdescent : baseEnd_2109963 < baseStart_2109963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2109984 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 1, 5]
def baseStart_2109984 : Nat := 118140960795 + 2109984 * 2 ^ 59
def prefixEnd_2109984 : Nat := 4983230072969 + 3 ^ 40 * 2109984 * 2
def baseEnd_2109984 : Nat := 722290643530918607730911

theorem tailTrace_2109984 : CollatzResearch.WordTrace tailWord_2109984 prefixEnd_2109984 722290643530918607730911 := by
  unfold tailWord_2109984
  simp only [CollatzResearch.WordTrace]
  refine ⟨38478719393947899711428503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51304959191930532948571337 38478719393947899711428503)
  ·
    refine ⟨57718079090921849567142755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38478719393947899711428503 57718079090921849567142755)
    ·
      refine ⟨86577118636382774350714133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57718079090921849567142755 86577118636382774350714133)
      ·
        refine ⟨4058302436080442547689725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86577118636382774350714133 4058302436080442547689725)
        ·
          refine ⟨1521863413530165955383647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4058302436080442547689725 1521863413530165955383647)
          ·
            refine ⟨2282795120295248933075471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521863413530165955383647 2282795120295248933075471)
            ·
              refine ⟨3424192680442873399613207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2282795120295248933075471 3424192680442873399613207)
              ·
                refine ⟨5136289020664310099419811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424192680442873399613207 5136289020664310099419811)
                ·
                  refine ⟨7704433530996465149129717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5136289020664310099419811 7704433530996465149129717)
                  ·
                    refine ⟨722290643530918607730911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7704433530996465149129717 722290643530918607730911)
                    ·
                      rfl

theorem cell22_2109984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_2109984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2109984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2109984 prefixEnd_2109984 := by exact prefixLift 2109984
  have htrace : WordTrace (prefixWord ++ tailWord_2109984) baseStart_2109984 baseEnd_2109984 := by
    simpa [prefixWord, tailWord_2109984, baseEnd_2109984] using wordTrace_append hprefix tailTrace_2109984
  have hstable : (prefixWord ++ tailWord_2109984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2109984).length < 2 ^ (prefixWord ++ tailWord_2109984).sum := by decide
  have hdescent : baseEnd_2109984 < baseStart_2109984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2109984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110008 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_2110008 : Nat := 118140960795 + 2110008 * 2 ^ 59
def prefixEnd_2110008 : Nat := 4983230072969 + 3 ^ 40 * 2110008 * 2
def baseEnd_2110008 : Nat := 240766286407130181710279

theorem tailTrace_2110008 : CollatzResearch.WordTrace tailWord_2110008 prefixEnd_2110008 240766286407130181710279 := by
  unfold tailWord_2110008
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479157069904425760865339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51305542759872567681153785 38479157069904425760865339)
  ·
    refine ⟨57718735604856638641298009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38479157069904425760865339 57718735604856638641298009)
    ·
      refine ⟨43289051703642478980973507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57718735604856638641298009 43289051703642478980973507)
      ·
        refine ⟨64933577555463718471460261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43289051703642478980973507 64933577555463718471460261)
        ·
          refine ⟨12175045791649447213398799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64933577555463718471460261 12175045791649447213398799)
          ·
            refine ⟨18262568687474170820098199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12175045791649447213398799 18262568687474170820098199)
            ·
              refine ⟨27393853031211256230147299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18262568687474170820098199 27393853031211256230147299)
              ·
                refine ⟨41090779546816884345220949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27393853031211256230147299 41090779546816884345220949)
                ·
                  refine ⟨240766286407130181710279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41090779546816884345220949 240766286407130181710279)
                  ·
                    rfl

theorem cell22_2110008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_2110008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110008 prefixEnd_2110008 := by exact prefixLift 2110008
  have htrace : WordTrace (prefixWord ++ tailWord_2110008) baseStart_2110008 baseEnd_2110008 := by
    simpa [prefixWord, tailWord_2110008, baseEnd_2110008] using wordTrace_append hprefix tailTrace_2110008
  have hstable : (prefixWord ++ tailWord_2110008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110008).length < 2 ^ (prefixWord ++ tailWord_2110008).sum := by decide
  have hdescent : baseEnd_2110008 < baseStart_2110008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110014 : List Nat := [4, 2, 1, 4, 2, 1, 8]
def baseStart_2110014 : Nat := 118140960795 + 2110014 * 2 ^ 59
def prefixEnd_2110014 : Nat := 4983230072969 + 3 ^ 40 * 2110014 * 2
def baseEnd_2110014 : Nat := 26751885672000315906697

theorem tailTrace_2110014 : CollatzResearch.WordTrace tailWord_2110014 prefixEnd_2110014 26751885672000315906697 := by
  unfold tailWord_2110014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9619816622223389318306137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51305688651858076364299397 9619816622223389318306137)
  ·
    refine ⟨7214862466667541988729603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9619816622223389318306137 7214862466667541988729603)
    ·
      refine ⟨10822293700001312983094405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7214862466667541988729603 10822293700001312983094405)
      ·
        refine ⟨2029180068750246184330201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10822293700001312983094405 2029180068750246184330201)
        ·
          refine ⟨1521885051562684638247651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029180068750246184330201 1521885051562684638247651)
          ·
            refine ⟨2282827577344026957371477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521885051562684638247651 2282827577344026957371477)
            ·
              refine ⟨26751885672000315906697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2282827577344026957371477 26751885672000315906697)
              ·
                rfl

theorem cell22_2110014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 8].length) (baseStart_2110014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110014 prefixEnd_2110014 := by exact prefixLift 2110014
  have htrace : WordTrace (prefixWord ++ tailWord_2110014) baseStart_2110014 baseEnd_2110014 := by
    simpa [prefixWord, tailWord_2110014, baseEnd_2110014] using wordTrace_append hprefix tailTrace_2110014
  have hstable : (prefixWord ++ tailWord_2110014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110014).length < 2 ^ (prefixWord ++ tailWord_2110014).sum := by decide
  have hdescent : baseEnd_2110014 < baseStart_2110014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110029 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2110029 : Nat := 118140960795 + 2110029 * 2 ^ 59
def prefixEnd_2110029 : Nat := 4983230072969 + 3 ^ 40 * 2110029 * 2
def baseEnd_2110029 : Nat := 722306047950553490355773

theorem tailTrace_2110029 : CollatzResearch.WordTrace tailWord_2110029 prefixEnd_2110029 722306047950553490355773 := by
  unfold tailWord_2110029
  simp only [CollatzResearch.WordTrace]
  refine ⟨76959080072732772108245141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51306053381821848072163427 76959080072732772108245141)
  ·
    refine ⟨3607456878409348692573991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 76959080072732772108245141 3607456878409348692573991)
    ·
      refine ⟨5411185317614023038860987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607456878409348692573991 5411185317614023038860987)
      ·
        refine ⟨8116777976421034558291481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5411185317614023038860987 8116777976421034558291481)
        ·
          refine ⟨6087583482315775918718611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8116777976421034558291481 6087583482315775918718611)
          ·
            refine ⟨9131375223473663878077917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6087583482315775918718611 9131375223473663878077917)
            ·
              refine ⟨3424265708802623954279219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9131375223473663878077917 3424265708802623954279219)
              ·
                refine ⟨5136398563203935931418829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424265708802623954279219 5136398563203935931418829)
                ·
                  refine ⟨1926149461201475974282061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5136398563203935931418829 1926149461201475974282061)
                  ·
                    refine ⟨722306047950553490355773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926149461201475974282061 722306047950553490355773)
                    ·
                      rfl

theorem cell22_2110029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2110029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110029 prefixEnd_2110029 := by exact prefixLift 2110029
  have htrace : WordTrace (prefixWord ++ tailWord_2110029) baseStart_2110029 baseEnd_2110029 := by
    simpa [prefixWord, tailWord_2110029, baseEnd_2110029] using wordTrace_append hprefix tailTrace_2110029
  have hstable : (prefixWord ++ tailWord_2110029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110029).length < 2 ^ (prefixWord ++ tailWord_2110029).sum := by decide
  have hdescent : baseEnd_2110029 < baseStart_2110029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110087 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 4]
def baseStart_2110087 : Nat := 118140960795 + 2110087 * 2 ^ 59
def prefixEnd_2110087 : Nat := 4983230072969 + 3 ^ 40 * 2110087 * 2
def baseEnd_2110087 : Nat := 240775300845286890801865

theorem tailTrace_2110087 : CollatzResearch.WordTrace tailWord_2110087 prefixEnd_2110087 240775300845286890801865 := by
  unfold tailWord_2110087
  simp only [CollatzResearch.WordTrace]
  refine ⟨76961195506522648013856515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51307463671015098675904343 76961195506522648013856515)
  ·
    refine ⟨115441793259783972020784773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76961195506522648013856515 115441793259783972020784773)
    ·
      refine ⟨21645336236209494753897145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115441793259783972020784773 21645336236209494753897145)
      ·
        refine ⟨16234002177157121065422859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21645336236209494753897145 16234002177157121065422859)
        ·
          refine ⟨24351003265735681598134289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16234002177157121065422859 24351003265735681598134289)
          ·
            refine ⟨18263252449301761198600717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24351003265735681598134289 18263252449301761198600717)
            ·
              refine ⟨6848719668488160449475269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18263252449301761198600717 6848719668488160449475269)
              ·
                refine ⟨1284134937841530084276613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6848719668488160449475269 1284134937841530084276613)
                ·
                  refine ⟨240775300845286890801865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284134937841530084276613 240775300845286890801865)
                  ·
                    rfl

theorem cell22_2110087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 4].length) (baseStart_2110087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110087 prefixEnd_2110087 := by exact prefixLift 2110087
  have htrace : WordTrace (prefixWord ++ tailWord_2110087) baseStart_2110087 baseEnd_2110087 := by
    simpa [prefixWord, tailWord_2110087, baseEnd_2110087] using wordTrace_append hprefix tailTrace_2110087
  have hstable : (prefixWord ++ tailWord_2110087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110087).length < 2 ^ (prefixWord ++ tailWord_2110087).sum := by decide
  have hdescent : baseEnd_2110087 < baseStart_2110087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110181 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_2110181 : Nat := 118140960795 + 2110181 * 2 ^ 59
def prefixEnd_2110181 : Nat := 4983230072969 + 3 ^ 40 * 2110181 * 2
def baseEnd_2110181 : Nat := 722358080656875760555307

theorem tailTrace_2110181 : CollatzResearch.WordTrace tailWord_2110181 prefixEnd_2110181 722358080656875760555307 := by
  unfold tailWord_2110181
  simp only [CollatzResearch.WordTrace]
  refine ⟨76964623968182102067778397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51309749312121401378518931 76964623968182102067778397)
  ·
    refine ⟨28861733988068288275416899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76964623968182102067778397 28861733988068288275416899)
    ·
      refine ⟨43292600982102432413125349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28861733988068288275416899 43292600982102432413125349)
      ·
        refine ⟨8117362684144206077461003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43292600982102432413125349 8117362684144206077461003)
        ·
          refine ⟨12176044026216309116191505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117362684144206077461003 12176044026216309116191505)
          ·
            refine ⟨9132033019662231837143629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12176044026216309116191505 9132033019662231837143629)
            ·
              refine ⟨3424512382373336938928861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9132033019662231837143629 3424512382373336938928861)
              ·
                refine ⟨1284192143390001352098323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3424512382373336938928861 1284192143390001352098323)
                ·
                  refine ⟨1926288215085002028147485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284192143390001352098323 1926288215085002028147485)
                  ·
                    refine ⟨722358080656875760555307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926288215085002028147485 722358080656875760555307)
                    ·
                      rfl

theorem cell22_2110181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_2110181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110181 prefixEnd_2110181 := by exact prefixLift 2110181
  have htrace : WordTrace (prefixWord ++ tailWord_2110181) baseStart_2110181 baseEnd_2110181 := by
    simpa [prefixWord, tailWord_2110181, baseEnd_2110181] using wordTrace_append hprefix tailTrace_2110181
  have hstable : (prefixWord ++ tailWord_2110181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110181).length < 2 ^ (prefixWord ++ tailWord_2110181).sum := by decide
  have hdescent : baseEnd_2110181 < baseStart_2110181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110198 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2110198 : Nat := 118140960795 + 2110198 * 2 ^ 59
def prefixEnd_2110198 : Nat := 4983230072969 + 3 ^ 40 * 2110198 * 2
def baseEnd_2110198 : Nat := 722363900104293382880255

theorem tailTrace_2110198 : CollatzResearch.WordTrace tailWord_2110198 prefixEnd_2110198 722363900104293382880255 := by
  unfold tailWord_2110198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810327750570032123196703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51310162672747009314098165 4810327750570032123196703)
  ·
    refine ⟨7215491625855048184795055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810327750570032123196703 7215491625855048184795055)
    ·
      refine ⟨10823237438782572277192583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215491625855048184795055 10823237438782572277192583)
      ·
        refine ⟨16234856158173858415788875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10823237438782572277192583 16234856158173858415788875)
        ·
          refine ⟨24352284237260787623683313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16234856158173858415788875 24352284237260787623683313)
          ·
            refine ⟨18264213177945590717762485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24352284237260787623683313 18264213177945590717762485)
            ·
              refine ⟨1712269985432399129790233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18264213177945590717762485 1712269985432399129790233)
              ·
                refine ⟨1284202489074299347342675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712269985432399129790233 1284202489074299347342675)
                ·
                  refine ⟨1926303733611449021014013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284202489074299347342675 1926303733611449021014013)
                  ·
                    refine ⟨722363900104293382880255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926303733611449021014013 722363900104293382880255)
                    ·
                      rfl

theorem cell22_2110198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2110198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110198 prefixEnd_2110198 := by exact prefixLift 2110198
  have htrace : WordTrace (prefixWord ++ tailWord_2110198) baseStart_2110198 baseEnd_2110198 := by
    simpa [prefixWord, tailWord_2110198, baseEnd_2110198] using wordTrace_append hprefix tailTrace_2110198
  have hstable : (prefixWord ++ tailWord_2110198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110198).length < 2 ^ (prefixWord ++ tailWord_2110198).sum := by decide
  have hdescent : baseEnd_2110198 < baseStart_2110198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110252 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_2110252 : Nat := 118140960795 + 2110252 * 2 ^ 59
def prefixEnd_2110252 : Nat := 4983230072969 + 3 ^ 40 * 2110252 * 2
def baseEnd_2110252 : Nat := 722382385407855242030089

theorem tailTrace_2110252 : CollatzResearch.WordTrace tailWord_2110252 prefixEnd_2110252 722382385407855242030089 := by
  unfold tailWord_2110252
  simp only [CollatzResearch.WordTrace]
  refine ⟨38483606775462440596806505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51311475700616587462408673 38483606775462440596806505)
  ·
    refine ⟨28862705081596830447604879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38483606775462440596806505 28862705081596830447604879)
    ·
      refine ⟨43294057622395245671407319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28862705081596830447604879 43294057622395245671407319)
      ·
        refine ⟨64941086433592868507110979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43294057622395245671407319 64941086433592868507110979)
        ·
          refine ⟨97411629650389302760666469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64941086433592868507110979 97411629650389302760666469)
          ·
            refine ⟨18264680559447994267624963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97411629650389302760666469 18264680559447994267624963)
            ·
              refine ⟨27397020839171991401437445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18264680559447994267624963 27397020839171991401437445)
              ·
                refine ⟨5136941407344748387769521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27397020839171991401437445 5136941407344748387769521)
                ·
                  refine ⟨3852706055508561290827141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5136941407344748387769521 3852706055508561290827141)
                  ·
                    refine ⟨722382385407855242030089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852706055508561290827141 722382385407855242030089)
                    ·
                      rfl

theorem cell22_2110252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_2110252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110252 prefixEnd_2110252 := by exact prefixLift 2110252
  have htrace : WordTrace (prefixWord ++ tailWord_2110252) baseStart_2110252 baseEnd_2110252 := by
    simpa [prefixWord, tailWord_2110252, baseEnd_2110252] using wordTrace_append hprefix tailTrace_2110252
  have hstable : (prefixWord ++ tailWord_2110252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110252).length < 2 ^ (prefixWord ++ tailWord_2110252).sum := by decide
  have hdescent : baseEnd_2110252 < baseStart_2110252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110284 : List Nat := [2, 2, 1, 3, 3, 2, 3, 6]
def baseStart_2110284 : Nat := 118140960795 + 2110284 * 2 ^ 59
def prefixEnd_2110284 : Nat := 4983230072969 + 3 ^ 40 * 2110284 * 2
def baseEnd_2110284 : Nat := 80265926629090869469999

theorem tailTrace_2110284 : CollatzResearch.WordTrace tailWord_2110284 prefixEnd_2110284 80265926629090869469999 := by
  unfold tailWord_2110284
  simp only [CollatzResearch.WordTrace]
  refine ⟨38484190343404475329388953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51312253791205967105851937 38484190343404475329388953)
  ·
    refine ⟨28863142757553356497041715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38484190343404475329388953 28863142757553356497041715)
    ·
      refine ⟨43294714136330034745562573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28863142757553356497041715 43294714136330034745562573)
      ·
        refine ⟨16235517801123763029585965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43294714136330034745562573 16235517801123763029585965)
        ·
          refine ⟨6088319175421411136094737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16235517801123763029585965 6088319175421411136094737)
          ·
            refine ⟨4566239381566058352071053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6088319175421411136094737 4566239381566058352071053)
            ·
              refine ⟨1712339768087271882026645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4566239381566058352071053 1712339768087271882026645)
              ·
                refine ⟨80265926629090869469999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1712339768087271882026645 80265926629090869469999)
                ·
                  rfl

theorem cell22_2110284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_2110284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110284 prefixEnd_2110284 := by exact prefixLift 2110284
  have htrace : WordTrace (prefixWord ++ tailWord_2110284) baseStart_2110284 baseEnd_2110284 := by
    simpa [prefixWord, tailWord_2110284, baseEnd_2110284] using wordTrace_append hprefix tailTrace_2110284
  have hstable : (prefixWord ++ tailWord_2110284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110284).length < 2 ^ (prefixWord ++ tailWord_2110284).sum := by decide
  have hdescent : baseEnd_2110284 < baseStart_2110284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110316 : List Nat := [2, 2, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_2110316 : Nat := 118140960795 + 2110316 * 2 ^ 59
def prefixEnd_2110316 : Nat := 4983230072969 + 3 ^ 40 * 2110316 * 2
def baseEnd_2110316 : Nat := 722404293915780408429893

theorem tailTrace_2110316 : CollatzResearch.WordTrace tailWord_2110316 prefixEnd_2110316 722404293915780408429893 := by
  unfold tailWord_2110316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38484773911346510061971401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51313031881795346749295201 38484773911346510061971401)
  ·
    refine ⟨28863580433509882546478551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38484773911346510061971401 28863580433509882546478551)
    ·
      refine ⟨43295370650264823819717827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28863580433509882546478551 43295370650264823819717827)
      ·
        refine ⟨64943055975397235729576741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43295370650264823819717827 64943055975397235729576741)
        ·
          refine ⟨12176822995386981699295639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64943055975397235729576741 12176822995386981699295639)
          ·
            refine ⟨18265234493080472548943459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12176822995386981699295639 18265234493080472548943459)
            ·
              refine ⟨27397851739620708823415189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18265234493080472548943459 27397851739620708823415189)
              ·
                refine ⟨1284274300294720726097587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27397851739620708823415189 1284274300294720726097587)
                ·
                  refine ⟨1926411450442081089146381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284274300294720726097587 1926411450442081089146381)
                  ·
                    refine ⟨722404293915780408429893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926411450442081089146381 722404293915780408429893)
                    ·
                      rfl

theorem cell22_2110316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_2110316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110316 prefixEnd_2110316 := by exact prefixLift 2110316
  have htrace : WordTrace (prefixWord ++ tailWord_2110316) baseStart_2110316 baseEnd_2110316 := by
    simpa [prefixWord, tailWord_2110316, baseEnd_2110316] using wordTrace_append hprefix tailTrace_2110316
  have hstable : (prefixWord ++ tailWord_2110316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110316).length < 2 ^ (prefixWord ++ tailWord_2110316).sum := by decide
  have hdescent : baseEnd_2110316 < baseStart_2110316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110359 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 1, 4]
def baseStart_2110359 : Nat := 118140960795 + 2110359 * 2 ^ 59
def prefixEnd_2110359 : Nat := 4983230072969 + 3 ^ 40 * 2110359 * 2
def baseEnd_2110359 : Nat := 722419013694542629604761

theorem tailTrace_2110359 : CollatzResearch.WordTrace tailWord_2110359 prefixEnd_2110359 722419013694542629604761 := by
  unfold tailWord_2110359
  simp only [CollatzResearch.WordTrace]
  refine ⟨76971116161537238467758131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51314077441024825645172087 76971116161537238467758131)
  ·
    refine ⟨115456674242305857701637197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76971116161537238467758131 115456674242305857701637197)
    ·
      refine ⟨43296252840864696638113949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115456674242305857701637197 43296252840864696638113949)
      ·
        refine ⟨16236094815324261239292731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43296252840864696638113949 16236094815324261239292731)
        ·
          refine ⟨24354142222986391858939097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16236094815324261239292731 24354142222986391858939097)
          ·
            refine ⟨18265606667239793894204323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24354142222986391858939097 18265606667239793894204323)
            ·
              refine ⟨27398410000859690841306485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18265606667239793894204323 27398410000859690841306485)
              ·
                refine ⟨2568600937580596016372483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27398410000859690841306485 2568600937580596016372483)
                ·
                  refine ⟨3852901406370894024558725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568600937580596016372483 3852901406370894024558725)
                  ·
                    refine ⟨722419013694542629604761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3852901406370894024558725 722419013694542629604761)
                    ·
                      rfl

theorem cell22_2110359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_2110359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110359 prefixEnd_2110359 := by exact prefixLift 2110359
  have htrace : WordTrace (prefixWord ++ tailWord_2110359) baseStart_2110359 baseEnd_2110359 := by
    simpa [prefixWord, tailWord_2110359, baseEnd_2110359] using wordTrace_append hprefix tailTrace_2110359
  have hstable : (prefixWord ++ tailWord_2110359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110359).length < 2 ^ (prefixWord ++ tailWord_2110359).sum := by decide
  have hdescent : baseEnd_2110359 < baseStart_2110359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110387 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 6]
def baseStart_2110387 : Nat := 118140960795 + 2110387 * 2 ^ 59
def prefixEnd_2110387 : Nat := 4983230072969 + 3 ^ 40 * 2110387 * 2
def baseEnd_2110387 : Nat := 722428598666759889904675

theorem tailTrace_2110387 : CollatzResearch.WordTrace tailWord_2110387 prefixEnd_2110387 722428598666759889904675 := by
  unfold tailWord_2110387
  simp only [CollatzResearch.WordTrace]
  refine ⟨76972137405435799249777415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51314758270290532833184943 76972137405435799249777415)
  ·
    refine ⟨115458206108153698874666123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76972137405435799249777415 115458206108153698874666123)
    ·
      refine ⟨173187309162230548311999185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115458206108153698874666123 173187309162230548311999185)
      ·
        refine ⟨129890481871672911233999389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173187309162230548311999185 129890481871672911233999389)
        ·
          refine ⟨48708930701877341712749771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129890481871672911233999389 48708930701877341712749771)
          ·
            refine ⟨73063396052816012569124657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48708930701877341712749771 73063396052816012569124657)
            ·
              refine ⟨54797547039612009426843493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73063396052816012569124657 54797547039612009426843493)
              ·
                refine ⟨10274540069927251767533155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54797547039612009426843493 10274540069927251767533155)
                ·
                  refine ⟨15411810104890877651299733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10274540069927251767533155 15411810104890877651299733)
                  ·
                    refine ⟨722428598666759889904675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15411810104890877651299733 722428598666759889904675)
                    ·
                      rfl

theorem cell22_2110387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_2110387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110387 prefixEnd_2110387 := by exact prefixLift 2110387
  have htrace : WordTrace (prefixWord ++ tailWord_2110387) baseStart_2110387 baseEnd_2110387 := by
    simpa [prefixWord, tailWord_2110387, baseEnd_2110387] using wordTrace_append hprefix tailTrace_2110387
  have hstable : (prefixWord ++ tailWord_2110387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110387).length < 2 ^ (prefixWord ++ tailWord_2110387).sum := by decide
  have hdescent : baseEnd_2110387 < baseStart_2110387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110389 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2110389 : Nat := 118140960795 + 2110389 * 2 ^ 59
def prefixEnd_2110389 : Nat := 4983230072969 + 3 ^ 40 * 2110389 * 2
def baseEnd_2110389 : Nat := 722429283307632551354669

theorem tailTrace_2110389 : CollatzResearch.WordTrace tailWord_2110389 prefixEnd_2110389 722429283307632551354669 := by
  unfold tailWord_2110389
  simp only [CollatzResearch.WordTrace]
  refine ⟨76972210351428553591350221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51314806900952369060900147 76972210351428553591350221)
  ·
    refine ⟨28864578881785707596756333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76972210351428553591350221 28864578881785707596756333)
    ·
      refine ⟨10824217080669640348783625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28864578881785707596756333 10824217080669640348783625)
      ·
        refine ⟨8118162810502230261587719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10824217080669640348783625 8118162810502230261587719)
        ·
          refine ⟨12177244215753345392381579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118162810502230261587719 12177244215753345392381579)
          ·
            refine ⟨18265866323630018088572369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12177244215753345392381579 18265866323630018088572369)
            ·
              refine ⟨13699399742722513566429277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18265866323630018088572369 13699399742722513566429277)
              ·
                refine ⟨5137274903520942587410979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13699399742722513566429277 5137274903520942587410979)
                ·
                  refine ⟨7705912355281413881116469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5137274903520942587410979 7705912355281413881116469)
                  ·
                    refine ⟨722429283307632551354669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7705912355281413881116469 722429283307632551354669)
                    ·
                      rfl

theorem cell22_2110389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2110389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110389 prefixEnd_2110389 := by exact prefixLift 2110389
  have htrace : WordTrace (prefixWord ++ tailWord_2110389) baseStart_2110389 baseEnd_2110389 := by
    simpa [prefixWord, tailWord_2110389, baseEnd_2110389] using wordTrace_append hprefix tailTrace_2110389
  have hstable : (prefixWord ++ tailWord_2110389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110389).length < 2 ^ (prefixWord ++ tailWord_2110389).sum := by decide
  have hdescent : baseEnd_2110389 < baseStart_2110389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110498 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2110498 : Nat := 118140960795 + 2110498 * 2 ^ 59
def prefixEnd_2110498 : Nat := 4983230072969 + 3 ^ 40 * 2110498 * 2
def baseEnd_2110498 : Nat := 240822198745064200126445

theorem tailTrace_2110498 : CollatzResearch.WordTrace tailWord_2110498 prefixEnd_2110498 240822198745064200126445 := by
  unfold tailWord_2110498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19244046477008416301767037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51317457272022443471378765 19244046477008416301767037)
  ·
    refine ⟨7216517428878156113162639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19244046477008416301767037 7216517428878156113162639)
    ·
      refine ⟨10824776143317234169743959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216517428878156113162639 10824776143317234169743959)
      ·
        refine ⟨16237164214975851254615939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824776143317234169743959 16237164214975851254615939)
        ·
          refine ⟨24355746322463776881923909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16237164214975851254615939 24355746322463776881923909)
          ·
            refine ⟨4566702435461958165360733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24355746322463776881923909 4566702435461958165360733)
            ·
              refine ⟨1712513413298234312010275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4566702435461958165360733 1712513413298234312010275)
              ·
                refine ⟨2568770119947351468015413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712513413298234312010275 2568770119947351468015413)
                ·
                  refine ⟨240822198745064200126445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2568770119947351468015413 240822198745064200126445)
                  ·
                    rfl

theorem cell22_2110498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2110498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110498 prefixEnd_2110498 := by exact prefixLift 2110498
  have htrace : WordTrace (prefixWord ++ tailWord_2110498) baseStart_2110498 baseEnd_2110498 := by
    simpa [prefixWord, tailWord_2110498, baseEnd_2110498] using wordTrace_append hprefix tailTrace_2110498
  have hstable : (prefixWord ++ tailWord_2110498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110498).length < 2 ^ (prefixWord ++ tailWord_2110498).sum := by decide
  have hdescent : baseEnd_2110498 < baseStart_2110498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110556 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2110556 : Nat := 118140960795 + 2110556 * 2 ^ 59
def prefixEnd_2110556 : Nat := 4983230072969 + 3 ^ 40 * 2110556 * 2
def baseEnd_2110556 : Nat := 722486450820499782429157

theorem tailTrace_2110556 : CollatzResearch.WordTrace tailWord_2110556 prefixEnd_2110556 722486450820499782429157 := by
  unfold tailWord_2110556
  simp only [CollatzResearch.WordTrace]
  refine ⟨38489150670911770556339761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51318867561215694075119681 38489150670911770556339761)
  ·
    refine ⟨28866863003183827917254821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38489150670911770556339761 28866863003183827917254821)
    ·
      refine ⟨5412536813096967734485279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28866863003183827917254821 5412536813096967734485279)
      ·
        refine ⟨8118805219645451601727919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412536813096967734485279 8118805219645451601727919)
        ·
          refine ⟨12178207829468177402591879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118805219645451601727919 12178207829468177402591879)
          ·
            refine ⟨18267311744202266103887819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12178207829468177402591879 18267311744202266103887819)
            ·
              refine ⟨27400967616303399155831729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18267311744202266103887819 27400967616303399155831729)
              ·
                refine ⟨20550725712227549366873797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27400967616303399155831729 20550725712227549366873797)
                ·
                  refine ⟨3853261071042665506288837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20550725712227549366873797 3853261071042665506288837)
                  ·
                    refine ⟨722486450820499782429157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853261071042665506288837 722486450820499782429157)
                    ·
                      rfl

theorem cell22_2110556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2110556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110556 prefixEnd_2110556 := by exact prefixLift 2110556
  have htrace : WordTrace (prefixWord ++ tailWord_2110556) baseStart_2110556 baseEnd_2110556 := by
    simpa [prefixWord, tailWord_2110556, baseEnd_2110556] using wordTrace_append hprefix tailTrace_2110556
  have hstable : (prefixWord ++ tailWord_2110556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110556).length < 2 ^ (prefixWord ++ tailWord_2110556).sum := by decide
  have hdescent : baseEnd_2110556 < baseStart_2110556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110573 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2110573 : Nat := 118140960795 + 2110573 * 2 ^ 59
def prefixEnd_2110573 : Nat := 4983230072969 + 3 ^ 40 * 2110573 * 2
def baseEnd_2110573 : Nat := 722492270267917404754105

theorem tailTrace_2110573 : CollatzResearch.WordTrace tailWord_2110573 prefixEnd_2110573 722492270267917404754105 := by
  unfold tailWord_2110573
  simp only [CollatzResearch.WordTrace]
  refine ⟨76978921382761953016048373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51319280921841302010698915 76978921382761953016048373)
  ·
    refine ⟨7216773879633933095254535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76978921382761953016048373 7216773879633933095254535)
    ·
      refine ⟨10825160819450899642881803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7216773879633933095254535 10825160819450899642881803)
      ·
        refine ⟨16237741229176349464322705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10825160819450899642881803 16237741229176349464322705)
        ·
          refine ⟨12178305921882262098242029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16237741229176349464322705 12178305921882262098242029)
          ·
            refine ⟨4566864720705848286840761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12178305921882262098242029 4566864720705848286840761)
            ·
              refine ⟨3425148540529386215130571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566864720705848286840761 3425148540529386215130571)
              ·
                refine ⟨5137722810794079322695857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3425148540529386215130571 5137722810794079322695857)
                ·
                  refine ⟨3853292108095559492021893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5137722810794079322695857 3853292108095559492021893)
                  ·
                    refine ⟨722492270267917404754105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853292108095559492021893 722492270267917404754105)
                    ·
                      rfl

theorem cell22_2110573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2110573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110573 prefixEnd_2110573 := by exact prefixLift 2110573
  have htrace : WordTrace (prefixWord ++ tailWord_2110573) baseStart_2110573 baseEnd_2110573 := by
    simpa [prefixWord, tailWord_2110573, baseEnd_2110573] using wordTrace_append hprefix tailTrace_2110573
  have hstable : (prefixWord ++ tailWord_2110573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110573).length < 2 ^ (prefixWord ++ tailWord_2110573).sum := by decide
  have hdescent : baseEnd_2110573 < baseStart_2110573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110680 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_2110680 : Nat := 118140960795 + 2110680 * 2 ^ 59
def prefixEnd_2110680 : Nat := 4983230072969 + 3 ^ 40 * 2110680 * 2
def baseEnd_2110680 : Nat := 722528898554604792328777

theorem tailTrace_2110680 : CollatzResearch.WordTrace tailWord_2110680 prefixEnd_2110680 722528898554604792328777 := by
  unfold tailWord_2110680
  simp only [CollatzResearch.WordTrace]
  refine ⟨38491411996687155145096747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51321882662249540193462329 38491411996687155145096747)
  ·
    refine ⟨57737117995030732717645121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38491411996687155145096747 57737117995030732717645121)
    ·
      refine ⟨43302838496273049538233841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57737117995030732717645121 43302838496273049538233841)
      ·
        refine ⟨32477128872204787153675381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43302838496273049538233841 32477128872204787153675381)
        ·
          refine ⟨3044730831769198795657067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32477128872204787153675381 3044730831769198795657067)
          ·
            refine ⟨4567096247653798193485601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044730831769198795657067 4567096247653798193485601)
            ·
              refine ⟨3425322185740348645114201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4567096247653798193485601 3425322185740348645114201)
              ·
                refine ⟨2568991639305261483835651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425322185740348645114201 2568991639305261483835651)
                ·
                  refine ⟨3853487458957892225753477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2568991639305261483835651 3853487458957892225753477)
                  ·
                    refine ⟨722528898554604792328777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853487458957892225753477 722528898554604792328777)
                    ·
                      rfl

theorem cell22_2110680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_2110680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110680 prefixEnd_2110680 := by exact prefixLift 2110680
  have htrace : WordTrace (prefixWord ++ tailWord_2110680) baseStart_2110680 baseEnd_2110680 := by
    simpa [prefixWord, tailWord_2110680, baseEnd_2110680] using wordTrace_append hprefix tailTrace_2110680
  have hstable : (prefixWord ++ tailWord_2110680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110680).length < 2 ^ (prefixWord ++ tailWord_2110680).sum := by decide
  have hdescent : baseEnd_2110680 < baseStart_2110680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110710 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_2110710 : Nat := 118140960795 + 2110710 * 2 ^ 59
def prefixEnd_2110710 : Nat := 4983230072969 + 3 ^ 40 * 2110710 * 2
def baseEnd_2110710 : Nat := 722539168167694714078685

theorem tailTrace_2110710 : CollatzResearch.WordTrace tailWord_2110710 prefixEnd_2110710 722539168167694714078685 := by
  unfold tailWord_2110710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811494886454101588361599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51322612122177083609190389 4811494886454101588361599)
  ·
    refine ⟨7217242329681152382542399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811494886454101588361599 7217242329681152382542399)
    ·
      refine ⟨10825863494521728573813599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7217242329681152382542399 10825863494521728573813599)
      ·
        refine ⟨16238795241782592860720399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10825863494521728573813599 16238795241782592860720399)
        ·
          refine ⟨24358192862673889291080599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16238795241782592860720399 24358192862673889291080599)
          ·
            refine ⟨36537289294010833936620899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24358192862673889291080599 36537289294010833936620899)
            ·
              refine ⟨54805933941016250904931349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36537289294010833936620899 54805933941016250904931349)
              ·
                refine ⟨2569028153485136761168657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54805933941016250904931349 2569028153485136761168657)
                ·
                  refine ⟨1926771115113852570876493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569028153485136761168657 1926771115113852570876493)
                  ·
                    refine ⟨722539168167694714078685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926771115113852570876493 722539168167694714078685)
                    ·
                      rfl

theorem cell22_2110710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_2110710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110710 prefixEnd_2110710 := by exact prefixLift 2110710
  have htrace : WordTrace (prefixWord ++ tailWord_2110710) baseStart_2110710 baseEnd_2110710 := by
    simpa [prefixWord, tailWord_2110710, baseEnd_2110710] using wordTrace_append hprefix tailTrace_2110710
  have hstable : (prefixWord ++ tailWord_2110710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110710).length < 2 ^ (prefixWord ++ tailWord_2110710).sum := by decide
  have hdescent : baseEnd_2110710 < baseStart_2110710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110768 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_2110768 : Nat := 118140960795 + 2110768 * 2 ^ 59
def prefixEnd_2110768 : Nat := 4983230072969 + 3 ^ 40 * 2110768 * 2
def baseEnd_2110768 : Nat := 240853007584333965376169

theorem tailTrace_2110768 : CollatzResearch.WordTrace tailWord_2110768 prefixEnd_2110768 240853007584333965376169 := by
  unfold tailWord_2110768
  simp only [CollatzResearch.WordTrace]
  refine ⟨38493016808527750659698479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51324022411370334212931305 38493016808527750659698479)
  ·
    refine ⟨57739525212791625989547719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38493016808527750659698479 57739525212791625989547719)
    ·
      refine ⟨86609287819187438984321579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57739525212791625989547719 86609287819187438984321579)
      ·
        refine ⟨129913931728781158476482369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86609287819187438984321579 129913931728781158476482369)
        ·
          refine ⟨97435448796585868857361777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129913931728781158476482369 97435448796585868857361777)
          ·
            refine ⟨73076586597439401643021333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97435448796585868857361777 73076586597439401643021333)
            ·
              refine ⟨3425464996754971952016625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73076586597439401643021333 3425464996754971952016625)
              ·
                refine ⟨2569098747566228964012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425464996754971952016625 2569098747566228964012469)
                ·
                  refine ⟨240853007584333965376169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569098747566228964012469 240853007584333965376169)
                  ·
                    rfl

theorem cell22_2110768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_2110768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110768 prefixEnd_2110768 := by exact prefixLift 2110768
  have htrace : WordTrace (prefixWord ++ tailWord_2110768) baseStart_2110768 baseEnd_2110768 := by
    simpa [prefixWord, tailWord_2110768, baseEnd_2110768] using wordTrace_append hprefix tailTrace_2110768
  have hstable : (prefixWord ++ tailWord_2110768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110768).length < 2 ^ (prefixWord ++ tailWord_2110768).sum := by decide
  have hdescent : baseEnd_2110768 < baseStart_2110768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110774 : List Nat := [5, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2110774 : Nat := 118140960795 + 2110774 * 2 ^ 59
def prefixEnd_2110774 : Nat := 4983230072969 + 3 ^ 40 * 2110774 * 2
def baseEnd_2110774 : Nat := 80284564075068875608721

theorem tailTrace_2110774 : CollatzResearch.WordTrace tailWord_2110774 prefixEnd_2110774 80284564075068875608721 := by
  unfold tailWord_2110774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811640778439610271507211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51324168303355842896076917 4811640778439610271507211)
  ·
    refine ⟨7217461167659415407260817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4811640778439610271507211 7217461167659415407260817)
    ·
      refine ⟨5413095875744561555445613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7217461167659415407260817 5413095875744561555445613)
      ·
        refine ⟨2029910953404210583292105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5413095875744561555445613 2029910953404210583292105)
        ·
          refine ⟨1522433215053157937469079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029910953404210583292105 1522433215053157937469079)
          ·
            refine ⟨2283649822579736906203619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522433215053157937469079 2283649822579736906203619)
            ·
              refine ⟨3425474733869605359305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283649822579736906203619 3425474733869605359305429)
              ·
                refine ⟨80284564075068875608721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3425474733869605359305429 80284564075068875608721)
                ·
                  rfl

theorem cell22_2110774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2110774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110774 prefixEnd_2110774 := by exact prefixLift 2110774
  have htrace : WordTrace (prefixWord ++ tailWord_2110774) baseStart_2110774 baseEnd_2110774 := by
    simpa [prefixWord, tailWord_2110774, baseEnd_2110774] using wordTrace_append hprefix tailTrace_2110774
  have hstable : (prefixWord ++ tailWord_2110774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110774).length < 2 ^ (prefixWord ++ tailWord_2110774).sum := by decide
  have hdescent : baseEnd_2110774 < baseStart_2110774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110783 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 2, 5]
def baseStart_2110783 : Nat := 118140960795 + 2110783 * 2 ^ 59
def prefixEnd_2110783 : Nat := 4983230072969 + 3 ^ 40 * 2110783 * 2
def baseEnd_2110783 : Nat := 722564157559546857003461

theorem tailTrace_2110783 : CollatzResearch.WordTrace tailWord_2110783 prefixEnd_2110783 722564157559546857003461 := by
  unfold tailWord_2110783
  simp only [CollatzResearch.WordTrace]
  refine ⟨76986580712001158881193003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51324387141334105920795335 76986580712001158881193003)
  ·
    refine ⟨115479871068001738321789505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76986580712001158881193003 115479871068001738321789505)
    ·
      refine ⟨86609903301001303741342129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115479871068001738321789505 86609903301001303741342129)
      ·
        refine ⟨64957427475750977806006597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86609903301001303741342129 64957427475750977806006597)
        ·
          refine ⟨12179517651703308338626237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64957427475750977806006597 12179517651703308338626237)
          ·
            refine ⟨4567319119388740626984839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12179517651703308338626237 4567319119388740626984839)
            ·
              refine ⟨6850978679083110940477259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4567319119388740626984839 6850978679083110940477259)
              ·
                refine ⟨10276468018624666410715889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6850978679083110940477259 10276468018624666410715889)
                ·
                  refine ⟨7707351013968499808036917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10276468018624666410715889 7707351013968499808036917)
                  ·
                    refine ⟨722564157559546857003461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7707351013968499808036917 722564157559546857003461)
                    ·
                      rfl

theorem cell22_2110783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_2110783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110783 prefixEnd_2110783 := by exact prefixLift 2110783
  have htrace : WordTrace (prefixWord ++ tailWord_2110783) baseStart_2110783 baseEnd_2110783 := by
    simpa [prefixWord, tailWord_2110783, baseEnd_2110783] using wordTrace_append hprefix tailTrace_2110783
  have hstable : (prefixWord ++ tailWord_2110783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110783).length < 2 ^ (prefixWord ++ tailWord_2110783).sum := by decide
  have hdescent : baseEnd_2110783 < baseStart_2110783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110785 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 5]
def baseStart_2110785 : Nat := 118140960795 + 2110785 * 2 ^ 59
def prefixEnd_2110785 : Nat := 4983230072969 + 3 ^ 40 * 2110785 * 2
def baseEnd_2110785 : Nat := 240854947400139839484485

theorem tailTrace_2110785 : CollatzResearch.WordTrace tailWord_2110785 prefixEnd_2110785 240854947400139839484485 := by
  unfold tailWord_2110785
  simp only [CollatzResearch.WordTrace]
  refine ⟨76986653657993913222765809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51324435771995942148510539 76986653657993913222765809)
  ·
    refine ⟨57739990243495434917074357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76986653657993913222765809 57739990243495434917074357)
    ·
      refine ⟨5413124085327697023475721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57739990243495434917074357 5413124085327697023475721)
      ·
        refine ⟨4059843063995772767606791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5413124085327697023475721 4059843063995772767606791)
        ·
          refine ⟨6089764595993659151410187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059843063995772767606791 6089764595993659151410187)
          ·
            refine ⟨9134646893990488727115281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089764595993659151410187 9134646893990488727115281)
            ·
              refine ⟨6850985170492866545336461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9134646893990488727115281 6850985170492866545336461)
              ·
                refine ⟨2569119438934824954501173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6850985170492866545336461 2569119438934824954501173)
                ·
                  refine ⟨240854947400139839484485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569119438934824954501173 240854947400139839484485)
                  ·
                    rfl

theorem cell22_2110785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_2110785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110785 prefixEnd_2110785 := by exact prefixLift 2110785
  have htrace : WordTrace (prefixWord ++ tailWord_2110785) baseStart_2110785 baseEnd_2110785 := by
    simpa [prefixWord, tailWord_2110785, baseEnd_2110785] using wordTrace_append hprefix tailTrace_2110785
  have hstable : (prefixWord ++ tailWord_2110785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110785).length < 2 ^ (prefixWord ++ tailWord_2110785).sum := by decide
  have hdescent : baseEnd_2110785 < baseStart_2110785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110798 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2110798 : Nat := 118140960795 + 2110798 * 2 ^ 59
def prefixEnd_2110798 : Nat := 4983230072969 + 3 ^ 40 * 2110798 * 2
def baseEnd_2110798 : Nat := 722569292366091817878415

theorem tailTrace_2110798 : CollatzResearch.WordTrace tailWord_2110798 prefixEnd_2110798 722569292366091817878415 := by
  unfold tailWord_2110798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9623390975868352055373631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51324751871297877628659365 9623390975868352055373631)
  ·
    refine ⟨14435086463802528083060447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9623390975868352055373631 14435086463802528083060447)
    ·
      refine ⟨21652629695703792124590671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14435086463802528083060447 21652629695703792124590671)
      ·
        refine ⟨32478944543555688186886007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21652629695703792124590671 32478944543555688186886007)
        ·
          refine ⟨48718416815333532280329011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32478944543555688186886007 48718416815333532280329011)
          ·
            refine ⟨73077625223000298420493517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48718416815333532280329011 73077625223000298420493517)
            ·
              refine ⟨27404109458625111907685069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73077625223000298420493517 27404109458625111907685069)
              ·
                refine ⟨10276541046984416965381901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27404109458625111907685069 10276541046984416965381901)
                ·
                  refine ⟨3853702892619156362018213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10276541046984416965381901 3853702892619156362018213)
                  ·
                    refine ⟨722569292366091817878415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3853702892619156362018213 722569292366091817878415)
                    ·
                      rfl

theorem cell22_2110798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2110798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110798 prefixEnd_2110798 := by exact prefixLift 2110798
  have htrace : WordTrace (prefixWord ++ tailWord_2110798) baseStart_2110798 baseEnd_2110798 := by
    simpa [prefixWord, tailWord_2110798, baseEnd_2110798] using wordTrace_append hprefix tailTrace_2110798
  have hstable : (prefixWord ++ tailWord_2110798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110798).length < 2 ^ (prefixWord ++ tailWord_2110798).sum := by decide
  have hdescent : baseEnd_2110798 < baseStart_2110798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110941 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2110941 : Nat := 118140960795 + 2110941 * 2 ^ 59
def prefixEnd_2110941 : Nat := 4983230072969 + 3 ^ 40 * 2110941 * 2
def baseEnd_2110941 : Nat := 722618244188487111552977

theorem tailTrace_2110941 : CollatzResearch.WordTrace tailWord_2110941 prefixEnd_2110941 722618244188487111552977 := by
  unfold tailWord_2110941
  simp only [CollatzResearch.WordTrace]
  refine ⟨76992343445428751865444677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51328228963619167910296451 76992343445428751865444677)
  ·
    refine ⟨14436064396017890974770877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76992343445428751865444677 14436064396017890974770877)
    ·
      refine ⟨5413524148506709115539079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14436064396017890974770877 5413524148506709115539079)
      ·
        refine ⟨8120286222760063673308619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413524148506709115539079 8120286222760063673308619)
        ·
          refine ⟨12180429334140095509962929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8120286222760063673308619 12180429334140095509962929)
          ·
            refine ⟨9135322000605071632472197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12180429334140095509962929 9135322000605071632472197)
            ·
              refine ⟨1712872875113450931088537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9135322000605071632472197 1712872875113450931088537)
              ·
                refine ⟨1284654656335088198316403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712872875113450931088537 1284654656335088198316403)
                ·
                  refine ⟨1926981984502632297474605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284654656335088198316403 1926981984502632297474605)
                  ·
                    refine ⟨722618244188487111552977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1926981984502632297474605 722618244188487111552977)
                    ·
                      rfl

theorem cell22_2110941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2110941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110941 prefixEnd_2110941 := by exact prefixLift 2110941
  have htrace : WordTrace (prefixWord ++ tailWord_2110941) baseStart_2110941 baseEnd_2110941 := by
    simpa [prefixWord, tailWord_2110941, baseEnd_2110941] using wordTrace_append hprefix tailTrace_2110941
  have hstable : (prefixWord ++ tailWord_2110941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110941).length < 2 ^ (prefixWord ++ tailWord_2110941).sum := by decide
  have hdescent : baseEnd_2110941 < baseStart_2110941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110948 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_2110948 : Nat := 118140960795 + 2110948 * 2 ^ 59
def prefixEnd_2110948 : Nat := 4983230072969 + 3 ^ 40 * 2110948 * 2
def baseEnd_2110948 : Nat := 240873546810513808875985

theorem tailTrace_2110948 : CollatzResearch.WordTrace tailWord_2110948 prefixEnd_2110948 240873546810513808875985 := by
  unfold tailWord_2110948
  simp only [CollatzResearch.WordTrace]
  refine ⟨38496299378201696030474749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51328399170935594707299665 38496299378201696030474749)
  ·
    refine ⟨14436112266825636011428031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38496299378201696030474749 14436112266825636011428031)
    ·
      refine ⟨21654168400238454017142047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14436112266825636011428031 21654168400238454017142047)
      ·
        refine ⟨32481252600357681025713071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21654168400238454017142047 32481252600357681025713071)
        ·
          refine ⟨48721878900536521538569607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32481252600357681025713071 48721878900536521538569607)
          ·
            refine ⟨73082818350804782307854411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48721878900536521538569607 73082818350804782307854411)
            ·
              refine ⟨109624227526207173461781617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73082818350804782307854411 109624227526207173461781617)
              ·
                refine ⟨82218170644655380096336213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109624227526207173461781617 82218170644655380096336213)
                ·
                  refine ⟨240873546810513808875985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 82218170644655380096336213 240873546810513808875985)
                  ·
                    rfl

theorem cell22_2110948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_2110948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110948 prefixEnd_2110948 := by exact prefixLift 2110948
  have htrace : WordTrace (prefixWord ++ tailWord_2110948) baseStart_2110948 baseEnd_2110948 := by
    simpa [prefixWord, tailWord_2110948, baseEnd_2110948] using wordTrace_append hprefix tailTrace_2110948
  have hstable : (prefixWord ++ tailWord_2110948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110948).length < 2 ^ (prefixWord ++ tailWord_2110948).sum := by decide
  have hdescent : baseEnd_2110948 < baseStart_2110948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110993 : List Nat := [1, 2, 2, 1, 1, 2, 13]
def baseStart_2110993 : Nat := 118140960795 + 2110993 * 2 ^ 59
def prefixEnd_2110993 : Nat := 4983230072969 + 3 ^ 40 * 2110993 * 2
def baseEnd_2110993 : Nat := 26764297957450974416771

theorem tailTrace_2110993 : CollatzResearch.WordTrace tailWord_2110993 prefixEnd_2110993 26764297957450974416771 := by
  unfold tailWord_2110993
  simp only [CollatzResearch.WordTrace]
  refine ⟨76994240041240364746337633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51329493360826909830891755 76994240041240364746337633)
  ·
    refine ⟨57745680030930273559753225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76994240041240364746337633 57745680030930273559753225)
    ·
      refine ⟨43309260023197705169814919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57745680030930273559753225 43309260023197705169814919)
      ·
        refine ⟨64963890034796557754722379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43309260023197705169814919 64963890034796557754722379)
        ·
          refine ⟨97445835052194836632083569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64963890034796557754722379 97445835052194836632083569)
          ·
            refine ⟨73084376289146127474062677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97445835052194836632083569 73084376289146127474062677)
            ·
              refine ⟨26764297957450974416771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 73084376289146127474062677 26764297957450974416771)
              ·
                rfl

theorem cell22_2110993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 13].length) (baseStart_2110993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110993 prefixEnd_2110993 := by exact prefixLift 2110993
  have htrace : WordTrace (prefixWord ++ tailWord_2110993) baseStart_2110993 baseEnd_2110993 := by
    simpa [prefixWord, tailWord_2110993, baseEnd_2110993] using wordTrace_append hprefix tailTrace_2110993
  have hstable : (prefixWord ++ tailWord_2110993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110993).length < 2 ^ (prefixWord ++ tailWord_2110993).sum := by decide
  have hdescent : baseEnd_2110993 < baseStart_2110993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2110997 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_2110997 : Nat := 118140960795 + 2110997 * 2 ^ 59
def prefixEnd_2110997 : Nat := 4983230072969 + 3 ^ 40 * 2110997 * 2
def baseEnd_2110997 : Nat := 722637414132921632152805

theorem tailTrace_2110997 : CollatzResearch.WordTrace tailWord_2110997 prefixEnd_2110997 722637414132921632152805 := by
  unfold tailWord_2110997
  simp only [CollatzResearch.WordTrace]
  refine ⟨76994385933225873429483245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51329590622150582286322163 76994385933225873429483245)
  ·
    refine ⟨28872894724959702536056217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76994385933225873429483245 28872894724959702536056217)
    ·
      refine ⟨21654671043719776902042163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28872894724959702536056217 21654671043719776902042163)
      ·
        refine ⟨32482006565579665353063245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21654671043719776902042163 32482006565579665353063245)
        ·
          refine ⟨12180752462092374507398717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32482006565579665353063245 12180752462092374507398717)
          ·
            refine ⟨4567782173284640440274519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12180752462092374507398717 4567782173284640440274519)
            ·
              refine ⟨6851673259926960660411779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4567782173284640440274519 6851673259926960660411779)
              ·
                refine ⟨10277509889890440990617669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6851673259926960660411779 10277509889890440990617669)
                ·
                  refine ⟨1927033104354457685740813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10277509889890440990617669 1927033104354457685740813)
                  ·
                    refine ⟨722637414132921632152805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927033104354457685740813 722637414132921632152805)
                    ·
                      rfl

theorem cell22_2110997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_2110997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2110997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2110997 prefixEnd_2110997 := by exact prefixLift 2110997
  have htrace : WordTrace (prefixWord ++ tailWord_2110997) baseStart_2110997 baseEnd_2110997 := by
    simpa [prefixWord, tailWord_2110997, baseEnd_2110997] using wordTrace_append hprefix tailTrace_2110997
  have hstable : (prefixWord ++ tailWord_2110997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2110997).length < 2 ^ (prefixWord ++ tailWord_2110997).sum := by decide
  have hdescent : baseEnd_2110997 < baseStart_2110997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2110997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111027 : List Nat := [1, 1, 1, 2, 4, 5, 2, 6]
def baseStart_2111027 : Nat := 118140960795 + 2111027 * 2 ^ 59
def prefixEnd_2111027 : Nat := 4983230072969 + 3 ^ 40 * 2111027 * 2
def baseEnd_2111027 : Nat := 80294187082890172655857

theorem tailTrace_2111027 : CollatzResearch.WordTrace tailWord_2111027 prefixEnd_2111027 80294187082890172655857 := by
  unfold tailWord_2111027
  simp only [CollatzResearch.WordTrace]
  refine ⟨76995480123117188553075335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51330320082078125702050223 76995480123117188553075335)
  ·
    refine ⟨115493220184675782829613003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76995480123117188553075335 115493220184675782829613003)
    ·
      refine ⟨173239830277013674244419505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115493220184675782829613003 173239830277013674244419505)
      ·
        refine ⟨129929872707760255683314629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173239830277013674244419505 129929872707760255683314629)
        ·
          refine ⟨24361851132705047940621493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129929872707760255683314629 24361851132705047940621493)
          ·
            refine ⟨2283923543691098244433265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24361851132705047940621493 2283923543691098244433265)
            ·
              refine ⟨1712942657768323683324949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2283923543691098244433265 1712942657768323683324949)
              ·
                refine ⟨80294187082890172655857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1712942657768323683324949 80294187082890172655857)
                ·
                  rfl

theorem cell22_2111027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 6].length) (baseStart_2111027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111027 prefixEnd_2111027 := by exact prefixLift 2111027
  have htrace : WordTrace (prefixWord ++ tailWord_2111027) baseStart_2111027 baseEnd_2111027 := by
    simpa [prefixWord, tailWord_2111027, baseEnd_2111027] using wordTrace_append hprefix tailTrace_2111027
  have hstable : (prefixWord ++ tailWord_2111027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111027).length < 2 ^ (prefixWord ++ tailWord_2111027).sum := by decide
  have hdescent : baseEnd_2111027 < baseStart_2111027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111046 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2111046 : Nat := 118140960795 + 2111046 * 2 ^ 59
def prefixEnd_2111046 : Nat := 4983230072969 + 3 ^ 40 * 2111046 * 2
def baseEnd_2111046 : Nat := 722654187834301837677655

theorem tailTrace_2111046 : CollatzResearch.WordTrace tailWord_2111046 prefixEnd_2111046 722654187834301837677655 := by
  unfold tailWord_2111046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406130409689011087438031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 51330782073365569865344661 2406130409689011087438031)
  ·
    refine ⟨3609195614533516631157047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2406130409689011087438031 3609195614533516631157047)
    ·
      refine ⟨5413793421800274946735571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609195614533516631157047 5413793421800274946735571)
      ·
        refine ⟨8120690132700412420103357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5413793421800274946735571 8120690132700412420103357)
        ·
          refine ⟨3045258799762654657538759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8120690132700412420103357 3045258799762654657538759)
          ·
            refine ⟨4567888199643981986308139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3045258799762654657538759 4567888199643981986308139)
            ·
              refine ⟨6851832299465972979462209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4567888199643981986308139 6851832299465972979462209)
              ·
                refine ⟨5138874224599479734596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6851832299465972979462209 5138874224599479734596657)
                ·
                  refine ⟨3854155668449609800947493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5138874224599479734596657 3854155668449609800947493)
                  ·
                    refine ⟨722654187834301837677655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3854155668449609800947493 722654187834301837677655)
                    ·
                      rfl

theorem cell22_2111046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2111046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111046 prefixEnd_2111046 := by exact prefixLift 2111046
  have htrace : WordTrace (prefixWord ++ tailWord_2111046) baseStart_2111046 baseEnd_2111046 := by
    simpa [prefixWord, tailWord_2111046, baseEnd_2111046] using wordTrace_append hprefix tailTrace_2111046
  have hstable : (prefixWord ++ tailWord_2111046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111046).length < 2 ^ (prefixWord ++ tailWord_2111046).sum := by decide
  have hdescent : baseEnd_2111046 < baseStart_2111046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111055 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 5]
def baseStart_2111055 : Nat := 118140960795 + 2111055 * 2 ^ 59
def prefixEnd_2111055 : Nat := 4983230072969 + 3 ^ 40 * 2111055 * 2
def baseEnd_2111055 : Nat := 240885756239409604734209

theorem tailTrace_2111055 : CollatzResearch.WordTrace tailWord_2111055 prefixEnd_2111055 240885756239409604734209 := by
  unfold tailWord_2111055
  simp only [CollatzResearch.WordTrace]
  refine ⟨76996501367015749335094619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51331000911343832890063079 76996501367015749335094619)
  ·
    refine ⟨115494752050523624002641929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76996501367015749335094619 115494752050523624002641929)
    ·
      refine ⟨86621064037892718001981447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115494752050523624002641929 86621064037892718001981447)
      ·
        refine ⟨129931596056839077002972171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86621064037892718001981447 129931596056839077002972171)
        ·
          refine ⟨194897394085258615504458257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129931596056839077002972171 194897394085258615504458257)
          ·
            refine ⟨146173045563943961628343693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194897394085258615504458257 146173045563943961628343693)
            ·
              refine ⟨54814892086478985610628885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146173045563943961628343693 54814892086478985610628885)
              ·
                refine ⟨2569448066553702450498229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54814892086478985610628885 2569448066553702450498229)
                ·
                  refine ⟨240885756239409604734209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2569448066553702450498229 240885756239409604734209)
                  ·
                    rfl

theorem cell22_2111055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 5].length) (baseStart_2111055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111055 prefixEnd_2111055 := by exact prefixLift 2111055
  have htrace : WordTrace (prefixWord ++ tailWord_2111055) baseStart_2111055 baseEnd_2111055 := by
    simpa [prefixWord, tailWord_2111055, baseEnd_2111055] using wordTrace_append hprefix tailTrace_2111055
  have hstable : (prefixWord ++ tailWord_2111055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111055).length < 2 ^ (prefixWord ++ tailWord_2111055).sum := by decide
  have hdescent : baseEnd_2111055 < baseStart_2111055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111115 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_2111115 : Nat := 118140960795 + 2111115 * 2 ^ 59
def prefixEnd_2111115 : Nat := 4983230072969 + 3 ^ 40 * 2111115 * 2
def baseEnd_2111115 : Nat := 722677807944408657702443

theorem tailTrace_2111115 : CollatzResearch.WordTrace tailWord_2111115 prefixEnd_2111115 722677807944408657702443 := by
  unfold tailWord_2111115
  simp only [CollatzResearch.WordTrace]
  refine ⟨76998689746798379582278799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51332459831198919721519199 76998689746798379582278799)
  ·
    refine ⟨115498034620197569373418199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76998689746798379582278799 115498034620197569373418199)
    ·
      refine ⟨173247051930296354060127299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115498034620197569373418199 173247051930296354060127299)
      ·
        refine ⟨259870577895444531090190949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173247051930296354060127299 259870577895444531090190949)
        ·
          refine ⟨48725733355395849579410803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259870577895444531090190949 48725733355395849579410803)
          ·
            refine ⟨73088600033093774369116205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48725733355395849579410803 73088600033093774369116205)
            ·
              refine ⟨27408225012410165388418577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73088600033093774369116205 27408225012410165388418577)
              ·
                refine ⟨20556168759307624041313933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27408225012410165388418577 20556168759307624041313933)
                ·
                  refine ⟨7708563284740359015492725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20556168759307624041313933 7708563284740359015492725)
                  ·
                    refine ⟨722677807944408657702443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7708563284740359015492725 722677807944408657702443)
                    ·
                      rfl

theorem cell22_2111115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_2111115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111115 prefixEnd_2111115 := by exact prefixLift 2111115
  have htrace : WordTrace (prefixWord ++ tailWord_2111115) baseStart_2111115 baseEnd_2111115 := by
    simpa [prefixWord, tailWord_2111115, baseEnd_2111115] using wordTrace_append hprefix tailTrace_2111115
  have hstable : (prefixWord ++ tailWord_2111115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111115).length < 2 ^ (prefixWord ++ tailWord_2111115).sum := by decide
  have hdescent : baseEnd_2111115 < baseStart_2111115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111134 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2111134 : Nat := 118140960795 + 2111134 * 2 ^ 59
def prefixEnd_2111134 : Nat := 4983230072969 + 3 ^ 40 * 2111134 * 2
def baseEnd_2111134 : Nat := 240894770677566313825795

theorem tailTrace_2111134 : CollatzResearch.WordTrace tailWord_2111134 prefixEnd_2111134 240894770677566313825795 := by
  unfold tailWord_2111134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9624922841716193228402557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51332921822486363884813637 9624922841716193228402557)
  ·
    refine ⟨3609346065643572460650959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9624922841716193228402557 3609346065643572460650959)
    ·
      refine ⟨5414019098465358690976439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3609346065643572460650959 5414019098465358690976439)
      ·
        refine ⟨8121028647698038036464659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5414019098465358690976439 8121028647698038036464659)
        ·
          refine ⟨12181542971547057054696989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8121028647698038036464659 12181542971547057054696989)
          ·
            refine ⟨4568078614330146395511371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12181542971547057054696989 4568078614330146395511371)
            ·
              refine ⟨6852117921495219593267057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4568078614330146395511371 6852117921495219593267057)
              ·
                refine ⟨5139088441121414694950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6852117921495219593267057 5139088441121414694950293)
                ·
                  refine ⟨240894770677566313825795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5139088441121414694950293 240894770677566313825795)
                  ·
                    rfl

theorem cell22_2111134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2111134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111134 prefixEnd_2111134 := by exact prefixLift 2111134
  have htrace : WordTrace (prefixWord ++ tailWord_2111134) baseStart_2111134 baseEnd_2111134 := by
    simpa [prefixWord, tailWord_2111134, baseEnd_2111134] using wordTrace_append hprefix tailTrace_2111134
  have hstable : (prefixWord ++ tailWord_2111134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111134).length < 2 ^ (prefixWord ++ tailWord_2111134).sum := by decide
  have hdescent : baseEnd_2111134 < baseStart_2111134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111149 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2111149 : Nat := 118140960795 + 2111149 * 2 ^ 59
def prefixEnd_2111149 : Nat := 4983230072969 + 3 ^ 40 * 2111149 * 2
def baseEnd_2111149 : Nat := 722689446839243902352339

theorem tailTrace_2111149 : CollatzResearch.WordTrace tailWord_2111149 prefixEnd_2111149 722689446839243902352339 := by
  unfold tailWord_2111149
  simp only [CollatzResearch.WordTrace]
  refine ⟨76999929828675203389016501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51333286552450135592677667 76999929828675203389016501)
  ·
    refine ⟨7218743421438300317720297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76999929828675203389016501 7218743421438300317720297)
    ·
      refine ⟨5414057566078725238290223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7218743421438300317720297 5414057566078725238290223)
      ·
        refine ⟨8121086349118087857435335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5414057566078725238290223 8121086349118087857435335)
        ·
          refine ⟨12181629523677131786153003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8121086349118087857435335 12181629523677131786153003)
          ·
            refine ⟨18272444285515697679229505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12181629523677131786153003 18272444285515697679229505)
            ·
              refine ⟨13704333214136773259422129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18272444285515697679229505 13704333214136773259422129)
              ·
                refine ⟨10278249910602579944566597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13704333214136773259422129 10278249910602579944566597)
                ·
                  refine ⟨1927171858237983739606237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10278249910602579944566597 1927171858237983739606237)
                  ·
                    refine ⟨722689446839243902352339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927171858237983739606237 722689446839243902352339)
                    ·
                      rfl

theorem cell22_2111149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2111149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111149 prefixEnd_2111149 := by exact prefixLift 2111149
  have htrace : WordTrace (prefixWord ++ tailWord_2111149) baseStart_2111149 baseEnd_2111149 := by
    simpa [prefixWord, tailWord_2111149, baseEnd_2111149] using wordTrace_append hprefix tailTrace_2111149
  have hstable : (prefixWord ++ tailWord_2111149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111149).length < 2 ^ (prefixWord ++ tailWord_2111149).sum := by decide
  have hdescent : baseEnd_2111149 < baseStart_2111149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111160 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2111160 : Nat := 118140960795 + 2111160 * 2 ^ 59
def prefixEnd_2111160 : Nat := 4983230072969 + 3 ^ 40 * 2111160 * 2
def baseEnd_2111160 : Nat := 722693212364043540327305

theorem tailTrace_2111160 : CollatzResearch.WordTrace tailWord_2111160 prefixEnd_2111160 722693212364043540327305 := by
  unfold tailWord_2111160
  simp only [CollatzResearch.WordTrace]
  refine ⟨38500165515817676133833467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51333554021090234845111289 38500165515817676133833467)
  ·
    refine ⟨57750248273726514200750201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38500165515817676133833467 57750248273726514200750201)
    ·
      refine ⟨43312686205294885650562651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57750248273726514200750201 43312686205294885650562651)
      ·
        refine ⟨64969029307942328475843977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43312686205294885650562651 64969029307942328475843977)
        ·
          refine ⟨48726771980956746356882983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64969029307942328475843977 48726771980956746356882983)
          ·
            refine ⟨73090157971435119535324475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48726771980956746356882983 73090157971435119535324475)
            ·
              refine ⟨109635236957152679302986713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73090157971435119535324475 109635236957152679302986713)
              ·
                refine ⟨82226427717864509477240035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109635236957152679302986713 82226427717864509477240035)
                ·
                  refine ⟨123339641576796764215860053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82226427717864509477240035 123339641576796764215860053)
                  ·
                    refine ⟨722693212364043540327305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123339641576796764215860053 722693212364043540327305)
                    ·
                      rfl

theorem cell22_2111160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2111160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111160 prefixEnd_2111160 := by exact prefixLift 2111160
  have htrace : WordTrace (prefixWord ++ tailWord_2111160) baseStart_2111160 baseEnd_2111160 := by
    simpa [prefixWord, tailWord_2111160, baseEnd_2111160] using wordTrace_append hprefix tailTrace_2111160
  have hstable : (prefixWord ++ tailWord_2111160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111160).length < 2 ^ (prefixWord ++ tailWord_2111160).sum := by decide
  have hdescent : baseEnd_2111160 < baseStart_2111160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111166 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_2111166 : Nat := 118140960795 + 2111166 * 2 ^ 59
def prefixEnd_2111166 : Nat := 4983230072969 + 3 ^ 40 * 2111166 * 2
def baseEnd_2111166 : Nat := 722695266286661524677287

theorem tailTrace_2111166 : CollatzResearch.WordTrace tailWord_2111166 prefixEnd_2111166 722695266286661524677287 := by
  unfold tailWord_2111166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625068733701701911548169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51333699913075743528256901 9625068733701701911548169)
  ·
    refine ⟨7218801550276276433661127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9625068733701701911548169 7218801550276276433661127)
    ·
      refine ⟨10828202325414414650491691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7218801550276276433661127 10828202325414414650491691)
      ·
        refine ⟨16242303488121621975737537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10828202325414414650491691 16242303488121621975737537)
        ·
          refine ⟨12181727616091216481803153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16242303488121621975737537 12181727616091216481803153)
          ·
            refine ⟨9136295712068412361352365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12181727616091216481803153 9136295712068412361352365)
            ·
              refine ⟨3426110892025654635507137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9136295712068412361352365 3426110892025654635507137)
              ·
                refine ⟨2569583169019240976630353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426110892025654635507137 2569583169019240976630353)
                ·
                  refine ⟨1927187376764430732472765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2569583169019240976630353 1927187376764430732472765)
                  ·
                    refine ⟨722695266286661524677287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927187376764430732472765 722695266286661524677287)
                    ·
                      rfl

theorem cell22_2111166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_2111166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111166 prefixEnd_2111166 := by exact prefixLift 2111166
  have htrace : WordTrace (prefixWord ++ tailWord_2111166) baseStart_2111166 baseEnd_2111166 := by
    simpa [prefixWord, tailWord_2111166, baseEnd_2111166] using wordTrace_append hprefix tailTrace_2111166
  have hstable : (prefixWord ++ tailWord_2111166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111166).length < 2 ^ (prefixWord ++ tailWord_2111166).sum := by decide
  have hdescent : baseEnd_2111166 < baseStart_2111166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111194 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_2111194 : Nat := 118140960795 + 2111194 * 2 ^ 59
def prefixEnd_2111194 : Nat := 4983230072969 + 3 ^ 40 * 2111194 * 2
def baseEnd_2111194 : Nat := 722704851258878784977201

theorem tailTrace_2111194 : CollatzResearch.WordTrace tailWord_2111194 prefixEnd_2111194 722704851258878784977201 := by
  unfold tailWord_2111194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19250392778378044018601159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51334380742341450716269757 19250392778378044018601159)
  ·
    refine ⟨28875589167567066027901739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19250392778378044018601159 28875589167567066027901739)
    ·
      refine ⟨43313383751350599041852609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28875589167567066027901739 43313383751350599041852609)
      ·
        refine ⟨32485037813512949281389457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43313383751350599041852609 32485037813512949281389457)
        ·
          refine ⟨24363778360134711961042093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32485037813512949281389457 24363778360134711961042093)
          ·
            refine ⟨9136416885050516985390785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24363778360134711961042093 9136416885050516985390785)
            ·
              refine ⟨6852312663787887739043089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9136416885050516985390785 6852312663787887739043089)
              ·
                refine ⟨5139234497840915804282317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6852312663787887739043089 5139234497840915804282317)
                ·
                  refine ⟨1927212936690343426605869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5139234497840915804282317 1927212936690343426605869)
                  ·
                    refine ⟨722704851258878784977201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927212936690343426605869 722704851258878784977201)
                    ·
                      rfl

theorem cell22_2111194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_2111194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111194 prefixEnd_2111194 := by exact prefixLift 2111194
  have htrace : WordTrace (prefixWord ++ tailWord_2111194) baseStart_2111194 baseEnd_2111194 := by
    simpa [prefixWord, tailWord_2111194, baseEnd_2111194] using wordTrace_append hprefix tailTrace_2111194
  have hstable : (prefixWord ++ tailWord_2111194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111194).length < 2 ^ (prefixWord ++ tailWord_2111194).sum := by decide
  have hdescent : baseEnd_2111194 < baseStart_2111194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111211 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 1, 3]
def baseStart_2111211 : Nat := 118140960795 + 2111211 * 2 ^ 59
def prefixEnd_2111211 : Nat := 4983230072969 + 3 ^ 40 * 2111211 * 2
def baseEnd_2111211 : Nat := 722710670706296407302149

theorem tailTrace_2111211 : CollatzResearch.WordTrace tailWord_2111211 prefixEnd_2111211 722710670706296407302149 := by
  unfold tailWord_2111211
  simp only [CollatzResearch.WordTrace]
  refine ⟨77002191154450587977773487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51334794102967058651848991 77002191154450587977773487)
  ·
    refine ⟨115503286731675881966660231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77002191154450587977773487 115503286731675881966660231)
    ·
      refine ⟨173254930097513822949990347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115503286731675881966660231 173254930097513822949990347)
      ·
        refine ⟨259882395146270734424985521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173254930097513822949990347 259882395146270734424985521)
        ·
          refine ⟨194911796359703050818739141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259882395146270734424985521 194911796359703050818739141)
          ·
            refine ⟨36545961817444322028513589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194911796359703050818739141 36545961817444322028513589)
            ·
              refine ⟨3426183920385405190173149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36545961817444322028513589 3426183920385405190173149)
              ·
                refine ⟨1284818970144526946314931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3426183920385405190173149 1284818970144526946314931)
                ·
                  refine ⟨1927228455216790419472397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284818970144526946314931 1927228455216790419472397)
                  ·
                    refine ⟨722710670706296407302149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927228455216790419472397 722710670706296407302149)
                    ·
                      rfl

theorem cell22_2111211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 1, 3].length) (baseStart_2111211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111211 prefixEnd_2111211 := by exact prefixLift 2111211
  have htrace : WordTrace (prefixWord ++ tailWord_2111211) baseStart_2111211 baseEnd_2111211 := by
    simpa [prefixWord, tailWord_2111211, baseEnd_2111211] using wordTrace_append hprefix tailTrace_2111211
  have hstable : (prefixWord ++ tailWord_2111211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111211).length < 2 ^ (prefixWord ++ tailWord_2111211).sum := by decide
  have hdescent : baseEnd_2111211 < baseStart_2111211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111228 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_2111228 : Nat := 118140960795 + 2111228 * 2 ^ 59
def prefixEnd_2111228 : Nat := 4983230072969 + 3 ^ 40 * 2111228 * 2
def baseEnd_2111228 : Nat := 722716490153714029627097

theorem tailTrace_2111228 : CollatzResearch.WordTrace tailWord_2111228 prefixEnd_2111228 722716490153714029627097 := by
  unfold tailWord_2111228
  simp only [CollatzResearch.WordTrace]
  refine ⟨38501405597694499940571169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51335207463592666587428225 38501405597694499940571169)
  ·
    refine ⟨28876054198270874955428377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38501405597694499940571169 28876054198270874955428377)
    ·
      refine ⟨21657040648703156216571283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28876054198270874955428377 21657040648703156216571283)
      ·
        refine ⟨32485560973054734324856925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21657040648703156216571283 32485560973054734324856925)
        ·
          refine ⟨12182085364895525371821347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32485560973054734324856925 12182085364895525371821347)
          ·
            refine ⟨18273128047343288057732021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12182085364895525371821347 18273128047343288057732021)
            ·
              refine ⟨1713105754438433255412377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18273128047343288057732021 1713105754438433255412377)
              ·
                refine ⟨1284829315828824941559283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713105754438433255412377 1284829315828824941559283)
                ·
                  refine ⟨1927243973743237412338925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284829315828824941559283 1927243973743237412338925)
                  ·
                    refine ⟨722716490153714029627097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927243973743237412338925 722716490153714029627097)
                    ·
                      rfl

theorem cell22_2111228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_2111228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111228 prefixEnd_2111228 := by exact prefixLift 2111228
  have htrace : WordTrace (prefixWord ++ tailWord_2111228) baseStart_2111228 baseEnd_2111228 := by
    simpa [prefixWord, tailWord_2111228, baseEnd_2111228] using wordTrace_append hprefix tailTrace_2111228
  have hstable : (prefixWord ++ tailWord_2111228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111228).length < 2 ^ (prefixWord ++ tailWord_2111228).sum := by decide
  have hdescent : baseEnd_2111228 < baseStart_2111228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111267 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_2111267 : Nat := 118140960795 + 2111267 * 2 ^ 59
def prefixEnd_2111267 : Nat := 4983230072969 + 3 ^ 40 * 2111267 * 2
def baseEnd_2111267 : Nat := 722729840650730927901977

theorem tailTrace_2111267 : CollatzResearch.WordTrace tailWord_2111267 prefixEnd_2111267 722729840650730927901977 := by
  unfold tailWord_2111267
  simp only [CollatzResearch.WordTrace]
  refine ⟨77004233642247709541812055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51336155761498473027874703 77004233642247709541812055)
  ·
    refine ⟨115506350463371564312718083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77004233642247709541812055 115506350463371564312718083)
    ·
      refine ⟨173259525695057346469077125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115506350463371564312718083 173259525695057346469077125)
      ·
        refine ⟨32486161067823252462951961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173259525695057346469077125 32486161067823252462951961)
        ·
          refine ⟨24364620800867439347213971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32486161067823252462951961 24364620800867439347213971)
          ·
            refine ⟨36546931201301159020820957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24364620800867439347213971 36546931201301159020820957)
            ·
              refine ⟨13705099200487934632807859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36546931201301159020820957 13705099200487934632807859)
              ·
                refine ⟨20557648800731901949211789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13705099200487934632807859 20557648800731901949211789)
                ·
                  refine ⟨7709118300274463230954421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20557648800731901949211789 7709118300274463230954421)
                  ·
                    refine ⟨722729840650730927901977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7709118300274463230954421 722729840650730927901977)
                    ·
                      rfl

theorem cell22_2111267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_2111267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111267 prefixEnd_2111267 := by exact prefixLift 2111267
  have htrace : WordTrace (prefixWord ++ tailWord_2111267) baseStart_2111267 baseEnd_2111267 := by
    simpa [prefixWord, tailWord_2111267, baseEnd_2111267] using wordTrace_append hprefix tailTrace_2111267
  have hstable : (prefixWord ++ tailWord_2111267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111267).length < 2 ^ (prefixWord ++ tailWord_2111267).sum := by decide
  have hdescent : baseEnd_2111267 < baseStart_2111267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111316 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2111316 : Nat := 118140960795 + 2111316 * 2 ^ 59
def prefixEnd_2111316 : Nat := 4983230072969 + 3 ^ 40 * 2111316 * 2
def baseEnd_2111316 : Nat := 722746614352111133426827

theorem tailTrace_2111316 : CollatzResearch.WordTrace tailWord_2111316 prefixEnd_2111316 722746614352111133426827 := by
  unfold tailWord_2111316
  simp only [CollatzResearch.WordTrace]
  refine ⟨38503010409535095455172901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51337347212713460606897201 38503010409535095455172901)
  ·
    refine ⟨7219314451787830397844919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38503010409535095455172901 7219314451787830397844919)
    ·
      refine ⟨10828971677681745596767379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7219314451787830397844919 10828971677681745596767379)
      ·
        refine ⟨16243457516522618395151069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10828971677681745596767379 16243457516522618395151069)
        ·
          refine ⟨6091296568695981898181651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16243457516522618395151069 6091296568695981898181651)
          ·
            refine ⟨9136944853043972847272477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091296568695981898181651 9136944853043972847272477)
            ·
              refine ⟨3426354319891489817727179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9136944853043972847272477 3426354319891489817727179)
              ·
                refine ⟨5139531479837234726590769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426354319891489817727179 5139531479837234726590769)
                ·
                  refine ⟨3854648609877926044943077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5139531479837234726590769 3854648609877926044943077)
                  ·
                    refine ⟨722746614352111133426827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3854648609877926044943077 722746614352111133426827)
                    ·
                      rfl

theorem cell22_2111316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2111316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111316 prefixEnd_2111316 := by exact prefixLift 2111316
  have htrace : WordTrace (prefixWord ++ tailWord_2111316) baseStart_2111316 baseEnd_2111316 := by
    simpa [prefixWord, tailWord_2111316, baseEnd_2111316] using wordTrace_append hprefix tailTrace_2111316
  have hstable : (prefixWord ++ tailWord_2111316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111316).length < 2 ^ (prefixWord ++ tailWord_2111316).sum := by decide
  have hdescent : baseEnd_2111316 < baseStart_2111316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111329 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_2111329 : Nat := 118140960795 + 2111329 * 2 ^ 59
def prefixEnd_2111329 : Nat := 4983230072969 + 3 ^ 40 * 2111329 * 2
def baseEnd_2111329 : Nat := 722751064517783432851787

theorem tailTrace_2111329 : CollatzResearch.WordTrace tailWord_2111329 prefixEnd_2111329 722751064517783432851787 := by
  unfold tailWord_2111329
  simp only [CollatzResearch.WordTrace]
  refine ⟨77006494968023094130569041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51337663312015396087046027 77006494968023094130569041)
  ·
    refine ⟨57754871226017320597926781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77006494968023094130569041 57754871226017320597926781)
    ·
      refine ⟨21658076709756495224222543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57754871226017320597926781 21658076709756495224222543)
      ·
        refine ⟨32487115064634742836333815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21658076709756495224222543 32487115064634742836333815)
        ·
          refine ⟨48730672596952114254500723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32487115064634742836333815 48730672596952114254500723)
          ·
            refine ⟨73096008895428171381751085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48730672596952114254500723 73096008895428171381751085)
            ·
              refine ⟨27411003335785564268156657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73096008895428171381751085 27411003335785564268156657)
              ·
                refine ⟨20558252501839173201117493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27411003335785564268156657 20558252501839173201117493)
                ·
                  refine ⟨1927336172047422487604765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20558252501839173201117493 1927336172047422487604765)
                  ·
                    refine ⟨722751064517783432851787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927336172047422487604765 722751064517783432851787)
                    ·
                      rfl

theorem cell22_2111329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_2111329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111329 prefixEnd_2111329 := by exact prefixLift 2111329
  have htrace : WordTrace (prefixWord ++ tailWord_2111329) baseStart_2111329 baseEnd_2111329 := by
    simpa [prefixWord, tailWord_2111329, baseEnd_2111329] using wordTrace_append hprefix tailTrace_2111329
  have hstable : (prefixWord ++ tailWord_2111329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111329).length < 2 ^ (prefixWord ++ tailWord_2111329).sum := by decide
  have hdescent : baseEnd_2111329 < baseStart_2111329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111380 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2111380 : Nat := 118140960795 + 2111380 * 2 ^ 59
def prefixEnd_2111380 : Nat := 4983230072969 + 3 ^ 40 * 2111380 * 2
def baseEnd_2111380 : Nat := 722768522860036299826631

theorem tailTrace_2111380 : CollatzResearch.WordTrace tailWord_2111380 prefixEnd_2111380 722768522860036299826631 := by
  unfold tailWord_2111380
  simp only [CollatzResearch.WordTrace]
  refine ⟨38504177545419164920337797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51338903393892219893783729 38504177545419164920337797)
  ·
    refine ⟨7219533289766093422563337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38504177545419164920337797 7219533289766093422563337)
    ·
      refine ⟨5414649967324570066922503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7219533289766093422563337 5414649967324570066922503)
      ·
        refine ⟨8121974950986855100383755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5414649967324570066922503 8121974950986855100383755)
        ·
          refine ⟨12182962426480282650575633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8121974950986855100383755 12182962426480282650575633)
          ·
            refine ⟨9137221819860211987931725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12182962426480282650575633 9137221819860211987931725)
            ·
              refine ⟨3426458182447579495474397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9137221819860211987931725 3426458182447579495474397)
              ·
                refine ⟨1284921818417842310802899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3426458182447579495474397 1284921818417842310802899)
                ·
                  refine ⟨1927382727626763466204349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284921818417842310802899 1927382727626763466204349)
                  ·
                    refine ⟨722768522860036299826631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927382727626763466204349 722768522860036299826631)
                    ·
                      rfl

theorem cell22_2111380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2111380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111380 prefixEnd_2111380 := by exact prefixLift 2111380
  have htrace : WordTrace (prefixWord ++ tailWord_2111380) baseStart_2111380 baseEnd_2111380 := by
    simpa [prefixWord, tailWord_2111380, baseEnd_2111380] using wordTrace_append hprefix tailTrace_2111380
  have hstable : (prefixWord ++ tailWord_2111380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111380).length < 2 ^ (prefixWord ++ tailWord_2111380).sum := by decide
  have hdescent : baseEnd_2111380 < baseStart_2111380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111434 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2111434 : Nat := 118140960795 + 2111434 * 2 ^ 59
def prefixEnd_2111434 : Nat := 4983230072969 + 3 ^ 40 * 2111434 * 2
def baseEnd_2111434 : Nat := 722787008163598158976465

theorem tailTrace_2111434 : CollatzResearch.WordTrace tailWord_2111434 prefixEnd_2111434 722787008163598158976465 := by
  unfold tailWord_2111434
  simp only [CollatzResearch.WordTrace]
  refine ⟨19252581158160674265785339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51340216421761798042094237 19252581158160674265785339)
  ·
    refine ⟨28878871737241011398678009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19252581158160674265785339 28878871737241011398678009)
    ·
      refine ⟨21659153802930758549008507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28878871737241011398678009 21659153802930758549008507)
      ·
        refine ⟨32488730704396137823512761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21659153802930758549008507 32488730704396137823512761)
        ·
          refine ⟨24366548028297103367634571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32488730704396137823512761 24366548028297103367634571)
          ·
            refine ⟨36549822042445655051451857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24366548028297103367634571 36549822042445655051451857)
            ·
              refine ⟨27412366531834241288588893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36549822042445655051451857 27412366531834241288588893)
              ·
                refine ⟨10279637449437840483220835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27412366531834241288588893 10279637449437840483220835)
                ·
                  refine ⟨15419456174156760724831253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10279637449437840483220835 15419456174156760724831253)
                  ·
                    refine ⟨722787008163598158976465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15419456174156760724831253 722787008163598158976465)
                    ·
                      rfl

theorem cell22_2111434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2111434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111434 prefixEnd_2111434 := by exact prefixLift 2111434
  have htrace : WordTrace (prefixWord ++ tailWord_2111434) baseStart_2111434 baseEnd_2111434 := by
    simpa [prefixWord, tailWord_2111434, baseEnd_2111434] using wordTrace_append hprefix tailTrace_2111434
  have hstable : (prefixWord ++ tailWord_2111434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111434).length < 2 ^ (prefixWord ++ tailWord_2111434).sum := by decide
  have hdescent : baseEnd_2111434 < baseStart_2111434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111436 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_2111436 : Nat := 118140960795 + 2111436 * 2 ^ 59
def prefixEnd_2111436 : Nat := 4983230072969 + 3 ^ 40 * 2111436 * 2
def baseEnd_2111436 : Nat := 722787692804470820426459

theorem tailTrace_2111436 : CollatzResearch.WordTrace tailWord_2111436 prefixEnd_2111436 722787692804470820426459 := by
  unfold tailWord_2111436
  simp only [CollatzResearch.WordTrace]
  refine ⟨38505198789317725702357081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51340265052423634269809441 38505198789317725702357081)
  ·
    refine ⟨28878899091988294276767811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38505198789317725702357081 28878899091988294276767811)
    ·
      refine ⟨43318348637982441415151717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28878899091988294276767811 43318348637982441415151717)
      ·
        refine ⟨8122190369621707765340947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43318348637982441415151717 8122190369621707765340947)
        ·
          refine ⟨12183285554432561648011421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122190369621707765340947 12183285554432561648011421)
          ·
            refine ⟨4568732082912210618004283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12183285554432561648011421 4568732082912210618004283)
            ·
              refine ⟨6853098124368315927006425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4568732082912210618004283 6853098124368315927006425)
              ·
                refine ⟨5139823593276236945254819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6853098124368315927006425 5139823593276236945254819)
                ·
                  refine ⟨7709735389914355417882229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5139823593276236945254819 7709735389914355417882229)
                  ·
                    refine ⟨722787692804470820426459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7709735389914355417882229 722787692804470820426459)
                    ·
                      rfl

theorem cell22_2111436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_2111436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111436 prefixEnd_2111436 := by exact prefixLift 2111436
  have htrace : WordTrace (prefixWord ++ tailWord_2111436) baseStart_2111436 baseEnd_2111436 := by
    simpa [prefixWord, tailWord_2111436, baseEnd_2111436] using wordTrace_append hprefix tailTrace_2111436
  have hstable : (prefixWord ++ tailWord_2111436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111436).length < 2 ^ (prefixWord ++ tailWord_2111436).sum := by decide
  have hdescent : baseEnd_2111436 < baseStart_2111436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111449 : List Nat := [1, 2, 1, 2, 6, 10]
def baseStart_2111449 : Nat := 118140960795 + 2111449 * 2 ^ 59
def prefixEnd_2111449 : Nat := 4983230072969 + 3 ^ 40 * 2111449 * 2
def baseEnd_2111449 : Nat := 8923359789754853331499

theorem tailTrace_2111449 : CollatzResearch.WordTrace tailWord_2111449 prefixEnd_2111449 8923359789754853331499 := by
  unfold tailWord_2111449
  simp only [CollatzResearch.WordTrace]
  refine ⟨77010871727588354624937401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51340581151725569749958267 77010871727588354624937401)
  ·
    refine ⟨57758153795691265968703051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77010871727588354624937401 57758153795691265968703051)
    ·
      refine ⟨86637230693536898953054577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57758153795691265968703051 86637230693536898953054577)
      ·
        refine ⟨64977923020152674214790933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86637230693536898953054577 64977923020152674214790933)
        ·
          refine ⟨3045840141569656603818325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64977923020152674214790933 3045840141569656603818325)
          ·
            refine ⟨8923359789754853331499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3045840141569656603818325 8923359789754853331499)
            ·
              rfl

theorem cell22_2111449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 10].length) (baseStart_2111449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111449 prefixEnd_2111449 := by exact prefixLift 2111449
  have htrace : WordTrace (prefixWord ++ tailWord_2111449) baseStart_2111449 baseEnd_2111449 := by
    simpa [prefixWord, tailWord_2111449, baseEnd_2111449] using wordTrace_append hprefix tailTrace_2111449
  have hstable : (prefixWord ++ tailWord_2111449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111449).length < 2 ^ (prefixWord ++ tailWord_2111449).sum := by decide
  have hdescent : baseEnd_2111449 < baseStart_2111449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111455 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 4]
def baseStart_2111455 : Nat := 118140960795 + 2111455 * 2 ^ 59
def prefixEnd_2111455 : Nat := 4983230072969 + 3 ^ 40 * 2111455 * 2
def baseEnd_2111455 : Nat := 240931398964253701400467

theorem tailTrace_2111455 : CollatzResearch.WordTrace tailWord_2111455 prefixEnd_2111455 240931398964253701400467 := by
  unfold tailWord_2111455
  simp only [CollatzResearch.WordTrace]
  refine ⟨77011090565566617649655819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51340727043711078433103879 77011090565566617649655819)
  ·
    refine ⟨115516635848349926474483729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77011090565566617649655819 115516635848349926474483729)
    ·
      refine ⟨86637476886262444855862797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115516635848349926474483729 86637476886262444855862797)
      ·
        refine ⟨32489053832348416820948549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86637476886262444855862797 32489053832348416820948549)
        ·
          refine ⟨6091697593565328153927853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32489053832348416820948549 6091697593565328153927853)
          ·
            refine ⟨2284386597586998057722945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6091697593565328153927853 2284386597586998057722945)
            ·
              refine ⟨1713289948190248543292209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284386597586998057722945 1713289948190248543292209)
              ·
                refine ⟨1284967461142686407469157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713289948190248543292209 1284967461142686407469157)
                ·
                  refine ⟨240931398964253701400467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1284967461142686407469157 240931398964253701400467)
                  ·
                    rfl

theorem cell22_2111455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 4].length) (baseStart_2111455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111455 prefixEnd_2111455 := by exact prefixLift 2111455
  have htrace : WordTrace (prefixWord ++ tailWord_2111455) baseStart_2111455 baseEnd_2111455 := by
    simpa [prefixWord, tailWord_2111455, baseEnd_2111455] using wordTrace_append hprefix tailTrace_2111455
  have hstable : (prefixWord ++ tailWord_2111455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111455).length < 2 ^ (prefixWord ++ tailWord_2111455).sum := by decide
  have hdescent : baseEnd_2111455 < baseStart_2111455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111464 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2111464 : Nat := 118140960795 + 2111464 * 2 ^ 59
def prefixEnd_2111464 : Nat := 4983230072969 + 3 ^ 40 * 2111464 * 2
def baseEnd_2111464 : Nat := 722797277776688080726373

theorem tailTrace_2111464 : CollatzResearch.WordTrace tailWord_2111464 prefixEnd_2111464 722797277776688080726373 := by
  unfold tailWord_2111464
  simp only [CollatzResearch.WordTrace]
  refine ⟨38505709411267006093366723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51340945881689341457822297 38505709411267006093366723)
  ·
    refine ⟨57758564116900509140050085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38505709411267006093366723 57758564116900509140050085)
    ·
      refine ⟨10829730771918845463759391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57758564116900509140050085 10829730771918845463759391)
      ·
        refine ⟨16244596157878268195639087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10829730771918845463759391 16244596157878268195639087)
        ·
          refine ⟨24366894236817402293458631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16244596157878268195639087 24366894236817402293458631)
          ·
            refine ⟨36550341355226103440187947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24366894236817402293458631 36550341355226103440187947)
            ·
              refine ⟨54825512032839155160281921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36550341355226103440187947 54825512032839155160281921)
              ·
                refine ⟨41119134024629366370211441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54825512032839155160281921 41119134024629366370211441)
                ·
                  refine ⟨30839350518472024777658581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41119134024629366370211441 30839350518472024777658581)
                  ·
                    refine ⟨722797277776688080726373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30839350518472024777658581 722797277776688080726373)
                    ·
                      rfl

theorem cell22_2111464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2111464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111464 prefixEnd_2111464 := by exact prefixLift 2111464
  have htrace : WordTrace (prefixWord ++ tailWord_2111464) baseStart_2111464 baseEnd_2111464 := by
    simpa [prefixWord, tailWord_2111464, baseEnd_2111464] using wordTrace_append hprefix tailTrace_2111464
  have hstable : (prefixWord ++ tailWord_2111464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111464).length < 2 ^ (prefixWord ++ tailWord_2111464).sum := by decide
  have hdescent : baseEnd_2111464 < baseStart_2111464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111481 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_2111481 : Nat := 118140960795 + 2111481 * 2 ^ 59
def prefixEnd_2111481 : Nat := 4983230072969 + 3 ^ 40 * 2111481 * 2
def baseEnd_2111481 : Nat := 722803097224105703051321

theorem tailTrace_2111481 : CollatzResearch.WordTrace tailWord_2111481 prefixEnd_2111481 722803097224105703051321 := by
  unfold tailWord_2111481
  simp only [CollatzResearch.WordTrace]
  refine ⟨77012038863472424090102297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51341359242314949393401531 77012038863472424090102297)
  ·
    refine ⟨57759029147604318067576723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77012038863472424090102297 57759029147604318067576723)
    ·
      refine ⟨86638543721406477101365085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57759029147604318067576723 86638543721406477101365085)
      ·
        refine ⟨32489453895527428913011907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86638543721406477101365085 32489453895527428913011907)
        ·
          refine ⟨48734180843291143369517861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32489453895527428913011907 48734180843291143369517861)
          ·
            refine ⟨9137658908117089381784599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48734180843291143369517861 9137658908117089381784599)
            ·
              refine ⟨13706488362175634072676899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9137658908117089381784599 13706488362175634072676899)
              ·
                refine ⟨20559732543263451109015349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13706488362175634072676899 20559732543263451109015349)
                ·
                  refine ⟨1927474925930948541470189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20559732543263451109015349 1927474925930948541470189)
                  ·
                    refine ⟨722803097224105703051321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927474925930948541470189 722803097224105703051321)
                    ·
                      rfl

theorem cell22_2111481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_2111481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111481 prefixEnd_2111481 := by exact prefixLift 2111481
  have htrace : WordTrace (prefixWord ++ tailWord_2111481) baseStart_2111481 baseEnd_2111481 := by
    simpa [prefixWord, tailWord_2111481, baseEnd_2111481] using wordTrace_append hprefix tailTrace_2111481
  have hstable : (prefixWord ++ tailWord_2111481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111481).length < 2 ^ (prefixWord ++ tailWord_2111481).sum := by decide
  have hdescent : baseEnd_2111481 < baseStart_2111481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111541 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2111541 : Nat := 118140960795 + 2111541 * 2 ^ 59
def prefixEnd_2111541 : Nat := 4983230072969 + 3 ^ 40 * 2111541 * 2
def baseEnd_2111541 : Nat := 722823636450285546551137

theorem tailTrace_2111541 : CollatzResearch.WordTrace tailWord_2111541 prefixEnd_2111541 722823636450285546551137 := by
  unfold tailWord_2111541
  simp only [CollatzResearch.WordTrace]
  refine ⟨77014227243255054337286477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51342818162170036224857651 77014227243255054337286477)
  ·
    refine ⟨28880335216220645376482429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77014227243255054337286477 28880335216220645376482429)
    ·
      refine ⟨10830125706082742016180911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28880335216220645376482429 10830125706082742016180911)
      ·
        refine ⟨16245188559124113024271367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10830125706082742016180911 16245188559124113024271367)
        ·
          refine ⟨24367782838686169536407051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16245188559124113024271367 24367782838686169536407051)
          ·
            refine ⟨36551674258029254304610577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24367782838686169536407051 36551674258029254304610577)
            ·
              refine ⟨27413755693521940728457933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36551674258029254304610577 27413755693521940728457933)
              ·
                refine ⟨10280158385070727773171725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27413755693521940728457933 10280158385070727773171725)
                ·
                  refine ⟨3855059394401522914939397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10280158385070727773171725 3855059394401522914939397)
                  ·
                    refine ⟨722823636450285546551137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855059394401522914939397 722823636450285546551137)
                    ·
                      rfl

theorem cell22_2111541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2111541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111541 prefixEnd_2111541 := by exact prefixLift 2111541
  have htrace : WordTrace (prefixWord ++ tailWord_2111541) baseStart_2111541 baseEnd_2111541 := by
    simpa [prefixWord, tailWord_2111541, baseEnd_2111541] using wordTrace_append hprefix tailTrace_2111541
  have hstable : (prefixWord ++ tailWord_2111541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111541).length < 2 ^ (prefixWord ++ tailWord_2111541).sum := by decide
  have hdescent : baseEnd_2111541 < baseStart_2111541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111571 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 8, 3]
def baseStart_2111571 : Nat := 118140960795 + 2111571 * 2 ^ 59
def prefixEnd_2111571 : Nat := 4983230072969 + 3 ^ 40 * 2111571 * 2
def baseEnd_2111571 : Nat := 722833906063375468301045

theorem tailTrace_2111571 : CollatzResearch.WordTrace tailWord_2111571 prefixEnd_2111571 722833906063375468301045 := by
  unfold tailWord_2111571
  simp only [CollatzResearch.WordTrace]
  refine ⟨77015321433146369460878567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51343547622097579640585711 77015321433146369460878567)
  ·
    refine ⟨115522982149719554191317851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77015321433146369460878567 115522982149719554191317851)
    ·
      refine ⟨173284473224579331286976777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115522982149719554191317851 173284473224579331286976777)
      ·
        refine ⟨129963354918434498465232583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173284473224579331286976777 129963354918434498465232583)
        ·
          refine ⟨194945032377651747697848875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129963354918434498465232583 194945032377651747697848875)
          ·
            refine ⟨292417548566477621546773313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194945032377651747697848875 292417548566477621546773313)
            ·
              refine ⟨219313161424858216160079985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292417548566477621546773313 219313161424858216160079985)
              ·
                refine ⟨164484871068643662120059989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219313161424858216160079985 164484871068643662120059989)
                ·
                  refine ⟨1927557082835667915469453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 164484871068643662120059989 1927557082835667915469453)
                  ·
                    refine ⟨722833906063375468301045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927557082835667915469453 722833906063375468301045)
                    ·
                      rfl

theorem cell22_2111571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 8, 3].length) (baseStart_2111571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111571 prefixEnd_2111571 := by exact prefixLift 2111571
  have htrace : WordTrace (prefixWord ++ tailWord_2111571) baseStart_2111571 baseEnd_2111571 := by
    simpa [prefixWord, tailWord_2111571, baseEnd_2111571] using wordTrace_append hprefix tailTrace_2111571
  have hstable : (prefixWord ++ tailWord_2111571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111571).length < 2 ^ (prefixWord ++ tailWord_2111571).sum := by decide
  have hdescent : baseEnd_2111571 < baseStart_2111571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111573 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 6]
def baseStart_2111573 : Nat := 118140960795 + 2111573 * 2 ^ 59
def prefixEnd_2111573 : Nat := 4983230072969 + 3 ^ 40 * 2111573 * 2
def baseEnd_2111573 : Nat := 240944863568082709917013

theorem tailTrace_2111573 : CollatzResearch.WordTrace tailWord_2111573 prefixEnd_2111573 240944863568082709917013 := by
  unfold tailWord_2111573
  simp only [CollatzResearch.WordTrace]
  refine ⟨77015394379139123802451373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51343596252759415868300915 77015394379139123802451373)
  ·
    refine ⟨28880772892177171425919265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77015394379139123802451373 28880772892177171425919265)
    ·
      refine ⟨21660579669132878569439449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28880772892177171425919265 21660579669132878569439449)
      ·
        refine ⟨16245434751849658927079587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21660579669132878569439449 16245434751849658927079587)
        ·
          refine ⟨24368152127774488390619381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16245434751849658927079587 24368152127774488390619381)
          ·
            refine ⟨2284514261978858286620567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24368152127774488390619381 2284514261978858286620567)
            ·
              refine ⟨3426771392968287429930851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284514261978858286620567 3426771392968287429930851)
              ·
                refine ⟨5140157089452431144896277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3426771392968287429930851 5140157089452431144896277)
                ·
                  refine ⟨240944863568082709917013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5140157089452431144896277 240944863568082709917013)
                  ·
                    rfl

theorem cell22_2111573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_2111573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111573 prefixEnd_2111573 := by exact prefixLift 2111573
  have htrace : WordTrace (prefixWord ++ tailWord_2111573) baseStart_2111573 baseEnd_2111573 := by
    simpa [prefixWord, tailWord_2111573, baseEnd_2111573] using wordTrace_append hprefix tailTrace_2111573
  have hstable : (prefixWord ++ tailWord_2111573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111573).length < 2 ^ (prefixWord ++ tailWord_2111573).sum := by decide
  have hdescent : baseEnd_2111573 < baseStart_2111573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111650 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2111650 : Nat := 118140960795 + 2111650 * 2 ^ 59
def prefixEnd_2111650 : Nat := 4983230072969 + 3 ^ 40 * 2111650 * 2
def baseEnd_2111650 : Nat := 722860949377845595575803

theorem tailTrace_2111650 : CollatzResearch.WordTrace tailWord_2111650 prefixEnd_2111650 722860949377845595575803 := by
  unfold tailWord_2111650
  simp only [CollatzResearch.WordTrace]
  refine ⟨19254550699965041488251101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51345468533240110635336269 19254550699965041488251101)
  ·
    refine ⟨7220456512486890558094163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19254550699965041488251101 7220456512486890558094163)
    ·
      refine ⟨10830684768730335837141245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7220456512486890558094163 10830684768730335837141245)
      ·
        refine ⟨4061506788273875938927967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10830684768730335837141245 4061506788273875938927967)
        ·
          refine ⟨6092260182410813908391951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4061506788273875938927967 6092260182410813908391951)
          ·
            refine ⟨9138390273616220862587927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092260182410813908391951 9138390273616220862587927)
            ·
              refine ⟨13707585410424331293881891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138390273616220862587927 13707585410424331293881891)
              ·
                refine ⟨20561378115636496940822837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13707585410424331293881891 20561378115636496940822837)
                ·
                  refine ⟨1927629198340921588202141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20561378115636496940822837 1927629198340921588202141)
                  ·
                    refine ⟨722860949377845595575803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927629198340921588202141 722860949377845595575803)
                    ·
                      rfl

theorem cell22_2111650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2111650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111650 prefixEnd_2111650 := by exact prefixLift 2111650
  have htrace : WordTrace (prefixWord ++ tailWord_2111650) baseStart_2111650 baseEnd_2111650 := by
    simpa [prefixWord, tailWord_2111650, baseEnd_2111650] using wordTrace_append hprefix tailTrace_2111650
  have hstable : (prefixWord ++ tailWord_2111650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111650).length < 2 ^ (prefixWord ++ tailWord_2111650).sum := by decide
  have hdescent : baseEnd_2111650 < baseStart_2111650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111680 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_2111680 : Nat := 118140960795 + 2111680 * 2 ^ 59
def prefixEnd_2111680 : Nat := 4983230072969 + 3 ^ 40 * 2111680 * 2
def baseEnd_2111680 : Nat := 240957072996978505775237

theorem tailTrace_2111680 : CollatzResearch.WordTrace tailWord_2111680 prefixEnd_2111680 240957072996978505775237 := by
  unfold tailWord_2111680
  simp only [CollatzResearch.WordTrace]
  refine ⟨38509648494875740538298247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51346197993167654051064329 38509648494875740538298247)
  ·
    refine ⟨57764472742313610807447371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38509648494875740538298247 57764472742313610807447371)
    ·
      refine ⟨86646709113470416211171057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57764472742313610807447371 86646709113470416211171057)
      ·
        refine ⟨64985031835102812158378293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86646709113470416211171057 64985031835102812158378293)
        ·
          refine ⟨6092346734540888639847965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64985031835102812158378293 6092346734540888639847965)
          ·
            refine ⟨2284630025452833239942987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6092346734540888639847965 2284630025452833239942987)
            ·
              refine ⟨3426945038179249859914481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2284630025452833239942987 3426945038179249859914481)
              ·
                refine ⟨2570208778634437394935861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426945038179249859914481 2570208778634437394935861)
                ·
                  refine ⟨240957072996978505775237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2570208778634437394935861 240957072996978505775237)
                  ·
                    rfl

theorem cell22_2111680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_2111680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111680 prefixEnd_2111680 := by exact prefixLift 2111680
  have htrace : WordTrace (prefixWord ++ tailWord_2111680) baseStart_2111680 baseEnd_2111680 := by
    simpa [prefixWord, tailWord_2111680, baseEnd_2111680] using wordTrace_append hprefix tailTrace_2111680
  have hstable : (prefixWord ++ tailWord_2111680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111680).length < 2 ^ (prefixWord ++ tailWord_2111680).sum := by decide
  have hdescent : baseEnd_2111680 < baseStart_2111680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111723 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 6, 3]
def baseStart_2111723 : Nat := 118140960795 + 2111723 * 2 ^ 59
def prefixEnd_2111723 : Nat := 4983230072969 + 3 ^ 40 * 2111723 * 2
def baseEnd_2111723 : Nat := 722885938769697738500579

theorem tailTrace_2111723 : CollatzResearch.WordTrace tailWord_2111723 prefixEnd_2111723 722885938769697738500579 := by
  unfold tailWord_2111723
  simp only [CollatzResearch.WordTrace]
  refine ⟨77020865328595699420411823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51347243552397132946941215 77020865328595699420411823)
  ·
    refine ⟨115531297992893549130617735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77020865328595699420411823 115531297992893549130617735)
    ·
      refine ⟨173296946989340323695926603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115531297992893549130617735 173296946989340323695926603)
      ·
        refine ⟨259945420484010485543889905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173296946989340323695926603 259945420484010485543889905)
        ·
          refine ⟨194959065363007864157917429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259945420484010485543889905 194959065363007864157917429)
          ·
            refine ⟨18277412377781987264804759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194959065363007864157917429 18277412377781987264804759)
            ·
              refine ⟨27416118566672980897207139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18277412377781987264804759 27416118566672980897207139)
              ·
                refine ⟨41124177850009471345810709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27416118566672980897207139 41124177850009471345810709)
                ·
                  refine ⟨1927695836719193969334877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41124177850009471345810709 1927695836719193969334877)
                  ·
                    refine ⟨722885938769697738500579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927695836719193969334877 722885938769697738500579)
                    ·
                      rfl

theorem cell22_2111723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 3].length) (baseStart_2111723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111723 prefixEnd_2111723 := by exact prefixLift 2111723
  have htrace : WordTrace (prefixWord ++ tailWord_2111723) baseStart_2111723 baseEnd_2111723 := by
    simpa [prefixWord, tailWord_2111723, baseEnd_2111723] using wordTrace_append hprefix tailTrace_2111723
  have hstable : (prefixWord ++ tailWord_2111723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111723).length < 2 ^ (prefixWord ++ tailWord_2111723).sum := by decide
  have hdescent : baseEnd_2111723 < baseStart_2111723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111738 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_2111738 : Nat := 118140960795 + 2111738 * 2 ^ 59
def prefixEnd_2111738 : Nat := 4983230072969 + 3 ^ 40 * 2111738 * 2
def baseEnd_2111738 : Nat := 722891073576242699375533

theorem tailTrace_2111738 : CollatzResearch.WordTrace tailWord_2111738 prefixEnd_2111738 722891073576242699375533 := by
  unfold tailWord_2111738
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255353105885339245551967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51347608282360904654805245 19255353105885339245551967)
  ·
    refine ⟨28883029658828008868327951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19255353105885339245551967 28883029658828008868327951)
    ·
      refine ⟨43324544488242013302491927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28883029658828008868327951 43324544488242013302491927)
      ·
        refine ⟨64986816732363019953737891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43324544488242013302491927 64986816732363019953737891)
        ·
          refine ⟨97480225098544529930606837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64986816732363019953737891 97480225098544529930606837)
          ·
            refine ⟨9138771102988549680994391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97480225098544529930606837 9138771102988549680994391)
            ·
              refine ⟨13708156654482824521491587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9138771102988549680994391 13708156654482824521491587)
              ·
                refine ⟨20562234981724236782237381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13708156654482824521491587 20562234981724236782237381)
                ·
                  refine ⟨3855419059073294396669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20562234981724236782237381 3855419059073294396669509)
                  ·
                    refine ⟨722891073576242699375533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855419059073294396669509 722891073576242699375533)
                    ·
                      rfl

theorem cell22_2111738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_2111738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111738 prefixEnd_2111738 := by exact prefixLift 2111738
  have htrace : WordTrace (prefixWord ++ tailWord_2111738) baseStart_2111738 baseEnd_2111738 := by
    simpa [prefixWord, tailWord_2111738, baseEnd_2111738] using wordTrace_append hprefix tailTrace_2111738
  have hstable : (prefixWord ++ tailWord_2111738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111738).length < 2 ^ (prefixWord ++ tailWord_2111738).sum := by decide
  have hdescent : baseEnd_2111738 < baseStart_2111738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111740 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2111740 : Nat := 118140960795 + 2111740 * 2 ^ 59
def prefixEnd_2111740 : Nat := 4983230072969 + 3 ^ 40 * 2111740 * 2
def baseEnd_2111740 : Nat := 722891758217115360825527

theorem tailTrace_2111740 : CollatzResearch.WordTrace tailWord_2111740 prefixEnd_2111740 722891758217115360825527 := by
  unfold tailWord_2111740
  simp only [CollatzResearch.WordTrace]
  refine ⟨38510742684767055661890337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51347656913022740882520449 38510742684767055661890337)
  ·
    refine ⟨28883057013575291746417753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38510742684767055661890337 28883057013575291746417753)
    ·
      refine ⟨21662292760181468809813315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28883057013575291746417753 21662292760181468809813315)
      ·
        refine ⟨32493439140272203214719973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21662292760181468809813315 32493439140272203214719973)
        ·
          refine ⟨6092519838801038102759995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32493439140272203214719973 6092519838801038102759995)
          ·
            refine ⟨9138779758201557154139993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6092519838801038102759995 9138779758201557154139993)
            ·
              refine ⟨6854084818651167865604995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9138779758201557154139993 6854084818651167865604995)
              ·
                refine ⟨10281127227976751798407493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6854084818651167865604995 10281127227976751798407493)
                ·
                  refine ⟨1927711355245640962201405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10281127227976751798407493 1927711355245640962201405)
                  ·
                    refine ⟨722891758217115360825527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927711355245640962201405 722891758217115360825527)
                    ·
                      rfl

theorem cell22_2111740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2111740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111740 prefixEnd_2111740 := by exact prefixLift 2111740
  have htrace : WordTrace (prefixWord ++ tailWord_2111740) baseStart_2111740 baseEnd_2111740 := by
    simpa [prefixWord, tailWord_2111740, baseEnd_2111740] using wordTrace_append hprefix tailTrace_2111740
  have hstable : (prefixWord ++ tailWord_2111740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111740).length < 2 ^ (prefixWord ++ tailWord_2111740).sum := by decide
  have hdescent : baseEnd_2111740 < baseStart_2111740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111753 : List Nat := [1, 2, 1, 1, 3, 5, 2, 7]
def baseStart_2111753 : Nat := 118140960795 + 2111753 * 2 ^ 59
def prefixEnd_2111753 : Nat := 4983230072969 + 3 ^ 40 * 2111753 * 2
def baseEnd_2111753 : Nat := 80321800931420851138943

theorem tailTrace_2111753 : CollatzResearch.WordTrace tailWord_2111753 prefixEnd_2111753 80321800931420851138943 := by
  unfold tailWord_2111753
  simp only [CollatzResearch.WordTrace]
  refine ⟨77021959518487014544003913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51347973012324676362669275 77021959518487014544003913)
  ·
    refine ⟨57766469638865260908002935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77021959518487014544003913 57766469638865260908002935)
    ·
      refine ⟨86649704458297891362004403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57766469638865260908002935 86649704458297891362004403)
      ·
        refine ⟨129974556687446837043006605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86649704458297891362004403 129974556687446837043006605)
        ·
          refine ⟨48740458757792563891127477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129974556687446837043006605 48740458757792563891127477)
          ·
            refine ⟨4569418008543052864793201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48740458757792563891127477 4569418008543052864793201)
            ·
              refine ⟨3427063506407289648594901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569418008543052864793201 3427063506407289648594901)
              ·
                refine ⟨80321800931420851138943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3427063506407289648594901 80321800931420851138943)
                ·
                  rfl

theorem cell22_2111753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 7].length) (baseStart_2111753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111753 prefixEnd_2111753 := by exact prefixLift 2111753
  have htrace : WordTrace (prefixWord ++ tailWord_2111753) baseStart_2111753 baseEnd_2111753 := by
    simpa [prefixWord, tailWord_2111753, baseEnd_2111753] using wordTrace_append hprefix tailTrace_2111753
  have hstable : (prefixWord ++ tailWord_2111753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111753).length < 2 ^ (prefixWord ++ tailWord_2111753).sum := by decide
  have hdescent : baseEnd_2111753 < baseStart_2111753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111843 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 8]
def baseStart_2111843 : Nat := 118140960795 + 2111843 * 2 ^ 59
def prefixEnd_2111843 : Nat := 4983230072969 + 3 ^ 40 * 2111843 * 2
def baseEnd_2111843 : Nat := 240975672407352475166737

theorem tailTrace_2111843 : CollatzResearch.WordTrace tailWord_2111843 prefixEnd_2111843 240975672407352475166737 := by
  unfold tailWord_2111843
  simp only [CollatzResearch.WordTrace]
  refine ⟨77025242088160959914780183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51350161392107306609853455 77025242088160959914780183)
  ·
    refine ⟨115537863132241439872170275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77025242088160959914780183 115537863132241439872170275)
    ·
      refine ⟨173306794698362159808255413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115537863132241439872170275 173306794698362159808255413)
      ·
        refine ⟨16247512002971452482023945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173306794698362159808255413 16247512002971452482023945)
        ·
          refine ⟨12185634002228589361517959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16247512002971452482023945 12185634002228589361517959)
          ·
            refine ⟨18278451003342884042276939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12185634002228589361517959 18278451003342884042276939)
            ·
              refine ⟨27417676505014326063415409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18278451003342884042276939 27417676505014326063415409)
              ·
                refine ⟨20563257378760744547561557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27417676505014326063415409 20563257378760744547561557)
                ·
                  refine ⟨240975672407352475166737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20563257378760744547561557 240975672407352475166737)
                  ·
                    rfl

theorem cell22_2111843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_2111843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111843 prefixEnd_2111843 := by exact prefixLift 2111843
  have htrace : WordTrace (prefixWord ++ tailWord_2111843) baseStart_2111843 baseEnd_2111843 := by
    simpa [prefixWord, tailWord_2111843, baseEnd_2111843] using wordTrace_append hprefix tailTrace_2111843
  have hstable : (prefixWord ++ tailWord_2111843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111843).length < 2 ^ (prefixWord ++ tailWord_2111843).sum := by decide
  have hdescent : baseEnd_2111843 < baseStart_2111843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111967 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 5]
def baseStart_2111967 : Nat := 118140960795 + 2111967 * 2 ^ 59
def prefixEnd_2111967 : Nat := 4983230072969 + 3 ^ 40 * 2111967 * 2
def baseEnd_2111967 : Nat := 240989821652054145133277

theorem tailTrace_2111967 : CollatzResearch.WordTrace tailWord_2111967 prefixEnd_2111967 240989821652054145133277 := by
  unfold tailWord_2111967
  simp only [CollatzResearch.WordTrace]
  refine ⟨77029764739711729092294155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51353176493141152728196103 77029764739711729092294155)
  ·
    refine ⟨115544647109567593638441233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77029764739711729092294155 115544647109567593638441233)
    ·
      refine ⟨86658485332175695228830925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115544647109567593638441233 86658485332175695228830925)
      ·
        refine ⟨32496931999565885710811597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86658485332175695228830925 32496931999565885710811597)
        ·
          refine ⟨12186349499837207141554349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32496931999565885710811597 12186349499837207141554349)
          ·
            refine ⟨4569881062438952678082881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12186349499837207141554349 4569881062438952678082881)
            ·
              refine ⟨3427410796829214508562161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4569881062438952678082881 3427410796829214508562161)
              ·
                refine ⟨2570558097621910881421621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3427410796829214508562161 2570558097621910881421621)
                ·
                  refine ⟨240989821652054145133277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2570558097621910881421621 240989821652054145133277)
                  ·
                    rfl

theorem cell22_2111967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 5].length) (baseStart_2111967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111967 prefixEnd_2111967 := by exact prefixLift 2111967
  have htrace : WordTrace (prefixWord ++ tailWord_2111967) baseStart_2111967 baseEnd_2111967 := by
    simpa [prefixWord, tailWord_2111967, baseEnd_2111967] using wordTrace_append hprefix tailTrace_2111967
  have hstable : (prefixWord ++ tailWord_2111967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111967).length < 2 ^ (prefixWord ++ tailWord_2111967).sum := by decide
  have hdescent : baseEnd_2111967 < baseStart_2111967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111971 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 1, 3]
def baseStart_2111971 : Nat := 118140960795 + 2111971 * 2 ^ 59
def prefixEnd_2111971 : Nat := 4983230072969 + 3 ^ 40 * 2111971 * 2
def baseEnd_2111971 : Nat := 722970834237907758299819

theorem tailTrace_2111971 : CollatzResearch.WordTrace tailWord_2111971 prefixEnd_2111971 722970834237907758299819 := by
  unfold tailWord_2111971
  simp only [CollatzResearch.WordTrace]
  refine ⟨77029910631697237775439767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51353273754464825183626511 77029910631697237775439767)
  ·
    refine ⟨115544865947545856663159651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77029910631697237775439767 115544865947545856663159651)
    ·
      refine ⟨173317298921318784994739477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115544865947545856663159651 173317298921318784994739477)
      ·
        refine ⟨8124248386936818046628413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 173317298921318784994739477 8124248386936818046628413)
        ·
          refine ⟨3046593145101306767485655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8124248386936818046628413 3046593145101306767485655)
          ·
            refine ⟨4569889717651960151228483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046593145101306767485655 4569889717651960151228483)
            ·
              refine ⟨6854834576477940226842725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569889717651960151228483 6854834576477940226842725)
              ·
                refine ⟨1285281483089613792533011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6854834576477940226842725 1285281483089613792533011)
                ·
                  refine ⟨1927922224634420688799517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285281483089613792533011 1927922224634420688799517)
                  ·
                    refine ⟨722970834237907758299819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1927922224634420688799517 722970834237907758299819)
                    ·
                      rfl

theorem cell22_2111971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 3].length) (baseStart_2111971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111971 prefixEnd_2111971 := by exact prefixLift 2111971
  have htrace : WordTrace (prefixWord ++ tailWord_2111971) baseStart_2111971 baseEnd_2111971 := by
    simpa [prefixWord, tailWord_2111971, baseEnd_2111971] using wordTrace_append hprefix tailTrace_2111971
  have hstable : (prefixWord ++ tailWord_2111971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111971).length < 2 ^ (prefixWord ++ tailWord_2111971).sum := by decide
  have hdescent : baseEnd_2111971 < baseStart_2111971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111980 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_2111980 : Nat := 118140960795 + 2111980 * 2 ^ 59
def prefixEnd_2111980 : Nat := 4983230072969 + 3 ^ 40 * 2111980 * 2
def baseEnd_2111980 : Nat := 722973915121834734824791

theorem tailTrace_2111980 : CollatzResearch.WordTrace tailWord_2111980 prefixEnd_2111980 722973915121834734824791 := by
  unfold tailWord_2111980
  simp only [CollatzResearch.WordTrace]
  refine ⟨38515119444332316156258697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51353492592443088208344929 38515119444332316156258697)
  ·
    refine ⟨28886339583249237117194023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38515119444332316156258697 28886339583249237117194023)
    ·
      refine ⟨43329509374873855675791035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28886339583249237117194023 43329509374873855675791035)
      ·
        refine ⟨64994264062310783513686553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43329509374873855675791035 64994264062310783513686553)
        ·
          refine ⟨48745698046733087635264915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64994264062310783513686553 48745698046733087635264915)
          ·
            refine ⟨73118547070099631452897373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48745698046733087635264915 73118547070099631452897373)
            ·
              refine ⟨27419455151287361794836515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73118547070099631452897373 27419455151287361794836515)
              ·
                refine ⟨41129182726931042692254773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27419455151287361794836515 41129182726931042692254773)
                ·
                  refine ⟨3855860880649785252398885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41129182726931042692254773 3855860880649785252398885)
                  ·
                    refine ⟨722973915121834734824791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855860880649785252398885 722973915121834734824791)
                    ·
                      rfl

theorem cell22_2111980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_2111980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111980 prefixEnd_2111980 := by exact prefixLift 2111980
  have htrace : WordTrace (prefixWord ++ tailWord_2111980) baseStart_2111980 baseEnd_2111980 := by
    simpa [prefixWord, tailWord_2111980, baseEnd_2111980] using wordTrace_append hprefix tailTrace_2111980
  have hstable : (prefixWord ++ tailWord_2111980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111980).length < 2 ^ (prefixWord ++ tailWord_2111980).sum := by decide
  have hdescent : baseEnd_2111980 < baseStart_2111980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111982 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2111982 : Nat := 118140960795 + 2111982 * 2 ^ 59
def prefixEnd_2111982 : Nat := 4983230072969 + 3 ^ 40 * 2111982 * 2
def baseEnd_2111982 : Nat := 722974599762707396274785

theorem tailTrace_2111982 : CollatzResearch.WordTrace tailWord_2111982 prefixEnd_2111982 722974599762707396274785 := by
  unfold tailWord_2111982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628788979332173331761275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51353541223104924436060133 9628788979332173331761275)
  ·
    refine ⟨14443183468998259997641913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9628788979332173331761275 14443183468998259997641913)
    ·
      refine ⟨10832387601748694998231435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14443183468998259997641913 10832387601748694998231435)
      ·
        refine ⟨16248581402623042497347153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10832387601748694998231435 16248581402623042497347153)
        ·
          refine ⟨12186436051967281873010365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16248581402623042497347153 12186436051967281873010365)
          ·
            refine ⟨4569913519487730702378887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12186436051967281873010365 4569913519487730702378887)
            ·
              refine ⟨6854870279231596053568331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569913519487730702378887 6854870279231596053568331)
              ·
                refine ⟨10282305418847394080352497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6854870279231596053568331 10282305418847394080352497)
                ·
                  refine ⟨7711729064135545560264373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10282305418847394080352497 7711729064135545560264373)
                  ·
                    refine ⟨722974599762707396274785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7711729064135545560264373 722974599762707396274785)
                    ·
                      rfl

theorem cell22_2111982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2111982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111982 prefixEnd_2111982 := by exact prefixLift 2111982
  have htrace : WordTrace (prefixWord ++ tailWord_2111982) baseStart_2111982 baseEnd_2111982 := by
    simpa [prefixWord, tailWord_2111982, baseEnd_2111982] using wordTrace_append hprefix tailTrace_2111982
  have hstable : (prefixWord ++ tailWord_2111982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111982).length < 2 ^ (prefixWord ++ tailWord_2111982).sum := by decide
  have hdescent : baseEnd_2111982 < baseStart_2111982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2111997 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2111997 : Nat := 118140960795 + 2111997 * 2 ^ 59
def prefixEnd_2111997 : Nat := 4983230072969 + 3 ^ 40 * 2111997 * 2
def baseEnd_2111997 : Nat := 722979734569252357149739

theorem tailTrace_2111997 : CollatzResearch.WordTrace tailWord_2111997 prefixEnd_2111997 722979734569252357149739 := by
  unfold tailWord_2111997
  simp only [CollatzResearch.WordTrace]
  refine ⟨77030858929603044215886245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51353905953068696143924163 77030858929603044215886245)
  ·
    refine ⟨14443286049300570790478671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77030858929603044215886245 14443286049300570790478671)
    ·
      refine ⟨21664929073950856185718007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14443286049300570790478671 21664929073950856185718007)
      ·
        refine ⟨32497393610926284278577011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21664929073950856185718007 32497393610926284278577011)
        ·
          refine ⟨48746090416389426417865517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32497393610926284278577011 48746090416389426417865517)
          ·
            refine ⟨18279783906146034906699569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48746090416389426417865517 18279783906146034906699569)
            ·
              refine ⟨13709837929609526180024677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18279783906146034906699569 13709837929609526180024677)
              ·
                refine ⟨2570594611801786158754627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13709837929609526180024677 2570594611801786158754627)
                ·
                  refine ⟨3855891917702679238131941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570594611801786158754627 3855891917702679238131941)
                  ·
                    refine ⟨722979734569252357149739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855891917702679238131941 722979734569252357149739)
                    ·
                      rfl

theorem cell22_2111997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2111997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2111997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2111997 prefixEnd_2111997 := by exact prefixLift 2111997
  have htrace : WordTrace (prefixWord ++ tailWord_2111997) baseStart_2111997 baseEnd_2111997 := by
    simpa [prefixWord, tailWord_2111997, baseEnd_2111997] using wordTrace_append hprefix tailTrace_2111997
  have hstable : (prefixWord ++ tailWord_2111997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2111997).length < 2 ^ (prefixWord ++ tailWord_2111997).sum := by decide
  have hdescent : baseEnd_2111997 < baseStart_2111997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2111997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112014 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2112014 : Nat := 118140960795 + 2112014 * 2 ^ 59
def prefixEnd_2112014 : Nat := 4983230072969 + 3 ^ 40 * 2112014 * 2
def baseEnd_2112014 : Nat := 722985554016669979474687

theorem tailTrace_2112014 : CollatzResearch.WordTrace tailWord_2112014 prefixEnd_2112014 722985554016669979474687 := by
  unfold tailWord_2112014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628934871317682014906887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51354319313694304079503397 9628934871317682014906887)
  ·
    refine ⟨14443402306976523022360331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9628934871317682014906887 14443402306976523022360331)
    ·
      refine ⟨21665103460464784533540497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14443402306976523022360331 21665103460464784533540497)
      ·
        refine ⟨16248827595348588400155373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21665103460464784533540497 16248827595348588400155373)
        ·
          refine ⟨6093310348255720650058265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16248827595348588400155373 6093310348255720650058265)
          ·
            refine ⟨4569982761191790487543699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6093310348255720650058265 4569982761191790487543699)
            ·
              refine ⟨6854974141787685731315549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4569982761191790487543699 6854974141787685731315549)
              ·
                refine ⟨2570615303170382149243331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6854974141787685731315549 2570615303170382149243331)
                ·
                  refine ⟨3855922954755573223864997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570615303170382149243331 3855922954755573223864997)
                  ·
                    refine ⟨722985554016669979474687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3855922954755573223864997 722985554016669979474687)
                    ·
                      rfl

theorem cell22_2112014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2112014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112014 prefixEnd_2112014 := by exact prefixLift 2112014
  have htrace : WordTrace (prefixWord ++ tailWord_2112014) baseStart_2112014 baseEnd_2112014 := by
    simpa [prefixWord, tailWord_2112014, baseEnd_2112014] using wordTrace_append hprefix tailTrace_2112014
  have hstable : (prefixWord ++ tailWord_2112014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112014).length < 2 ^ (prefixWord ++ tailWord_2112014).sum := by decide
  have hdescent : baseEnd_2112014 < baseStart_2112014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112029 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 4]
def baseStart_2112029 : Nat := 118140960795 + 2112029 * 2 ^ 59
def prefixEnd_2112029 : Nat := 4983230072969 + 3 ^ 40 * 2112029 * 2
def baseEnd_2112029 : Nat := 240996896274404980116547

theorem tailTrace_2112029 : CollatzResearch.WordTrace tailWord_2112029 prefixEnd_2112029 240996896274404980116547 := by
  unfold tailWord_2112029
  simp only [CollatzResearch.WordTrace]
  refine ⟨77032026065487113681051141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51354684043658075787367427 77032026065487113681051141)
  ·
    refine ⟨14443504887278833815197089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77032026065487113681051141 14443504887278833815197089)
    ·
      refine ⟨10832628665459125361397817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14443504887278833815197089 10832628665459125361397817)
      ·
        refine ⟨8124471499094344021048363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10832628665459125361397817 8124471499094344021048363)
        ·
          refine ⟨12186707248641516031572545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8124471499094344021048363 12186707248641516031572545)
          ·
            refine ⟨9140030436481137023679409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12186707248641516031572545 9140030436481137023679409)
            ·
              refine ⟨6855022827360852767759557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9140030436481137023679409 6855022827360852767759557)
              ·
                refine ⟨1285316780130159893954917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6855022827360852767759557 1285316780130159893954917)
                ·
                  refine ⟨240996896274404980116547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285316780130159893954917 240996896274404980116547)
                  ·
                    rfl

theorem cell22_2112029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_2112029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112029 prefixEnd_2112029 := by exact prefixLift 2112029
  have htrace : WordTrace (prefixWord ++ tailWord_2112029) baseStart_2112029 baseEnd_2112029 := by
    simpa [prefixWord, tailWord_2112029, baseEnd_2112029] using wordTrace_append hprefix tailTrace_2112029
  have hstable : (prefixWord ++ tailWord_2112029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112029).length < 2 ^ (prefixWord ++ tailWord_2112029).sum := by decide
  have hdescent : baseEnd_2112029 < baseStart_2112029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112042 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2112042 : Nat := 118140960795 + 2112042 * 2 ^ 59
def prefixEnd_2112042 : Nat := 4983230072969 + 3 ^ 40 * 2112042 * 2
def baseEnd_2112042 : Nat := 722995138988887239774601

theorem tailTrace_2112042 : CollatzResearch.WordTrace tailWord_2112042 prefixEnd_2112042 722995138988887239774601 := by
  unfold tailWord_2112042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19258125053610004225318595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51355000142960011267516253 19258125053610004225318595)
  ·
    refine ⟨28887187580415006337977893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19258125053610004225318595 28887187580415006337977893)
    ·
      refine ⟨5416347671327813688370855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28887187580415006337977893 5416347671327813688370855)
      ·
        refine ⟨8124521506991720532556283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416347671327813688370855 8124521506991720532556283)
        ·
          refine ⟨12186782260487580798834425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8124521506991720532556283 12186782260487580798834425)
          ·
            refine ⟨9140086695365685599125819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12186782260487580798834425 9140086695365685599125819)
            ·
              refine ⟨13710130043048528398688729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9140086695365685599125819 13710130043048528398688729)
              ·
                refine ⟨10282597532286396299016547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13710130043048528398688729 10282597532286396299016547)
                ·
                  refine ⟨15423896298429594448524821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10282597532286396299016547 15423896298429594448524821)
                  ·
                    refine ⟨722995138988887239774601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15423896298429594448524821 722995138988887239774601)
                    ·
                      rfl

theorem cell22_2112042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2112042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112042 prefixEnd_2112042 := by exact prefixLift 2112042
  have htrace : WordTrace (prefixWord ++ tailWord_2112042) baseStart_2112042 baseEnd_2112042 := by
    simpa [prefixWord, tailWord_2112042, baseEnd_2112042] using wordTrace_append hprefix tailTrace_2112042
  have hstable : (prefixWord ++ tailWord_2112042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112042).length < 2 ^ (prefixWord ++ tailWord_2112042).sum := by decide
  have hdescent : baseEnd_2112042 < baseStart_2112042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112055 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2112055 : Nat := 118140960795 + 2112055 * 2 ^ 59
def prefixEnd_2112055 : Nat := 4983230072969 + 3 ^ 40 * 2112055 * 2
def baseEnd_2112055 : Nat := 722999589154559539199561

theorem tailTrace_2112055 : CollatzResearch.WordTrace tailWord_2112055 prefixEnd_2112055 722999589154559539199561 := by
  unfold tailWord_2112055
  simp only [CollatzResearch.WordTrace]
  refine ⟨77032974363392920121497619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51355316242261946747665079 77032974363392920121497619)
  ·
    refine ⟨115549461545089380182246429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77032974363392920121497619 115549461545089380182246429)
    ·
      refine ⟨43331048079408517568342411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115549461545089380182246429 43331048079408517568342411)
      ·
        refine ⟨64996572119112776352513617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43331048079408517568342411 64996572119112776352513617)
        ·
          refine ⟨48747429089334582264385213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64996572119112776352513617 48747429089334582264385213)
          ·
            refine ⟨18280285908500468349144455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48747429089334582264385213 18280285908500468349144455)
            ·
              refine ⟨27420428862750702523716683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18280285908500468349144455 27420428862750702523716683)
              ·
                refine ⟨41130643294126053785575025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27420428862750702523716683 41130643294126053785575025)
                ·
                  refine ⟨30847982470594540339181269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41130643294126053785575025 30847982470594540339181269)
                  ·
                    refine ⟨722999589154559539199561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30847982470594540339181269 722999589154559539199561)
                    ·
                      rfl

theorem cell22_2112055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2112055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112055 prefixEnd_2112055 := by exact prefixLift 2112055
  have htrace : WordTrace (prefixWord ++ tailWord_2112055) baseStart_2112055 baseEnd_2112055 := by
    simpa [prefixWord, tailWord_2112055, baseEnd_2112055] using wordTrace_append hprefix tailTrace_2112055
  have hstable : (prefixWord ++ tailWord_2112055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112055).length < 2 ^ (prefixWord ++ tailWord_2112055).sum := by decide
  have hdescent : baseEnd_2112055 < baseStart_2112055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112072 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2112072 : Nat := 118140960795 + 2112072 * 2 ^ 59
def prefixEnd_2112072 : Nat := 4983230072969 + 3 ^ 40 * 2112072 * 2
def baseEnd_2112072 : Nat := 723005408601977161524509

theorem tailTrace_2112072 : CollatzResearch.WordTrace tailWord_2112072 prefixEnd_2112072 723005408601977161524509 := by
  unfold tailWord_2112072
  simp only [CollatzResearch.WordTrace]
  refine ⟨38516797202165666012433235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51355729602887554683244313 38516797202165666012433235)
  ·
    refine ⟨57775195803248499018649853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38516797202165666012433235 57775195803248499018649853)
    ·
      refine ⟨21665698426218187131993695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57775195803248499018649853 21665698426218187131993695)
      ·
        refine ⟨32498547639327280697990543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21665698426218187131993695 32498547639327280697990543)
        ·
          refine ⟨48747821458990921046985815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32498547639327280697990543 48747821458990921046985815)
          ·
            refine ⟨73121732188486381570478723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48747821458990921046985815 73121732188486381570478723)
            ·
              refine ⟨109682598282729572355718085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73121732188486381570478723 109682598282729572355718085)
              ·
                refine ⟨20565487178011794816697141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109682598282729572355718085 20565487178011794816697141)
                ·
                  refine ⟨1928014422938605764065357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20565487178011794816697141 1928014422938605764065357)
                  ·
                    refine ⟨723005408601977161524509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928014422938605764065357 723005408601977161524509)
                    ·
                      rfl

theorem cell22_2112072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2112072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112072 prefixEnd_2112072 := by exact prefixLift 2112072
  have htrace : WordTrace (prefixWord ++ tailWord_2112072) baseStart_2112072 baseEnd_2112072 := by
    simpa [prefixWord, tailWord_2112072, baseEnd_2112072] using wordTrace_append hprefix tailTrace_2112072
  have hstable : (prefixWord ++ tailWord_2112072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112072).length < 2 ^ (prefixWord ++ tailWord_2112072).sum := by decide
  have hdescent : baseEnd_2112072 < baseStart_2112072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112181 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 4]
def baseStart_2112181 : Nat := 118140960795 + 2112181 * 2 ^ 59
def prefixEnd_2112181 : Nat := 4983230072969 + 3 ^ 40 * 2112181 * 2
def baseEnd_2112181 : Nat := 241014240509845736849725

theorem tailTrace_2112181 : CollatzResearch.WordTrace tailWord_2112181 prefixEnd_2112181 241014240509845736849725 := by
  unfold tailWord_2112181
  simp only [CollatzResearch.WordTrace]
  refine ⟨77037569960936443640584397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51358379973957629093722931 77037569960936443640584397)
  ·
    refine ⟨28889088735351166365219149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77037569960936443640584397 28889088735351166365219149)
    ·
      refine ⟨10833408275756687386957181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28889088735351166365219149 10833408275756687386957181)
      ·
        refine ⟨4062528103408757770108943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10833408275756687386957181 4062528103408757770108943)
        ·
          refine ⟨6093792155113136655163415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4062528103408757770108943 6093792155113136655163415)
          ·
            refine ⟨9140688232669704982745123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6093792155113136655163415 9140688232669704982745123)
            ·
              refine ⟨13711032349004557474117685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9140688232669704982745123 13711032349004557474117685)
              ·
                refine ⟨1285409282719177263198533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13711032349004557474117685 1285409282719177263198533)
                ·
                  refine ⟨241014240509845736849725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285409282719177263198533 241014240509845736849725)
                  ·
                    rfl

theorem cell22_2112181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_2112181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112181 prefixEnd_2112181 := by exact prefixLift 2112181
  have htrace : WordTrace (prefixWord ++ tailWord_2112181) baseStart_2112181 baseEnd_2112181 := by
    simpa [prefixWord, tailWord_2112181, baseEnd_2112181] using wordTrace_append hprefix tailTrace_2112181
  have hstable : (prefixWord ++ tailWord_2112181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112181).length < 2 ^ (prefixWord ++ tailWord_2112181).sum := by decide
  have hdescent : baseEnd_2112181 < baseStart_2112181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112183 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 1, 4]
def baseStart_2112183 : Nat := 118140960795 + 2112183 * 2 ^ 59
def prefixEnd_2112183 : Nat := 4983230072969 + 3 ^ 40 * 2112183 * 2
def baseEnd_2112183 : Nat := 723043406170409871999169

theorem tailTrace_2112183 : CollatzResearch.WordTrace tailWord_2112183 prefixEnd_2112183 723043406170409871999169 := by
  unfold tailWord_2112183
  simp only [CollatzResearch.WordTrace]
  refine ⟨77037642906929197982157203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51358428604619465321438135 77037642906929197982157203)
  ·
    refine ⟨115556464360393796973235805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77037642906929197982157203 115556464360393796973235805)
    ·
      refine ⟨43333674135147673864963427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115556464360393796973235805 43333674135147673864963427)
      ·
        refine ⟨65000511202721510797445141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43333674135147673864963427 65000511202721510797445141)
        ·
          refine ⟨3046898962627570818630241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 65000511202721510797445141 3046898962627570818630241)
          ·
            refine ⟨2285174221970678113972681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046898962627570818630241 2285174221970678113972681)
            ·
              refine ⟨1713880666478008585479511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285174221970678113972681 1713880666478008585479511)
              ·
                refine ⟨2570820999717012878219267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713880666478008585479511 2570820999717012878219267)
                ·
                  refine ⟨3856231499575519317328901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2570820999717012878219267 3856231499575519317328901)
                  ·
                    refine ⟨723043406170409871999169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856231499575519317328901 723043406170409871999169)
                    ·
                      rfl

theorem cell22_2112183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_2112183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112183 prefixEnd_2112183 := by exact prefixLift 2112183
  have htrace : WordTrace (prefixWord ++ tailWord_2112183) baseStart_2112183 baseEnd_2112183 := by
    simpa [prefixWord, tailWord_2112183, baseEnd_2112183] using wordTrace_append hprefix tailTrace_2112183
  have hstable : (prefixWord ++ tailWord_2112183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112183).length < 2 ^ (prefixWord ++ tailWord_2112183).sum := by decide
  have hdescent : baseEnd_2112183 < baseStart_2112183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112192 : List Nat := [2, 1, 1, 2, 4, 3, 9]
def baseStart_2112192 : Nat := 118140960795 + 2112192 * 2 ^ 59
def prefixEnd_2112192 : Nat := 4983230072969 + 3 ^ 40 * 2112192 * 2
def baseEnd_2112192 : Nat := 26779499520530994389783

theorem tailTrace_2112192 : CollatzResearch.WordTrace tailWord_2112192 prefixEnd_2112192 26779499520530994389783 := by
  unfold tailWord_2112192
  simp only [CollatzResearch.WordTrace]
  refine ⟨38518985581948296259617415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51358647442597728346156553 38518985581948296259617415)
  ·
    refine ⟨57778478372922444389426123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38518985581948296259617415 57778478372922444389426123)
    ·
      refine ⟨86667717559383666584139185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57778478372922444389426123 86667717559383666584139185)
      ·
        refine ⟨65000788169537749938104389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86667717559383666584139185 65000788169537749938104389)
        ·
          refine ⟨12187647781788328113394573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65000788169537749938104389 12187647781788328113394573)
          ·
            refine ⟨4570367918170623042522965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12187647781788328113394573 4570367918170623042522965)
            ·
              refine ⟨26779499520530994389783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4570367918170623042522965 26779499520530994389783)
              ·
                rfl

theorem cell22_2112192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 9].length) (baseStart_2112192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112192 prefixEnd_2112192 := by exact prefixLift 2112192
  have htrace : WordTrace (prefixWord ++ tailWord_2112192) baseStart_2112192 baseEnd_2112192 := by
    simpa [prefixWord, tailWord_2112192, baseEnd_2112192] using wordTrace_append hprefix tailTrace_2112192
  have hstable : (prefixWord ++ tailWord_2112192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112192).length < 2 ^ (prefixWord ++ tailWord_2112192).sum := by decide
  have hdescent : baseEnd_2112192 < baseStart_2112192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112196 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2112196 : Nat := 118140960795 + 2112196 * 2 ^ 59
def prefixEnd_2112196 : Nat := 4983230072969 + 3 ^ 40 * 2112196 * 2
def baseEnd_2112196 : Nat := 723047856336082171424129

theorem tailTrace_2112196 : CollatzResearch.WordTrace tailWord_2112196 prefixEnd_2112196 723047856336082171424129 := by
  unfold tailWord_2112196
  simp only [CollatzResearch.WordTrace]
  refine ⟨38519058527941050601190221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51358744703921400801586961 38519058527941050601190221)
  ·
    refine ⟨14444646947977893975446333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38519058527941050601190221 14444646947977893975446333)
    ·
      refine ⟨5416742605491710240792375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14444646947977893975446333 5416742605491710240792375)
      ·
        refine ⟨8125113908237565361188563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416742605491710240792375 8125113908237565361188563)
        ·
          refine ⟨12187670862356348041782845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8125113908237565361188563 12187670862356348041782845)
          ·
            refine ⟨4570376573383630515668567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12187670862356348041782845 4570376573383630515668567)
            ·
              refine ⟨6855564860075445773502851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570376573383630515668567 6855564860075445773502851)
              ·
                refine ⟨10283347290113168660254277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6855564860075445773502851 10283347290113168660254277)
                ·
                  refine ⟨1928127616896219123797677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10283347290113168660254277 1928127616896219123797677)
                  ·
                    refine ⟨723047856336082171424129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928127616896219123797677 723047856336082171424129)
                    ·
                      rfl

theorem cell22_2112196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2112196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112196 prefixEnd_2112196 := by exact prefixLift 2112196
  have htrace : WordTrace (prefixWord ++ tailWord_2112196) baseStart_2112196 baseEnd_2112196 := by
    simpa [prefixWord, tailWord_2112196, baseEnd_2112196] using wordTrace_append hprefix tailTrace_2112196
  have hstable : (prefixWord ++ tailWord_2112196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112196).length < 2 ^ (prefixWord ++ tailWord_2112196).sum := by decide
  have hdescent : baseEnd_2112196 < baseStart_2112196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112213 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_2112213 : Nat := 118140960795 + 2112213 * 2 ^ 59
def prefixEnd_2112213 : Nat := 4983230072969 + 3 ^ 40 * 2112213 * 2
def baseEnd_2112213 : Nat := 723053675783499793749077

theorem tailTrace_2112213 : CollatzResearch.WordTrace tailWord_2112213 prefixEnd_2112213 723053675783499793749077 := by
  unfold tailWord_2112213
  simp only [CollatzResearch.WordTrace]
  refine ⟨77038737096820513105749293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51359158064547008737166195 77038737096820513105749293)
  ·
    refine ⟨28889526411307692414655985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77038737096820513105749293 28889526411307692414655985)
    ·
      refine ⟨21667144808480769310991989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28889526411307692414655985 21667144808480769310991989)
      ·
        refine ⟨2031294825795072122905499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21667144808480769310991989 2031294825795072122905499)
        ·
          refine ⟨3046942238692608184358249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031294825795072122905499 3046942238692608184358249)
          ·
            refine ⟨2285206679019456138268687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046942238692608184358249 2285206679019456138268687)
            ·
              refine ⟨3427810018529184207403031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285206679019456138268687 3427810018529184207403031)
              ·
                refine ⟨5141715027793776311104547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427810018529184207403031 5141715027793776311104547)
                ·
                  refine ⟨7712572541690664466656821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5141715027793776311104547 7712572541690664466656821)
                  ·
                    refine ⟨723053675783499793749077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7712572541690664466656821 723053675783499793749077)
                    ·
                      rfl

theorem cell22_2112213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_2112213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112213 prefixEnd_2112213 := by exact prefixLift 2112213
  have htrace : WordTrace (prefixWord ++ tailWord_2112213) baseStart_2112213 baseEnd_2112213 := by
    simpa [prefixWord, tailWord_2112213, baseEnd_2112213] using wordTrace_append hprefix tailTrace_2112213
  have hstable : (prefixWord ++ tailWord_2112213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112213).length < 2 ^ (prefixWord ++ tailWord_2112213).sum := by decide
  have hdescent : baseEnd_2112213 < baseStart_2112213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112245 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2112245 : Nat := 118140960795 + 2112245 * 2 ^ 59
def prefixEnd_2112245 : Nat := 4983230072969 + 3 ^ 40 * 2112245 * 2
def baseEnd_2112245 : Nat := 723064630037462376948979

theorem tailTrace_2112245 : CollatzResearch.WordTrace tailWord_2112245 prefixEnd_2112245 723064630037462376948979 := by
  unfold tailWord_2112245
  simp only [CollatzResearch.WordTrace]
  refine ⟨77039904232704582570914189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51359936155136388380609459 77039904232704582570914189)
  ·
    refine ⟨28889964087264218464092821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77039904232704582570914189 28889964087264218464092821)
    ·
      refine ⟨1354217066590510240504351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28889964087264218464092821 1354217066590510240504351)
      ·
        refine ⟨2031325599885765360756527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1354217066590510240504351 2031325599885765360756527)
        ·
          refine ⟨3046988399828648041134791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2031325599885765360756527 3046988399828648041134791)
          ·
            refine ⟨4570482599742972061702187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046988399828648041134791 4570482599742972061702187)
            ·
              refine ⟨6855723899614458092553281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570482599742972061702187 6855723899614458092553281)
              ·
                refine ⟨5141792924710843569414961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6855723899614458092553281 5141792924710843569414961)
                ·
                  refine ⟨3856344693533132677061221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5141792924710843569414961 3856344693533132677061221)
                  ·
                    refine ⟨723064630037462376948979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856344693533132677061221 723064630037462376948979)
                    ·
                      rfl

theorem cell22_2112245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2112245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112245 prefixEnd_2112245 := by exact prefixLift 2112245
  have htrace : WordTrace (prefixWord ++ tailWord_2112245) baseStart_2112245 baseEnd_2112245 := by
    simpa [prefixWord, tailWord_2112245, baseEnd_2112245] using wordTrace_append hprefix tailTrace_2112245
  have hstable : (prefixWord ++ tailWord_2112245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112245).length < 2 ^ (prefixWord ++ tailWord_2112245).sum := by decide
  have hdescent : baseEnd_2112245 < baseStart_2112245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112258 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2112258 : Nat := 118140960795 + 2112258 * 2 ^ 59
def prefixEnd_2112258 : Nat := 4983230072969 + 3 ^ 40 * 2112258 * 2
def baseEnd_2112258 : Nat := 723069080203134676373939

theorem tailTrace_2112258 : CollatzResearch.WordTrace tailWord_2112258 prefixEnd_2112258 723069080203134676373939 := by
  unfold tailWord_2112258
  simp only [CollatzResearch.WordTrace]
  refine ⟨19260094595414371447784357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51360252254438323860758285 19260094595414371447784357)
  ·
    refine ⟨3611267736640194646459567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19260094595414371447784357 3611267736640194646459567)
    ·
      refine ⟨5416901604960291969689351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611267736640194646459567 5416901604960291969689351)
      ·
        refine ⟨8125352407440437954534027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416901604960291969689351 8125352407440437954534027)
        ·
          refine ⟨12188028611160656931801041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8125352407440437954534027 12188028611160656931801041)
          ·
            refine ⟨9141021458370492698850781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12188028611160656931801041 9141021458370492698850781)
            ·
              refine ⟨3427883046888934762069043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9141021458370492698850781 3427883046888934762069043)
              ·
                refine ⟨5141824570333402143103565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427883046888934762069043 5141824570333402143103565)
                ·
                  refine ⟨1928184213875025803663837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5141824570333402143103565 1928184213875025803663837)
                  ·
                    refine ⟨723069080203134676373939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928184213875025803663837 723069080203134676373939)
                    ·
                      rfl

theorem cell22_2112258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2112258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112258 prefixEnd_2112258 := by exact prefixLift 2112258
  have htrace : WordTrace (prefixWord ++ tailWord_2112258) baseStart_2112258 baseEnd_2112258 := by
    simpa [prefixWord, tailWord_2112258, baseEnd_2112258] using wordTrace_append hprefix tailTrace_2112258
  have hstable : (prefixWord ++ tailWord_2112258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112258).length < 2 ^ (prefixWord ++ tailWord_2112258).sum := by decide
  have hdescent : baseEnd_2112258 < baseStart_2112258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112267 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_2112267 : Nat := 118140960795 + 2112267 * 2 ^ 59
def prefixEnd_2112267 : Nat := 4983230072969 + 3 ^ 40 * 2112267 * 2
def baseEnd_2112267 : Nat := 723072161087061652898911

theorem tailTrace_2112267 : CollatzResearch.WordTrace tailWord_2112267 prefixEnd_2112267 723072161087061652898911 := by
  unfold tailWord_2112267
  simp only [CollatzResearch.WordTrace]
  refine ⟨77040706638624880328215055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51360471092416586885476703 77040706638624880328215055)
  ·
    refine ⟨115561059957937320492322583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77040706638624880328215055 115561059957937320492322583)
    ·
      refine ⟨173341589936905980738483875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115561059957937320492322583 173341589936905980738483875)
      ·
        refine ⟨260012384905358971107725813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173341589936905980738483875 260012384905358971107725813)
        ·
          refine ⟨24376161084877403541349295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260012384905358971107725813 24376161084877403541349295)
          ·
            refine ⟨36564241627316105312023943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24376161084877403541349295 36564241627316105312023943)
            ·
              refine ⟨54846362440974157968035915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36564241627316105312023943 54846362440974157968035915)
              ·
                refine ⟨82269543661461236952053873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54846362440974157968035915 82269543661461236952053873)
                ·
                  refine ⟨61702157746095927714040405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82269543661461236952053873 61702157746095927714040405)
                  ·
                    refine ⟨723072161087061652898911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61702157746095927714040405 723072161087061652898911)
                    ·
                      rfl

theorem cell22_2112267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_2112267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112267 prefixEnd_2112267 := by exact prefixLift 2112267
  have htrace : WordTrace (prefixWord ++ tailWord_2112267) baseStart_2112267 baseEnd_2112267 := by
    simpa [prefixWord, tailWord_2112267, baseEnd_2112267] using wordTrace_append hprefix tailTrace_2112267
  have hstable : (prefixWord ++ tailWord_2112267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112267).length < 2 ^ (prefixWord ++ tailWord_2112267).sum := by decide
  have hdescent : baseEnd_2112267 < baseStart_2112267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112333 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2112333 : Nat := 118140960795 + 2112333 * 2 ^ 59
def prefixEnd_2112333 : Nat := 4983230072969 + 3 ^ 40 * 2112333 * 2
def baseEnd_2112333 : Nat := 241031584745286493582903

theorem tailTrace_2112333 : CollatzResearch.WordTrace tailWord_2112333 prefixEnd_2112333 241031584745286493582903 := by
  unfold tailWord_2112333
  simp only [CollatzResearch.WordTrace]
  refine ⟨77043113856385773600117653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51362075904257182400078435 77043113856385773600117653)
  ·
    refine ⟨3611395962018083137505515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 77043113856385773600117653 3611395962018083137505515)
    ·
      refine ⟨5417093943027124706258273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611395962018083137505515 5417093943027124706258273)
      ·
        refine ⟨4062820457270343529693705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5417093943027124706258273 4062820457270343529693705)
        ·
          refine ⟨3047115342952757647270279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4062820457270343529693705 3047115342952757647270279)
          ·
            refine ⟨4570673014429136470905419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3047115342952757647270279 4570673014429136470905419)
            ·
              refine ⟨6856009521643704706358129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4570673014429136470905419 6856009521643704706358129)
              ·
                refine ⟨5142007141232778529768597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6856009521643704706358129 5142007141232778529768597)
                ·
                  refine ⟨241031584745286493582903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5142007141232778529768597 241031584745286493582903)
                  ·
                    rfl

theorem cell22_2112333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2112333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112333 prefixEnd_2112333 := by exact prefixLift 2112333
  have htrace : WordTrace (prefixWord ++ tailWord_2112333) baseStart_2112333 baseEnd_2112333 := by
    simpa [prefixWord, tailWord_2112333, baseEnd_2112333] using wordTrace_append hprefix tailTrace_2112333
  have hstable : (prefixWord ++ tailWord_2112333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112333).length < 2 ^ (prefixWord ++ tailWord_2112333).sum := by decide
  have hdescent : baseEnd_2112333 < baseStart_2112333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112346 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_2112346 : Nat := 118140960795 + 2112346 * 2 ^ 59
def prefixEnd_2112346 : Nat := 4983230072969 + 3 ^ 40 * 2112346 * 2
def baseEnd_2112346 : Nat := 723099204401531780173669

theorem tailTrace_2112346 : CollatzResearch.WordTrace tailWord_2112346 prefixEnd_2112346 723099204401531780173669 := by
  unfold tailWord_2112346
  simp only [CollatzResearch.WordTrace]
  refine ⟨19260897001334669205085223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51362392003559117880227261 19260897001334669205085223)
  ·
    refine ⟨28891345502002003807627835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19260897001334669205085223 28891345502002003807627835)
    ·
      refine ⟨43337018253003005711441753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28891345502002003807627835 43337018253003005711441753)
      ·
        refine ⟨32502763689752254283581315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43337018253003005711441753 32502763689752254283581315)
        ·
          refine ⟨48754145534628381425371973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32502763689752254283581315 48754145534628381425371973)
          ·
            refine ⟨9141402287742821517257245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48754145534628381425371973 9141402287742821517257245)
            ·
              refine ⟨3428025857903558068971467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9141402287742821517257245 3428025857903558068971467)
              ·
                refine ⟨5142038786855337103457201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428025857903558068971467 5142038786855337103457201)
                ·
                  refine ⟨3856529090141502827592901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142038786855337103457201 3856529090141502827592901)
                  ·
                    refine ⟨723099204401531780173669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3856529090141502827592901 723099204401531780173669)
                    ·
                      rfl

theorem cell22_2112346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_2112346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112346 prefixEnd_2112346 := by exact prefixLift 2112346
  have htrace : WordTrace (prefixWord ++ tailWord_2112346) baseStart_2112346 baseEnd_2112346 := by
    simpa [prefixWord, tailWord_2112346, baseEnd_2112346] using wordTrace_append hprefix tailTrace_2112346
  have hstable : (prefixWord ++ tailWord_2112346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112346).length < 2 ^ (prefixWord ++ tailWord_2112346).sum := by decide
  have hdescent : baseEnd_2112346 < baseStart_2112346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112382 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2112382 : Nat := 118140960795 + 2112382 * 2 ^ 59
def prefixEnd_2112382 : Nat := 4983230072969 + 3 ^ 40 * 2112382 * 2
def baseEnd_2112382 : Nat := 723111527937239686273559

theorem tailTrace_2112382 : CollatzResearch.WordTrace tailWord_2112382 prefixEnd_2112382 723111527937239686273559 := by
  unfold tailWord_2112382
  simp only [CollatzResearch.WordTrace]
  refine ⟨9630612629151031871081425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51363267355472169979100933 9630612629151031871081425)
  ·
    refine ⟨7222959471863273903311069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9630612629151031871081425 7222959471863273903311069)
    ·
      refine ⟨2708609801948727713741651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7222959471863273903311069 2708609801948727713741651)
      ·
        refine ⟨4062914702923091570612477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708609801948727713741651 4062914702923091570612477)
        ·
          refine ⟨1523593013596159338979679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4062914702923091570612477 1523593013596159338979679)
          ·
            refine ⟨2285389520394239008469519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1523593013596159338979679 2285389520394239008469519)
            ·
              refine ⟨3428084280591358512704279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285389520394239008469519 3428084280591358512704279)
              ·
                refine ⟨5142126420887037769056419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428084280591358512704279 5142126420887037769056419)
                ·
                  refine ⟨7713189631330556653584629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5142126420887037769056419 7713189631330556653584629)
                  ·
                    refine ⟨723111527937239686273559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7713189631330556653584629 723111527937239686273559)
                    ·
                      rfl

theorem cell22_2112382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2112382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112382 prefixEnd_2112382 := by exact prefixLift 2112382
  have htrace : WordTrace (prefixWord ++ tailWord_2112382) baseStart_2112382 baseEnd_2112382 := by
    simpa [prefixWord, tailWord_2112382, baseEnd_2112382] using wordTrace_append hprefix tailTrace_2112382
  have hstable : (prefixWord ++ tailWord_2112382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112382).length < 2 ^ (prefixWord ++ tailWord_2112382).sum := by decide
  have hdescent : baseEnd_2112382 < baseStart_2112382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112479 : List Nat := [1, 1, 2, 3, 15]
def baseStart_2112479 : Nat := 118140960795 + 2112479 * 2 ^ 59
def prefixEnd_2112479 : Nat := 4983230072969 + 3 ^ 40 * 2112479 * 2
def baseEnd_2112479 : Nat := 2975904251109315911927

theorem tailTrace_2112479 : CollatzResearch.WordTrace tailWord_2112479 prefixEnd_2112479 2975904251109315911927 := by
  unfold tailWord_2112479
  simp only [CollatzResearch.WordTrace]
  refine ⟨77048438913856840534932491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51365625942571227023288327 77048438913856840534932491)
  ·
    refine ⟨115572658370785260802398737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77048438913856840534932491 115572658370785260802398737)
    ·
      refine ⟨86679493778088945601799053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115572658370785260802398737 86679493778088945601799053)
      ·
        refine ⟨32504810166783354600674645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86679493778088945601799053 32504810166783354600674645)
        ·
          refine ⟨2975904251109315911927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 32504810166783354600674645 2975904251109315911927)
          ·
            rfl

theorem cell22_2112479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 15].length) (baseStart_2112479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112479 prefixEnd_2112479 := by exact prefixLift 2112479
  have htrace : WordTrace (prefixWord ++ tailWord_2112479) baseStart_2112479 baseEnd_2112479 := by
    simpa [prefixWord, tailWord_2112479, baseEnd_2112479] using wordTrace_append hprefix tailTrace_2112479
  have hstable : (prefixWord ++ tailWord_2112479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112479).length < 2 ^ (prefixWord ++ tailWord_2112479).sum := by decide
  have hdescent : baseEnd_2112479 < baseStart_2112479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112513 : List Nat := [1, 2, 4, 1, 2, 3, 3, 6]
def baseStart_2112513 : Nat := 118140960795 + 2112513 * 2 ^ 59
def prefixEnd_2112513 : Nat := 4983230072969 + 3 ^ 40 * 2112513 * 2
def baseEnd_2112513 : Nat := 80350707990488779027573

theorem tailTrace_2112513 : CollatzResearch.WordTrace tailWord_2112513 prefixEnd_2112513 80350707990488779027573 := by
  unfold tailWord_2112513
  simp only [CollatzResearch.WordTrace]
  refine ⟨77049678995733664341670193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51366452663822442894446795 77049678995733664341670193)
  ·
    refine ⟨57787259246800248256252645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77049678995733664341670193 57787259246800248256252645)
    ·
      refine ⟨10835111108775046548047371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57787259246800248256252645 10835111108775046548047371)
      ·
        refine ⟨16252666663162569822071057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10835111108775046548047371 16252666663162569822071057)
        ·
          refine ⟨12189499997371927366553293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16252666663162569822071057 12189499997371927366553293)
          ·
            refine ⟨4571062499014472762457485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12189499997371927366553293 4571062499014472762457485)
            ·
              refine ⟨1714148437130427285921557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4571062499014472762457485 1714148437130427285921557)
              ·
                refine ⟨80350707990488779027573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1714148437130427285921557 80350707990488779027573)
                ·
                  rfl

theorem cell22_2112513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 6].length) (baseStart_2112513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112513 prefixEnd_2112513 := by exact prefixLift 2112513
  have htrace : WordTrace (prefixWord ++ tailWord_2112513) baseStart_2112513 baseEnd_2112513 := by
    simpa [prefixWord, tailWord_2112513, baseEnd_2112513] using wordTrace_append hprefix tailTrace_2112513
  have hstable : (prefixWord ++ tailWord_2112513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112513).length < 2 ^ (prefixWord ++ tailWord_2112513).sum := by decide
  have hdescent : baseEnd_2112513 < baseStart_2112513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112545 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_2112545 : Nat := 118140960795 + 2112545 * 2 ^ 59
def prefixEnd_2112545 : Nat := 4983230072969 + 3 ^ 40 * 2112545 * 2
def baseEnd_2112545 : Nat := 723167326168361594448059

theorem tailTrace_2112545 : CollatzResearch.WordTrace tailWord_2112545 prefixEnd_2112545 723167326168361594448059 := by
  unfold tailWord_2112545
  simp only [CollatzResearch.WordTrace]
  refine ⟨77050846131617733806835089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51367230754411822537890059 77050846131617733806835089)
  ·
    refine ⟨57788134598713300355126317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77050846131617733806835089 57788134598713300355126317)
    ·
      refine ⟨21670550474517487633172369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57788134598713300355126317 21670550474517487633172369)
      ·
        refine ⟨16252912855888115724879277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21670550474517487633172369 16252912855888115724879277)
        ·
          refine ⟨6094842320958043396829729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16252912855888115724879277 6094842320958043396829729)
          ·
            refine ⟨4571131740718532547622297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094842320958043396829729 4571131740718532547622297)
            ·
              refine ⟨3428348805538899410716723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4571131740718532547622297 3428348805538899410716723)
              ·
                refine ⟨5142523208308349116075085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428348805538899410716723 5142523208308349116075085)
                ·
                  refine ⟨1928446203115630918528157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5142523208308349116075085 1928446203115630918528157)
                  ·
                    refine ⟨723167326168361594448059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928446203115630918528157 723167326168361594448059)
                    ·
                      rfl

theorem cell22_2112545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_2112545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112545 prefixEnd_2112545 := by exact prefixLift 2112545
  have htrace : WordTrace (prefixWord ++ tailWord_2112545) baseStart_2112545 baseEnd_2112545 := by
    simpa [prefixWord, tailWord_2112545, baseEnd_2112545] using wordTrace_append hprefix tailTrace_2112545
  have hstable : (prefixWord ++ tailWord_2112545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112545).length < 2 ^ (prefixWord ++ tailWord_2112545).sum := by decide
  have hdescent : baseEnd_2112545 < baseStart_2112545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112556 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_2112556 : Nat := 118140960795 + 2112556 * 2 ^ 59
def prefixEnd_2112556 : Nat := 4983230072969 + 3 ^ 40 * 2112556 * 2
def baseEnd_2112556 : Nat := 723171091693161232423025

theorem tailTrace_2112556 : CollatzResearch.WordTrace tailWord_2112556 prefixEnd_2112556 723171091693161232423025 := by
  unfold tailWord_2112556
  simp only [CollatzResearch.WordTrace]
  refine ⟨38525623667288941342742761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51367498223051921790323681 38525623667288941342742761)
  ·
    refine ⟨28894217750466706007057071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38525623667288941342742761 28894217750466706007057071)
    ·
      refine ⟨43341326625700059010585607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28894217750466706007057071 43341326625700059010585607)
      ·
        refine ⟨65011989938550088515878411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43341326625700059010585607 65011989938550088515878411)
        ·
          refine ⟨97517984907825132773817617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65011989938550088515878411 97517984907825132773817617)
          ·
            refine ⟨73138488680868849580363213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97517984907825132773817617 73138488680868849580363213)
            ·
              refine ⟨27426933255325818592636205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73138488680868849580363213 27426933255325818592636205)
              ·
                refine ⟨10285099970747181972238577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27426933255325818592636205 10285099970747181972238577)
                ·
                  refine ⟨7713824978060386479178933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10285099970747181972238577 7713824978060386479178933)
                  ·
                    refine ⟨723171091693161232423025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7713824978060386479178933 723171091693161232423025)
                    ·
                      rfl

theorem cell22_2112556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_2112556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112556 prefixEnd_2112556 := by exact prefixLift 2112556
  have htrace : WordTrace (prefixWord ++ tailWord_2112556) baseStart_2112556 baseEnd_2112556 := by
    simpa [prefixWord, tailWord_2112556, baseEnd_2112556] using wordTrace_append hprefix tailTrace_2112556
  have hstable : (prefixWord ++ tailWord_2112556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112556).length < 2 ^ (prefixWord ++ tailWord_2112556).sum := by decide
  have hdescent : baseEnd_2112556 < baseStart_2112556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112586 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_2112586 : Nat := 118140960795 + 2112586 * 2 ^ 59
def prefixEnd_2112586 : Nat := 4983230072969 + 3 ^ 40 * 2112586 * 2
def baseEnd_2112586 : Nat := 241060453768750384724311

theorem tailTrace_2112586 : CollatzResearch.WordTrace tailWord_2112586 prefixEnd_2112586 241060453768750384724311 := by
  unfold tailWord_2112586
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263085381117299452269403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51368227682979465206051741 19263085381117299452269403)
  ·
    refine ⟨28894628071675949178404105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19263085381117299452269403 28894628071675949178404105)
    ·
      refine ⟨21670971053756961883803079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28894628071675949178404105 21670971053756961883803079)
      ·
        refine ⟨32506456580635442825704619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21670971053756961883803079 32506456580635442825704619)
        ·
          refine ⟨48759684870953164238556929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32506456580635442825704619 48759684870953164238556929)
          ·
            refine ⟨36569763653214873178917697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48759684870953164238556929 36569763653214873178917697)
            ·
              refine ⟨27427322739911154884188273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36569763653214873178917697 27427322739911154884188273)
              ·
                refine ⟨20570492054933366163141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27427322739911154884188273 20570492054933366163141205)
                ·
                  refine ⟨241060453768750384724311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20570492054933366163141205 241060453768750384724311)
                  ·
                    rfl

theorem cell22_2112586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_2112586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112586 prefixEnd_2112586 := by exact prefixLift 2112586
  have htrace : WordTrace (prefixWord ++ tailWord_2112586) baseStart_2112586 baseEnd_2112586 := by
    simpa [prefixWord, tailWord_2112586, baseEnd_2112586] using wordTrace_append hprefix tailTrace_2112586
  have hstable : (prefixWord ++ tailWord_2112586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112586).length < 2 ^ (prefixWord ++ tailWord_2112586).sum := by decide
  have hdescent : baseEnd_2112586 < baseStart_2112586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112601 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_2112601 : Nat := 118140960795 + 2112601 * 2 ^ 59
def prefixEnd_2112601 : Nat := 4983230072969 + 3 ^ 40 * 2112601 * 2
def baseEnd_2112601 : Nat := 723186496112796115047887

theorem tailTrace_2112601 : CollatzResearch.WordTrace tailWord_2112601 prefixEnd_2112601 723186496112796115047887 := by
  unfold tailWord_2112601
  simp only [CollatzResearch.WordTrace]
  refine ⟨77052888619414855370873657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51368592412943236913915771 77052888619414855370873657)
  ·
    refine ⟨57789666464561141528155243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77052888619414855370873657 57789666464561141528155243)
    ·
      refine ⟨86684499696841712292232865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57789666464561141528155243 86684499696841712292232865)
      ·
        refine ⟨65013374772631284219174649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86684499696841712292232865 65013374772631284219174649)
        ·
          refine ⟨48760031079473463164380987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65013374772631284219174649 48760031079473463164380987)
          ·
            refine ⟨73140046619210194746571481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48760031079473463164380987 73140046619210194746571481)
            ·
              refine ⟨54855034964407646059928611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73140046619210194746571481 54855034964407646059928611)
              ·
                refine ⟨82282552446611469089892917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54855034964407646059928611 82282552446611469089892917)
                ·
                  refine ⟨7713989291869825227177461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82282552446611469089892917 7713989291869825227177461)
                  ·
                    refine ⟨723186496112796115047887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7713989291869825227177461 723186496112796115047887)
                    ·
                      rfl

theorem cell22_2112601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_2112601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112601 prefixEnd_2112601 := by exact prefixLift 2112601
  have htrace : WordTrace (prefixWord ++ tailWord_2112601) baseStart_2112601 baseEnd_2112601 := by
    simpa [prefixWord, tailWord_2112601, baseEnd_2112601] using wordTrace_append hprefix tailTrace_2112601
  have hstable : (prefixWord ++ tailWord_2112601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112601).length < 2 ^ (prefixWord ++ tailWord_2112601).sum := by decide
  have hdescent : baseEnd_2112601 < baseStart_2112601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112622 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2112622 : Nat := 118140960795 + 2112622 * 2 ^ 59
def prefixEnd_2112622 : Nat := 4983230072969 + 3 ^ 40 * 2112622 * 2
def baseEnd_2112622 : Nat := 723193684841959060272823

theorem tailTrace_2112622 : CollatzResearch.WordTrace tailWord_2112622 prefixEnd_2112622 723193684841959060272823 := by
  unfold tailWord_2112622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631706819042346994673515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51369103034892517304925413 9631706819042346994673515)
  ·
    refine ⟨14447560228563520492010273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9631706819042346994673515 14447560228563520492010273)
    ·
      refine ⟨10835670171422640369007705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14447560228563520492010273 10835670171422640369007705)
      ·
        refine ⟨8126752628566980276755779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10835670171422640369007705 8126752628566980276755779)
        ·
          refine ⟨12190128942850470415133669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8126752628566980276755779 12190128942850470415133669)
          ·
            refine ⟨2285649176784463202837563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12190128942850470415133669 2285649176784463202837563)
            ·
              refine ⟨3428473765176694804256345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285649176784463202837563 3428473765176694804256345)
              ·
                refine ⟨2571355323882521103192259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428473765176694804256345 2571355323882521103192259)
                ·
                  refine ⟨3857032985823781654788389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571355323882521103192259 3857032985823781654788389)
                  ·
                    refine ⟨723193684841959060272823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857032985823781654788389 723193684841959060272823)
                    ·
                      rfl

theorem cell22_2112622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2112622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112622 prefixEnd_2112622 := by exact prefixLift 2112622
  have htrace : WordTrace (prefixWord ++ tailWord_2112622) baseStart_2112622 baseEnd_2112622 := by
    simpa [prefixWord, tailWord_2112622, baseEnd_2112622] using wordTrace_append hprefix tailTrace_2112622
  have hstable : (prefixWord ++ tailWord_2112622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112622).length < 2 ^ (prefixWord ++ tailWord_2112622).sum := by decide
  have hdescent : baseEnd_2112622 < baseStart_2112622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112631 : List Nat := [1, 1, 3, 1, 1, 4, 1, 10]
def baseStart_2112631 : Nat := 118140960795 + 2112631 * 2 ^ 59
def prefixEnd_2112631 : Nat := 4983230072969 + 3 ^ 40 * 2112631 * 2
def baseEnd_2112631 : Nat := 80355196191765115199755

theorem tailTrace_2112631 : CollatzResearch.WordTrace tailWord_2112631 prefixEnd_2112631 80355196191765115199755 := by
  unfold tailWord_2112631
  simp only [CollatzResearch.WordTrace]
  refine ⟨77053982809306170494465747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51369321872870780329643831 77053982809306170494465747)
  ·
    refine ⟨115580974213959255741698621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77053982809306170494465747 115580974213959255741698621)
    ·
      refine ⟨43342865330234720903136983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115580974213959255741698621 43342865330234720903136983)
      ·
        refine ⟨65014297995352081354705475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43342865330234720903136983 65014297995352081354705475)
        ·
          refine ⟨97521446993028122032058213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65014297995352081354705475 97521446993028122032058213)
          ·
            refine ⟨18285271311192772881010915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97521446993028122032058213 18285271311192772881010915)
            ·
              refine ⟨27427906966789159321516373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18285271311192772881010915 27427906966789159321516373)
              ·
                refine ⟨80355196191765115199755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27427906966789159321516373 80355196191765115199755)
                ·
                  rfl

theorem cell22_2112631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 10].length) (baseStart_2112631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112631 prefixEnd_2112631 := by exact prefixLift 2112631
  have htrace : WordTrace (prefixWord ++ tailWord_2112631) baseStart_2112631 baseEnd_2112631 := by
    simpa [prefixWord, tailWord_2112631, baseEnd_2112631] using wordTrace_append hprefix tailTrace_2112631
  have hstable : (prefixWord ++ tailWord_2112631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112631).length < 2 ^ (prefixWord ++ tailWord_2112631).sum := by decide
  have hdescent : baseEnd_2112631 < baseStart_2112631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112648 : List Nat := [2, 1, 3, 4, 2, 10]
def baseStart_2112648 : Nat := 118140960795 + 2112648 * 2 ^ 59
def prefixEnd_2112648 : Nat := 4983230072969 + 3 ^ 40 * 2112648 * 2
def baseEnd_2112648 : Nat := 8928426977448193322503

theorem tailTrace_2112648 : CollatzResearch.WordTrace tailWord_2112648 prefixEnd_2112648 8928426977448193322503 := by
  unfold tailWord_2112648
  simp only [CollatzResearch.WordTrace]
  refine ⟨38527301425122291198917299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51369735233496388265223065 38527301425122291198917299)
  ·
    refine ⟨57790952137683436798375949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38527301425122291198917299 57790952137683436798375949)
    ·
      refine ⟨21671607051631288799390981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57790952137683436798375949 21671607051631288799390981)
      ·
        refine ⟨4063426322180866649885809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21671607051631288799390981 4063426322180866649885809)
        ·
          refine ⟨3047569741635649987414357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4063426322180866649885809 3047569741635649987414357)
          ·
            refine ⟨8928426977448193322503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3047569741635649987414357 8928426977448193322503)
            ·
              rfl

theorem cell22_2112648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 10].length) (baseStart_2112648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112648 prefixEnd_2112648 := by exact prefixLift 2112648
  have htrace : WordTrace (prefixWord ++ tailWord_2112648) baseStart_2112648 baseEnd_2112648 := by
    simpa [prefixWord, tailWord_2112648, baseEnd_2112648] using wordTrace_append hprefix tailTrace_2112648
  have hstable : (prefixWord ++ tailWord_2112648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112648).length < 2 ^ (prefixWord ++ tailWord_2112648).sum := by decide
  have hdescent : baseEnd_2112648 < baseStart_2112648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112654 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_2112654 : Nat := 118140960795 + 2112654 * 2 ^ 59
def prefixEnd_2112654 : Nat := 4983230072969 + 3 ^ 40 * 2112654 * 2
def baseEnd_2112654 : Nat := 241068213031973881157575

theorem tailTrace_2112654 : CollatzResearch.WordTrace tailWord_2112654 prefixEnd_2112654 241068213031973881157575 := by
  unfold tailWord_2112654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9631852711027855677819127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51369881125481896948368677 9631852711027855677819127)
  ·
    refine ⟨14447779066541783516728691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9631852711027855677819127 14447779066541783516728691)
    ·
      refine ⟨21671668599812675275093037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14447779066541783516728691 21671668599812675275093037)
      ·
        refine ⟨8126875724929753228159889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21671668599812675275093037 8126875724929753228159889)
        ·
          refine ⟨6095156793697314921119917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8126875724929753228159889 6095156793697314921119917)
          ·
            refine ⟨2285683797636493095419969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6095156793697314921119917 2285683797636493095419969)
            ·
              refine ⟨1714262848227369821564977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2285683797636493095419969 1714262848227369821564977)
              ·
                refine ⟨1285697136170527366173733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1714262848227369821564977 1285697136170527366173733)
                ·
                  refine ⟨241068213031973881157575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1285697136170527366173733 241068213031973881157575)
                  ·
                    rfl

theorem cell22_2112654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_2112654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112654 prefixEnd_2112654 := by exact prefixLift 2112654
  have htrace : WordTrace (prefixWord ++ tailWord_2112654) baseStart_2112654 baseEnd_2112654 := by
    simpa [prefixWord, tailWord_2112654, baseEnd_2112654] using wordTrace_append hprefix tailTrace_2112654
  have hstable : (prefixWord ++ tailWord_2112654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112654).length < 2 ^ (prefixWord ++ tailWord_2112654).sum := by decide
  have hdescent : baseEnd_2112654 < baseStart_2112654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112682 : List Nat := [3, 1, 5, 1, 1, 2, 3, 6]
def baseStart_2112682 : Nat := 118140960795 + 2112682 * 2 ^ 59
def prefixEnd_2112682 : Nat := 4983230072969 + 3 ^ 40 * 2112682 * 2
def baseEnd_2112682 : Nat := 80357136007570989308071

theorem tailTrace_2112682 : CollatzResearch.WordTrace tailWord_2112682 prefixEnd_2112682 80357136007570989308071 := by
  unfold tailWord_2112682
  simp only [CollatzResearch.WordTrace]
  refine ⟨19263960733030351551143075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51370561954747604136381533 19263960733030351551143075)
  ·
    refine ⟨28895941099545527326714613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19263960733030351551143075 28895941099545527326714613)
    ·
      refine ⟨2708994478082393186879495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28895941099545527326714613 2708994478082393186879495)
      ·
        refine ⟨4063491717123589780319243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708994478082393186879495 4063491717123589780319243)
        ·
          refine ⟨6095237575685384670478865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063491717123589780319243 6095237575685384670478865)
          ·
            refine ⟨4571428181764038502859149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6095237575685384670478865 4571428181764038502859149)
            ·
              refine ⟨1714285568161514438572181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4571428181764038502859149 1714285568161514438572181)
              ·
                refine ⟨80357136007570989308071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1714285568161514438572181 80357136007570989308071)
                ·
                  rfl

theorem cell22_2112682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_2112682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112682 prefixEnd_2112682 := by exact prefixLift 2112682
  have htrace : WordTrace (prefixWord ++ tailWord_2112682) baseStart_2112682 baseEnd_2112682 := by
    simpa [prefixWord, tailWord_2112682, baseEnd_2112682] using wordTrace_append hprefix tailTrace_2112682
  have hstable : (prefixWord ++ tailWord_2112682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112682).length < 2 ^ (prefixWord ++ tailWord_2112682).sum := by decide
  have hdescent : baseEnd_2112682 < baseStart_2112682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112697 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 1, 3]
def baseStart_2112697 : Nat := 118140960795 + 2112697 * 2 ^ 59
def prefixEnd_2112697 : Nat := 4983230072969 + 3 ^ 40 * 2112697 * 2
def baseEnd_2112697 : Nat := 723219358874683864647593

theorem tailTrace_2112697 : CollatzResearch.WordTrace tailWord_2112697 prefixEnd_2112697 723219358874683864647593 := by
  unfold tailWord_2112697
  simp only [CollatzResearch.WordTrace]
  refine ⟨77056390027067063766368345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51370926684711375844245563 77056390027067063766368345)
  ·
    refine ⟨57792292520300297824776259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77056390027067063766368345 57792292520300297824776259)
    ·
      refine ⟨86688438780450446737164389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57792292520300297824776259 86688438780450446737164389)
      ·
        refine ⟨16254082271334458763218323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86688438780450446737164389 16254082271334458763218323)
        ·
          refine ⟨24381123407001688144827485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16254082271334458763218323 24381123407001688144827485)
          ·
            refine ⟨9142921277625633054310307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24381123407001688144827485 9142921277625633054310307)
            ·
              refine ⟨13714381916438449581465461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9142921277625633054310307 13714381916438449581465461)
              ·
                refine ⟨1285723304666104648262387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13714381916438449581465461 1285723304666104648262387)
                ·
                  refine ⟨1928584956999156972393581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285723304666104648262387 1928584956999156972393581)
                  ·
                    refine ⟨723219358874683864647593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928584956999156972393581 723219358874683864647593)
                    ·
                      rfl

theorem cell22_2112697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_2112697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112697 prefixEnd_2112697 := by exact prefixLift 2112697
  have htrace : WordTrace (prefixWord ++ tailWord_2112697) baseStart_2112697 baseEnd_2112697 := by
    simpa [prefixWord, tailWord_2112697, baseEnd_2112697] using wordTrace_append hprefix tailTrace_2112697
  have hstable : (prefixWord ++ tailWord_2112697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112697).length < 2 ^ (prefixWord ++ tailWord_2112697).sum := by decide
  have hdescent : baseEnd_2112697 < baseStart_2112697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112725 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2112725 : Nat := 118140960795 + 2112725 * 2 ^ 59
def prefixEnd_2112725 : Nat := 4983230072969 + 3 ^ 40 * 2112725 * 2
def baseEnd_2112725 : Nat := 723228943846901124947507

theorem tailTrace_2112725 : CollatzResearch.WordTrace tailWord_2112725 prefixEnd_2112725 723228943846901124947507 := by
  unfold tailWord_2112725
  simp only [CollatzResearch.WordTrace]
  refine ⟨77057411270965624548387629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51371607513977083032258419 77057411270965624548387629)
  ·
    refine ⟨28896529226612109205645361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77057411270965624548387629 28896529226612109205645361)
    ·
      refine ⟨21672396919959081904234021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28896529226612109205645361 21672396919959081904234021)
      ·
        refine ⟨4063574422492327857043879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21672396919959081904234021 4063574422492327857043879)
        ·
          refine ⟨6095361633738491785565819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063574422492327857043879 6095361633738491785565819)
          ·
            refine ⟨9143042450607737678348729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6095361633738491785565819 9143042450607737678348729)
            ·
              refine ⟨6857281837955803258761547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9143042450607737678348729 6857281837955803258761547)
              ·
                refine ⟨10285922756933704888142321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6857281837955803258761547 10285922756933704888142321)
                ·
                  refine ⟨7714442067700278666106741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10285922756933704888142321 7714442067700278666106741)
                  ·
                    refine ⟨723228943846901124947507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7714442067700278666106741 723228943846901124947507)
                    ·
                      rfl

theorem cell22_2112725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2112725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112725 prefixEnd_2112725 := by exact prefixLift 2112725
  have htrace : WordTrace (prefixWord ++ tailWord_2112725) baseStart_2112725 baseEnd_2112725 := by
    simpa [prefixWord, tailWord_2112725, baseEnd_2112725] using wordTrace_append hprefix tailTrace_2112725
  have hstable : (prefixWord ++ tailWord_2112725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112725).length < 2 ^ (prefixWord ++ tailWord_2112725).sum := by decide
  have hdescent : baseEnd_2112725 < baseStart_2112725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112740 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_2112740 : Nat := 118140960795 + 2112740 * 2 ^ 59
def prefixEnd_2112740 : Nat := 4983230072969 + 3 ^ 40 * 2112740 * 2
def baseEnd_2112740 : Nat := 723234078653446085822461

theorem tailTrace_2112740 : CollatzResearch.WordTrace tailWord_2112740 prefixEnd_2112740 723234078653446085822461 := by
  unfold tailWord_2112740
  simp only [CollatzResearch.WordTrace]
  refine ⟨38528979182955641055091837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51371972243940854740122449 38528979182955641055091837)
  ·
    refine ⟨14448367193608365395659439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38528979182955641055091837 14448367193608365395659439)
    ·
      refine ⟨21672550790412548093489159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14448367193608365395659439 21672550790412548093489159)
      ·
        refine ⟨32508826185618822140233739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21672550790412548093489159 32508826185618822140233739)
        ·
          refine ⟨48763239278428233210350609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32508826185618822140233739 48763239278428233210350609)
          ·
            refine ⟨36572429458821174907762957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48763239278428233210350609 36572429458821174907762957)
            ·
              refine ⟨13714661047057940590411109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36572429458821174907762957 13714661047057940590411109)
              ·
                refine ⟨2571498946323363860702083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13714661047057940590411109 2571498946323363860702083)
                ·
                  refine ⟨3857248419485045791053125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571498946323363860702083 3857248419485045791053125)
                  ·
                    refine ⟨723234078653446085822461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857248419485045791053125 723234078653446085822461)
                    ·
                      rfl

theorem cell22_2112740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_2112740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112740 prefixEnd_2112740 := by exact prefixLift 2112740
  have htrace : WordTrace (prefixWord ++ tailWord_2112740) baseStart_2112740 baseEnd_2112740 := by
    simpa [prefixWord, tailWord_2112740, baseEnd_2112740] using wordTrace_append hprefix tailTrace_2112740
  have hstable : (prefixWord ++ tailWord_2112740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112740).length < 2 ^ (prefixWord ++ tailWord_2112740).sum := by decide
  have hdescent : baseEnd_2112740 < baseStart_2112740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112753 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2112753 : Nat := 118140960795 + 2112753 * 2 ^ 59
def prefixEnd_2112753 : Nat := 4983230072969 + 3 ^ 40 * 2112753 * 2
def baseEnd_2112753 : Nat := 723238528819118385247421

theorem tailTrace_2112753 : CollatzResearch.WordTrace tailWord_2112753 prefixEnd_2112753 723238528819118385247421 := by
  unfold tailWord_2112753
  simp only [CollatzResearch.WordTrace]
  refine ⟨77058432514864185330406913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51372288343242790220271275 77058432514864185330406913)
  ·
    refine ⟨57793824386148138997805185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77058432514864185330406913 57793824386148138997805185)
    ·
      refine ⟨43345368289611104248353889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57793824386148138997805185 43345368289611104248353889)
      ·
        refine ⟨32509026217208328186265417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43345368289611104248353889 32509026217208328186265417)
        ·
          refine ⟨24381769662906246139699063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32509026217208328186265417 24381769662906246139699063)
          ·
            refine ⟨36572654494359369209548595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24381769662906246139699063 36572654494359369209548595)
            ·
              refine ⟨54858981741539053814322893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36572654494359369209548595 54858981741539053814322893)
              ·
                refine ⟨20572118153077145180371085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54858981741539053814322893 20572118153077145180371085)
                ·
                  refine ⟨7714544307403929442639157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20572118153077145180371085 7714544307403929442639157)
                  ·
                    refine ⟨723238528819118385247421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7714544307403929442639157 723238528819118385247421)
                    ·
                      rfl

theorem cell22_2112753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2112753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112753 prefixEnd_2112753 := by exact prefixLift 2112753
  have htrace : WordTrace (prefixWord ++ tailWord_2112753) baseStart_2112753 baseEnd_2112753 := by
    simpa [prefixWord, tailWord_2112753, baseEnd_2112753] using wordTrace_append hprefix tailTrace_2112753
  have hstable : (prefixWord ++ tailWord_2112753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112753).length < 2 ^ (prefixWord ++ tailWord_2112753).sum := by decide
  have hdescent : baseEnd_2112753 < baseStart_2112753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112772 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_2112772 : Nat := 118140960795 + 2112772 * 2 ^ 59
def prefixEnd_2112772 : Nat := 4983230072969 + 3 ^ 40 * 2112772 * 2
def baseEnd_2112772 : Nat := 241081677635802889674121

theorem tailTrace_2112772 : CollatzResearch.WordTrace tailWord_2112772 prefixEnd_2112772 241081677635802889674121 := by
  unfold tailWord_2112772
  simp only [CollatzResearch.WordTrace]
  refine ⟨38529562750897675787674285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51372750334530234383565713 38529562750897675787674285)
  ·
    refine ⟨14448586031586628420377857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38529562750897675787674285 14448586031586628420377857)
    ·
      refine ⟨10836439523689971315283393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14448586031586628420377857 10836439523689971315283393)
      ·
        refine ⟨8127329642767478486462545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10836439523689971315283393 8127329642767478486462545)
        ·
          refine ⟨6095497232075608864846909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8127329642767478486462545 6095497232075608864846909)
          ·
            refine ⟨2285811462028353324317591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6095497232075608864846909 2285811462028353324317591)
            ·
              refine ⟨3428717193042529986476387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285811462028353324317591 3428717193042529986476387)
              ·
                refine ⟨5143075789563794979714581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3428717193042529986476387 5143075789563794979714581)
                ·
                  refine ⟨241081677635802889674121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5143075789563794979714581 241081677635802889674121)
                  ·
                    rfl

theorem cell22_2112772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_2112772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112772 prefixEnd_2112772 := by exact prefixLift 2112772
  have htrace : WordTrace (prefixWord ++ tailWord_2112772) baseStart_2112772 baseEnd_2112772 := by
    simpa [prefixWord, tailWord_2112772, baseEnd_2112772] using wordTrace_append hprefix tailTrace_2112772
  have hstable : (prefixWord ++ tailWord_2112772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112772).length < 2 ^ (prefixWord ++ tailWord_2112772).sum := by decide
  have hdescent : baseEnd_2112772 < baseStart_2112772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112830 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2112830 : Nat := 118140960795 + 2112830 * 2 ^ 59
def prefixEnd_2112830 : Nat := 4983230072969 + 3 ^ 40 * 2112830 * 2
def baseEnd_2112830 : Nat := 723264887492715851072185

theorem tailTrace_2112830 : CollatzResearch.WordTrace tailWord_2112830 prefixEnd_2112830 723264887492715851072185 := by
  unfold tailWord_2112830
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632655116948153435119993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51374160623723484987306629 9632655116948153435119993)
  ·
    refine ⟨7224491337711115076339995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9632655116948153435119993 7224491337711115076339995)
    ·
      refine ⟨10836737006566672614509993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7224491337711115076339995 10836737006566672614509993)
      ·
        refine ⟨8127552754925004460882495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10836737006566672614509993 8127552754925004460882495)
        ·
          refine ⟨12191329132387506691323743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8127552754925004460882495 12191329132387506691323743)
          ·
            refine ⟨18286993698581260036985615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12191329132387506691323743 18286993698581260036985615)
            ·
              refine ⟨27430490547871890055478423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18286993698581260036985615 27430490547871890055478423)
              ·
                refine ⟨41145735821807835083217635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27430490547871890055478423 41145735821807835083217635)
                ·
                  refine ⟨61718603732711752624826453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41145735821807835083217635 61718603732711752624826453)
                  ·
                    refine ⟨723264887492715851072185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61718603732711752624826453 723264887492715851072185)
                    ·
                      rfl

theorem cell22_2112830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2112830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112830 prefixEnd_2112830 := by exact prefixLift 2112830
  have htrace : WordTrace (prefixWord ++ tailWord_2112830) baseStart_2112830 baseEnd_2112830 := by
    simpa [prefixWord, tailWord_2112830, baseEnd_2112830] using wordTrace_append hprefix tailTrace_2112830
  have hstable : (prefixWord ++ tailWord_2112830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112830).length < 2 ^ (prefixWord ++ tailWord_2112830).sum := by decide
  have hdescent : baseEnd_2112830 < baseStart_2112830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112866 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2112866 : Nat := 118140960795 + 2112866 * 2 ^ 59
def prefixEnd_2112866 : Nat := 4983230072969 + 3 ^ 40 * 2112866 * 2
def baseEnd_2112866 : Nat := 723277211028423757172075

theorem tailTrace_2112866 : CollatzResearch.WordTrace tailWord_2112866 prefixEnd_2112866 723277211028423757172075 := by
  unfold tailWord_2112866
  simp only [CollatzResearch.WordTrace]
  refine ⟨19265638490863701407317613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51375035975636537086180301 19265638490863701407317613)
  ·
    refine ⟨7224614434073888027744105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19265638490863701407317613 7224614434073888027744105)
    ·
      refine ⟨5418460825555416020808079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7224614434073888027744105 5418460825555416020808079)
      ·
        refine ⟨8127691238333124031212119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5418460825555416020808079 8127691238333124031212119)
        ·
          refine ⟨12191536857499686046818179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8127691238333124031212119 12191536857499686046818179)
          ·
            refine ⟨18287305286249529070227269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12191536857499686046818179 18287305286249529070227269)
            ·
              refine ⟨3428869741171786700667613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18287305286249529070227269 3428869741171786700667613)
              ·
                refine ⟨1285826152939420012750355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3428869741171786700667613 1285826152939420012750355)
                ·
                  refine ⟨1928739229409130019125533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285826152939420012750355 1928739229409130019125533)
                  ·
                    refine ⟨723277211028423757172075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928739229409130019125533 723277211028423757172075)
                    ·
                      rfl

theorem cell22_2112866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2112866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112866 prefixEnd_2112866 := by exact prefixLift 2112866
  have htrace : WordTrace (prefixWord ++ tailWord_2112866) baseStart_2112866 baseEnd_2112866 := by
    simpa [prefixWord, tailWord_2112866, baseEnd_2112866] using wordTrace_append hprefix tailTrace_2112866
  have hstable : (prefixWord ++ tailWord_2112866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112866).length < 2 ^ (prefixWord ++ tailWord_2112866).sum := by decide
  have hdescent : baseEnd_2112866 < baseStart_2112866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112922 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_2112922 : Nat := 118140960795 + 2112922 * 2 ^ 59
def prefixEnd_2112922 : Nat := 4983230072969 + 3 ^ 40 * 2112922 * 2
def baseEnd_2112922 : Nat := 723296380972858277771903

theorem tailTrace_2112922 : CollatzResearch.WordTrace tailWord_2112922 prefixEnd_2112922 723296380972858277771903 := by
  unfold tailWord_2112922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19266149112812981798327255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51376397634167951462206013 19266149112812981798327255)
  ·
    refine ⟨28899223669219472697490883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19266149112812981798327255 28899223669219472697490883)
    ·
      refine ⟨43348835503829209046236325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28899223669219472697490883 43348835503829209046236325)
      ·
        refine ⟨8127906656967976696169311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43348835503829209046236325 8127906656967976696169311)
        ·
          refine ⟨12191859985451965044253967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8127906656967976696169311 12191859985451965044253967)
          ·
            refine ⟨18287789978177947566380951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12191859985451965044253967 18287789978177947566380951)
            ·
              refine ⟨27431684967266921349571427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18287789978177947566380951 27431684967266921349571427)
              ·
                refine ⟨41147527450900382024357141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27431684967266921349571427 41147527450900382024357141)
                ·
                  refine ⟨1928790349260955407391741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41147527450900382024357141 1928790349260955407391741)
                  ·
                    refine ⟨723296380972858277771903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928790349260955407391741 723296380972858277771903)
                    ·
                      rfl

theorem cell22_2112922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_2112922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112922 prefixEnd_2112922 := by exact prefixLift 2112922
  have htrace : WordTrace (prefixWord ++ tailWord_2112922) baseStart_2112922 baseEnd_2112922 := by
    simpa [prefixWord, tailWord_2112922, baseEnd_2112922] using wordTrace_append hprefix tailTrace_2112922
  have hstable : (prefixWord ++ tailWord_2112922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112922).length < 2 ^ (prefixWord ++ tailWord_2112922).sum := by decide
  have hdescent : baseEnd_2112922 < baseStart_2112922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112956 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_2112956 : Nat := 118140960795 + 2112956 * 2 ^ 59
def prefixEnd_2112956 : Nat := 4983230072969 + 3 ^ 40 * 2112956 * 2
def baseEnd_2112956 : Nat := 723308019867693522421799

theorem tailTrace_2112956 : CollatzResearch.WordTrace tailWord_2112956 prefixEnd_2112956 723308019867693522421799 := by
  unfold tailWord_2112956
  simp only [CollatzResearch.WordTrace]
  refine ⟨38532918266564375500023361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 51377224355419167333364481 38532918266564375500023361)
  ·
    refine ⟨28899688699923281625017521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38532918266564375500023361 28899688699923281625017521)
    ·
      refine ⟨21674766524942461218763141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28899688699923281625017521 21674766524942461218763141)
      ·
        refine ⟨4064018723426711478518089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21674766524942461218763141 4064018723426711478518089)
        ·
          refine ⟨3048014042570033608888567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4064018723426711478518089 3048014042570033608888567)
          ·
            refine ⟨4572021063855050413332851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048014042570033608888567 4572021063855050413332851)
            ·
              refine ⟨6858031595782575619999277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572021063855050413332851 6858031595782575619999277)
              ·
                refine ⟨2571761848418465857499729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6858031595782575619999277 2571761848418465857499729)
                ·
                  refine ⟨1928821386313849393124797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2571761848418465857499729 1928821386313849393124797)
                  ·
                    refine ⟨723308019867693522421799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928821386313849393124797 723308019867693522421799)
                    ·
                      rfl

theorem cell22_2112956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_2112956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112956 prefixEnd_2112956 := by exact prefixLift 2112956
  have htrace : WordTrace (prefixWord ++ tailWord_2112956) baseStart_2112956 baseEnd_2112956 := by
    simpa [prefixWord, tailWord_2112956, baseEnd_2112956] using wordTrace_append hprefix tailTrace_2112956
  have hstable : (prefixWord ++ tailWord_2112956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112956).length < 2 ^ (prefixWord ++ tailWord_2112956).sum := by decide
  have hdescent : baseEnd_2112956 < baseStart_2112956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2112967 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2112967 : Nat := 118140960795 + 2112967 * 2 ^ 59
def prefixEnd_2112967 : Nat := 4983230072969 + 3 ^ 40 * 2112967 * 2
def baseEnd_2112967 : Nat := 723311785392493160396765

theorem tailTrace_2112967 : CollatzResearch.WordTrace tailWord_2112967 prefixEnd_2112967 723311785392493160396765 := by
  unfold tailWord_2112967
  simp only [CollatzResearch.WordTrace]
  refine ⟨77066237736088899878697155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51377491824059266585798103 77066237736088899878697155)
  ·
    refine ⟨115599356604133349818045733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77066237736088899878697155 115599356604133349818045733)
    ·
      refine ⟨21674879363275003090883575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115599356604133349818045733 21674879363275003090883575)
      ·
        refine ⟨32512319044912504636325363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21674879363275003090883575 32512319044912504636325363)
        ·
          refine ⟨48768478567368756954488045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32512319044912504636325363 48768478567368756954488045)
          ·
            refine ⟨18288179462763283857933017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48768478567368756954488045 18288179462763283857933017)
            ·
              refine ⟨13716134597072462893449763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18288179462763283857933017 13716134597072462893449763)
              ·
                refine ⟨20574201895608694340174645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13716134597072462893449763 20574201895608694340174645)
                ·
                  refine ⟨1928831427713315094391373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20574201895608694340174645 1928831427713315094391373)
                  ·
                    refine ⟨723311785392493160396765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1928831427713315094391373 723311785392493160396765)
                    ·
                      rfl

theorem cell22_2112967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2112967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2112967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2112967 prefixEnd_2112967 := by exact prefixLift 2112967
  have htrace : WordTrace (prefixWord ++ tailWord_2112967) baseStart_2112967 baseEnd_2112967 := by
    simpa [prefixWord, tailWord_2112967, baseEnd_2112967] using wordTrace_append hprefix tailTrace_2112967
  have hstable : (prefixWord ++ tailWord_2112967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2112967).length < 2 ^ (prefixWord ++ tailWord_2112967).sum := by decide
  have hdescent : baseEnd_2112967 < baseStart_2112967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2112967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113014 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_2113014 : Nat := 118140960795 + 2113014 * 2 ^ 59
def prefixEnd_2113014 : Nat := 4983230072969 + 3 ^ 40 * 2113014 * 2
def baseEnd_2113014 : Nat := 241109291484333568157207

theorem tailTrace_2113014 : CollatzResearch.WordTrace tailWord_2113014 prefixEnd_2113014 241109291484333568157207 := by
  unfold tailWord_2113014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816746997932414181603631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51378634644612417937105397 4816746997932414181603631)
  ·
    refine ⟨7225120496898621272405447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4816746997932414181603631 7225120496898621272405447)
    ·
      refine ⟨10837680745347931908608171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7225120496898621272405447 10837680745347931908608171)
      ·
        refine ⟨16256521118021897862912257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10837680745347931908608171 16256521118021897862912257)
        ·
          refine ⟨12192390838516423397184193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16256521118021897862912257 12192390838516423397184193)
          ·
            refine ⟨9144293128887317547888145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12192390838516423397184193 9144293128887317547888145)
            ·
              refine ⟨6858219846665488160916109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9144293128887317547888145 6858219846665488160916109)
              ·
                refine ⟨2571832442499558060343541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6858219846665488160916109 2571832442499558060343541)
                ·
                  refine ⟨241109291484333568157207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2571832442499558060343541 241109291484333568157207)
                  ·
                    rfl

theorem cell22_2113014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_2113014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113014 prefixEnd_2113014 := by exact prefixLift 2113014
  have htrace : WordTrace (prefixWord ++ tailWord_2113014) baseStart_2113014 baseEnd_2113014 := by
    simpa [prefixWord, tailWord_2113014, baseEnd_2113014] using wordTrace_append hprefix tailTrace_2113014
  have hstable : (prefixWord ++ tailWord_2113014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113014).length < 2 ^ (prefixWord ++ tailWord_2113014).sum := by decide
  have hdescent : baseEnd_2113014 < baseStart_2113014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113059 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 6]
def baseStart_2113059 : Nat := 118140960795 + 2113059 * 2 ^ 59
def prefixEnd_2113059 : Nat := 4983230072969 + 3 ^ 40 * 2113059 * 2
def baseEnd_2113059 : Nat := 241114426290878529032161

theorem tailTrace_2113059 : CollatzResearch.WordTrace tailWord_2113059 prefixEnd_2113059 241114426290878529032161 := by
  unfold tailWord_2113059
  simp only [CollatzResearch.WordTrace]
  refine ⟨77069593251755599591046231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51379728834503733060697487 77069593251755599591046231)
  ·
    refine ⟨115604389877633399386569347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77069593251755599591046231 115604389877633399386569347)
    ·
      refine ⟨173406584816450099079854021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115604389877633399386569347 173406584816450099079854021)
      ·
        refine ⟨32513734653084393577472629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173406584816450099079854021 32513734653084393577472629)
        ·
          refine ⟨3048162623726661897888059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32513734653084393577472629 3048162623726661897888059)
          ·
            refine ⟨4572243935589992846832089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048162623726661897888059 4572243935589992846832089)
            ·
              refine ⟨3429182951692494635124067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572243935589992846832089 3429182951692494635124067)
              ·
                refine ⟨5143774427538741952686101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429182951692494635124067 5143774427538741952686101)
                ·
                  refine ⟨241114426290878529032161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5143774427538741952686101 241114426290878529032161)
                  ·
                    rfl

theorem cell22_2113059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 6].length) (baseStart_2113059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113059 prefixEnd_2113059 := by exact prefixLift 2113059
  have htrace : WordTrace (prefixWord ++ tailWord_2113059) baseStart_2113059 baseEnd_2113059 := by
    simpa [prefixWord, tailWord_2113059, baseEnd_2113059] using wordTrace_append hprefix tailTrace_2113059
  have hstable : (prefixWord ++ tailWord_2113059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113059).length < 2 ^ (prefixWord ++ tailWord_2113059).sum := by decide
  have hdescent : baseEnd_2113059 < baseStart_2113059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113078 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2113078 : Nat := 118140960795 + 2113078 * 2 ^ 59
def prefixEnd_2113078 : Nat := 4983230072969 + 3 ^ 40 * 2113078 * 2
def baseEnd_2113078 : Nat := 723349782960925870871425

theorem tailTrace_2113078 : CollatzResearch.WordTrace tailWord_2113078 prefixEnd_2113078 723349782960925870871425 := by
  unfold tailWord_2113078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816892889917922864749243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51380190825791177223991925 4816892889917922864749243)
  ·
    refine ⟨7225339334876884297123865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4816892889917922864749243 7225339334876884297123865)
    ·
      refine ⟨5419004501157663222842899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7225339334876884297123865 5419004501157663222842899)
      ·
        refine ⟨8128506751736494834264349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419004501157663222842899 8128506751736494834264349)
        ·
          refine ⟨3048190031901185562849131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8128506751736494834264349 3048190031901185562849131)
          ·
            refine ⟨4572285047851778344273697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048190031901185562849131 4572285047851778344273697)
            ·
              refine ⟨3429213785888833758205273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572285047851778344273697 3429213785888833758205273)
              ·
                refine ⟨2571910339416625318653955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429213785888833758205273 2571910339416625318653955)
                ·
                  refine ⟨3857865509124937977980933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2571910339416625318653955 3857865509124937977980933)
                  ·
                    refine ⟨723349782960925870871425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857865509124937977980933 723349782960925870871425)
                    ·
                      rfl

theorem cell22_2113078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2113078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113078 prefixEnd_2113078 := by exact prefixLift 2113078
  have htrace : WordTrace (prefixWord ++ tailWord_2113078) baseStart_2113078 baseEnd_2113078 := by
    simpa [prefixWord, tailWord_2113078, baseEnd_2113078] using wordTrace_append hprefix tailTrace_2113078
  have hstable : (prefixWord ++ tailWord_2113078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113078).length < 2 ^ (prefixWord ++ tailWord_2113078).sum := by decide
  have hdescent : baseEnd_2113078 < baseStart_2113078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113087 : List Nat := [1, 1, 2, 2, 3, 4, 1, 8]
def baseStart_2113087 : Nat := 118140960795 + 2113087 * 2 ^ 59
def prefixEnd_2113087 : Nat := 4983230072969 + 3 ^ 40 * 2113087 * 2
def baseEnd_2113087 : Nat := 80372540427205871932933

theorem tailTrace_2113087 : CollatzResearch.WordTrace tailWord_2113087 prefixEnd_2113087 80372540427205871932933 := by
  unfold tailWord_2113087
  simp only [CollatzResearch.WordTrace]
  refine ⟨77070614495654160373065515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51380409663769440248710343 77070614495654160373065515)
  ·
    refine ⟨115605921743481240559598273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77070614495654160373065515 115605921743481240559598273)
    ·
      refine ⟨86704441307610930419698705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115605921743481240559598273 86704441307610930419698705)
      ·
        refine ⟨65028330980708197814774029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86704441307610930419698705 65028330980708197814774029)
        ·
          refine ⟨24385624117765574180540261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65028330980708197814774029 24385624117765574180540261)
          ·
            refine ⟨4572304522081045158851299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24385624117765574180540261 4572304522081045158851299)
            ·
              refine ⟨6858456783121567738276949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572304522081045158851299 6858456783121567738276949)
              ·
                refine ⟨80372540427205871932933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6858456783121567738276949 80372540427205871932933)
                ·
                  rfl

theorem cell22_2113087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 8].length) (baseStart_2113087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113087 prefixEnd_2113087 := by exact prefixLift 2113087
  have htrace : WordTrace (prefixWord ++ tailWord_2113087) baseStart_2113087 baseEnd_2113087 := by
    simpa [prefixWord, tailWord_2113087, baseEnd_2113087] using wordTrace_append hprefix tailTrace_2113087
  have hstable : (prefixWord ++ tailWord_2113087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113087).length < 2 ^ (prefixWord ++ tailWord_2113087).sum := by decide
  have hdescent : baseEnd_2113087 < baseStart_2113087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113089 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2113089 : Nat := 118140960795 + 2113089 * 2 ^ 59
def prefixEnd_2113089 : Nat := 4983230072969 + 3 ^ 40 * 2113089 * 2
def baseEnd_2113089 : Nat := 723353548485725508846391

theorem tailTrace_2113089 : CollatzResearch.WordTrace tailWord_2113089 prefixEnd_2113089 723353548485725508846391 := by
  unfold tailWord_2113089
  simp only [CollatzResearch.WordTrace]
  refine ⟨77070687441646914714638321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 51380458294431276476425547 77070687441646914714638321)
  ·
    refine ⟨57803015581235186035978741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77070687441646914714638321 57803015581235186035978741)
    ·
      refine ⟨5419032710740798690873007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57803015581235186035978741 5419032710740798690873007)
      ·
        refine ⟨8128549066111198036309511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419032710740798690873007 8128549066111198036309511)
        ·
          refine ⟨12192823599166797054464267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128549066111198036309511 12192823599166797054464267)
          ·
            refine ⟨18289235398750195581696401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12192823599166797054464267 18289235398750195581696401)
            ·
              refine ⟨13716926549062646686272301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18289235398750195581696401 13716926549062646686272301)
              ·
                refine ⟨5143847455898492507352113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13716926549062646686272301 5143847455898492507352113)
                ·
                  refine ⟨3857885591923869380514085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5143847455898492507352113 3857885591923869380514085)
                  ·
                    refine ⟨723353548485725508846391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3857885591923869380514085 723353548485725508846391)
                    ·
                      rfl

theorem cell22_2113089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2113089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113089 prefixEnd_2113089 := by exact prefixLift 2113089
  have htrace : WordTrace (prefixWord ++ tailWord_2113089) baseStart_2113089 baseEnd_2113089 := by
    simpa [prefixWord, tailWord_2113089, baseEnd_2113089] using wordTrace_append hprefix tailTrace_2113089
  have hstable : (prefixWord ++ tailWord_2113089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113089).length < 2 ^ (prefixWord ++ tailWord_2113089).sum := by decide
  have hdescent : baseEnd_2113089 < baseStart_2113089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113110 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_2113110 : Nat := 118140960795 + 2113110 * 2 ^ 59
def prefixEnd_2113110 : Nat := 4983230072969 + 3 ^ 40 * 2113110 * 2
def baseEnd_2113110 : Nat := 241120245738296151357109

theorem tailTrace_2113110 : CollatzResearch.WordTrace tailWord_2113110 prefixEnd_2113110 241120245738296151357109 := by
  unfold tailWord_2113110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4816965835910677206322049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 51380968916380556867435189 4816965835910677206322049)
  ·
    refine ⟨3612724376933007904741537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4816965835910677206322049 3612724376933007904741537)
    ·
      refine ⟨2709543282699755928556153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3612724376933007904741537 2709543282699755928556153)
      ·
        refine ⟨2032157462024816946417115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2709543282699755928556153 2032157462024816946417115)
        ·
          refine ⟨3048236193037225419625673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2032157462024816946417115 3048236193037225419625673)
          ·
            refine ⟨2286177144777919064719255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3048236193037225419625673 2286177144777919064719255)
            ·
              refine ⟨3429265717166878597078883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2286177144777919064719255 3429265717166878597078883)
              ·
                refine ⟨5143898575750317895618325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3429265717166878597078883 5143898575750317895618325)
                ·
                  refine ⟨241120245738296151357109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5143898575750317895618325 241120245738296151357109)
                  ·
                    rfl

theorem cell22_2113110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_2113110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113110 prefixEnd_2113110 := by exact prefixLift 2113110
  have htrace : WordTrace (prefixWord ++ tailWord_2113110) baseStart_2113110 baseEnd_2113110 := by
    simpa [prefixWord, tailWord_2113110, baseEnd_2113110] using wordTrace_append hprefix tailTrace_2113110
  have hstable : (prefixWord ++ tailWord_2113110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113110).length < 2 ^ (prefixWord ++ tailWord_2113110).sum := by decide
  have hdescent : baseEnd_2113110 < baseStart_2113110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113166 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_2113166 : Nat := 118140960795 + 2113166 * 2 ^ 59
def prefixEnd_2113166 : Nat := 4983230072969 + 3 ^ 40 * 2113166 * 2
def baseEnd_2113166 : Nat := 241126635719774324890385

theorem tailTrace_2113166 : CollatzResearch.WordTrace tailWord_2113166 prefixEnd_2113166 241126635719774324890385 := by
  unfold tailWord_2113166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9634186982795994608148919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 51382330574911971243460901 9634186982795994608148919)
  ·
    refine ⟨14451280474193991912223379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9634186982795994608148919 14451280474193991912223379)
    ·
      refine ⟨21676920711290987868335069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14451280474193991912223379 21676920711290987868335069)
      ·
        refine ⟨8128845266734120450625651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21676920711290987868335069 8128845266734120450625651)
        ·
          refine ⟨12193267900101180675938477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8128845266734120450625651 12193267900101180675938477)
          ·
            refine ⟨4572475462537942753476929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12193267900101180675938477 4572475462537942753476929)
            ·
              refine ⟨3429356596903457065107697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4572475462537942753476929 3429356596903457065107697)
              ·
                refine ⟨2572017447677592798830773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3429356596903457065107697 2572017447677592798830773)
                ·
                  refine ⟨241126635719774324890385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2572017447677592798830773 241126635719774324890385)
                  ·
                    rfl

theorem cell22_2113166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_2113166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113166 prefixEnd_2113166 := by exact prefixLift 2113166
  have htrace : WordTrace (prefixWord ++ tailWord_2113166) baseStart_2113166 baseEnd_2113166 := by
    simpa [prefixWord, tailWord_2113166, baseEnd_2113166] using wordTrace_append hprefix tailTrace_2113166
  have hstable : (prefixWord ++ tailWord_2113166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113166).length < 2 ^ (prefixWord ++ tailWord_2113166).sum := by decide
  have hdescent : baseEnd_2113166 < baseStart_2113166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2113170 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_2113170 : Nat := 118140960795 + 2113170 * 2 ^ 59
def prefixEnd_2113170 : Nat := 4983230072969 + 3 ^ 40 * 2113170 * 2
def baseEnd_2113170 : Nat := 723381276441068297571143

theorem tailTrace_2113170 : CollatzResearch.WordTrace tailWord_2113170 prefixEnd_2113170 723381276441068297571143 := by
  unfold tailWord_2113170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19268410438588366387084241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 51382427836235643698891309 19268410438588366387084241)
  ·
    refine ⟨14451307828941274790313181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19268410438588366387084241 14451307828941274790313181)
    ·
      refine ⟨5419240435852978046367443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14451307828941274790313181 5419240435852978046367443)
      ·
        refine ⟨8128860653779467069551165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5419240435852978046367443 8128860653779467069551165)
        ·
          refine ⟨3048322745167300151081687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8128860653779467069551165 3048322745167300151081687)
          ·
            refine ⟨4572484117750950226622531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3048322745167300151081687 4572484117750950226622531)
            ·
              refine ⟨6858726176626425339933797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4572484117750950226622531 6858726176626425339933797)
              ·
                refine ⟨1286011158117454751237587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6858726176626425339933797 1286011158117454751237587)
                ·
                  refine ⟨1929016737176182126856381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1286011158117454751237587 1929016737176182126856381)
                  ·
                    refine ⟨723381276441068297571143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1929016737176182126856381 723381276441068297571143)
                    ·
                      rfl

theorem cell22_2113170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_2113170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2113170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2113170 prefixEnd_2113170 := by exact prefixLift 2113170
  have htrace : WordTrace (prefixWord ++ tailWord_2113170) baseStart_2113170 baseEnd_2113170 := by
    simpa [prefixWord, tailWord_2113170, baseEnd_2113170] using wordTrace_append hprefix tailTrace_2113170
  have hstable : (prefixWord ++ tailWord_2113170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2113170).length < 2 ^ (prefixWord ++ tailWord_2113170).sum := by decide
  have hdescent : baseEnd_2113170 < baseStart_2113170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2113170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
