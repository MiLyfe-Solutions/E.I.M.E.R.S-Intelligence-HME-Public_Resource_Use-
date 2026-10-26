import V185TrunkScan22Chunk041

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_375826 : List Nat := [3, 2, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_375826 : Nat := 118140960795 + 375826 * 2 ^ 59
def prefixEnd_375826 : Nat := 4983230072969 + 3 ^ 40 * 375826 * 2
def baseEnd_375826 : Nat := 128652920304501208497743

theorem tailTrace_375826 : CollatzResearch.WordTrace tailWord_375826 prefixEnd_375826 128652920304501208497743 := by
  unfold tailWord_375826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3426875084113515703950833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9138333557636041877202221 3426875084113515703950833)
  ·
    refine ⟨2570156313085136777963125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3426875084113515703950833 2570156313085136777963125)
    ·
      refine ⟨240952154351731572934043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2570156313085136777963125 240952154351731572934043)
      ·
        refine ⟨361428231527597359401065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240952154351731572934043 361428231527597359401065)
        ·
          refine ⟨271071173645698019550799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361428231527597359401065 271071173645698019550799)
          ·
            refine ⟨406606760468547029326199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271071173645698019550799 406606760468547029326199)
            ·
              refine ⟨609910140702820543989299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406606760468547029326199 609910140702820543989299)
              ·
                refine ⟨914865211054230815983949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609910140702820543989299 914865211054230815983949)
                ·
                  refine ⟨343074454145336555993981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 914865211054230815983949 343074454145336555993981)
                  ·
                    refine ⟨128652920304501208497743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343074454145336555993981 128652920304501208497743)
                    ·
                      rfl

theorem cell22_375826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_375826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375826 prefixEnd_375826 := by exact prefixLift 375826
  have htrace : WordTrace (prefixWord ++ tailWord_375826) baseStart_375826 baseEnd_375826 := by
    simpa [prefixWord, tailWord_375826, baseEnd_375826] using wordTrace_append hprefix tailTrace_375826
  have hstable : (prefixWord ++ tailWord_375826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375826).length < 2 ^ (prefixWord ++ tailWord_375826).sum := by decide
  have hdescent : baseEnd_375826 < baseStart_375826 := by decide
  rcases family_descends (prefixWord ++ tailWord_375826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375878 : List Nat := [6, 1, 1, 1, 1, 12]
def baseStart_375878 : Nat := 118140960795 + 375878 * 2 ^ 59
def prefixEnd_375878 : Nat := 4983230072969 + 3 ^ 40 * 375878 * 2
def baseEnd_375878 : Nat := 1588527419348029706143

theorem tailTrace_375878 : CollatzResearch.WordTrace tailWord_375878 prefixEnd_375878 1588527419348029706143 := by
  unfold tailWord_375878
  simp only [CollatzResearch.WordTrace]
  refine ⟨428418654133302365521759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9139597954843783797797525 428418654133302365521759)
  ·
    refine ⟨642627981199953548282639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428418654133302365521759 642627981199953548282639)
    ·
      refine ⟨963941971799930322423959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642627981199953548282639 963941971799930322423959)
      ·
        refine ⟨1445912957699895483635939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963941971799930322423959 1445912957699895483635939)
        ·
          refine ⟨2168869436549843225453909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1445912957699895483635939 2168869436549843225453909)
          ·
            refine ⟨1588527419348029706143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2168869436549843225453909 1588527419348029706143)
            ·
              rfl

theorem cell22_375878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 12].length) (baseStart_375878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375878 prefixEnd_375878 := by exact prefixLift 375878
  have htrace : WordTrace (prefixWord ++ tailWord_375878) baseStart_375878 baseEnd_375878 := by
    simpa [prefixWord, tailWord_375878, baseEnd_375878] using wordTrace_append hprefix tailTrace_375878
  have hstable : (prefixWord ++ tailWord_375878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375878).length < 2 ^ (prefixWord ++ tailWord_375878).sum := by decide
  have hdescent : baseEnd_375878 < baseStart_375878 := by decide
  rcases family_descends (prefixWord ++ tailWord_375878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375893 : List Nat := [1, 3, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_375893 : Nat := 118140960795 + 375893 * 2 ^ 59
def prefixEnd_375893 : Nat := 4983230072969 + 3 ^ 40 * 375893 * 2
def baseEnd_375893 : Nat := 128675855773735367072537

theorem tailTrace_375893 : CollatzResearch.WordTrace tailWord_375893 prefixEnd_375893 128675855773735367072537 := by
  unfold tailWord_375893
  simp only [CollatzResearch.WordTrace]
  refine ⟨13709944027211333258492333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9139962684807555505661555 13709944027211333258492333)
  ·
    refine ⟨5141229010204249971934625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13709944027211333258492333 5141229010204249971934625)
    ·
      refine ⟨3855921757653187478950969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5141229010204249971934625 3855921757653187478950969)
      ·
        refine ⟨2891941318239890609213227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3855921757653187478950969 2891941318239890609213227)
        ·
          refine ⟨4337911977359835913819841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2891941318239890609213227 4337911977359835913819841)
          ·
            refine ⟨3253433983019876935364881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4337911977359835913819841 3253433983019876935364881)
            ·
              refine ⟨2440075487264907701523661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3253433983019876935364881 2440075487264907701523661)
              ·
                refine ⟨915028307724340388071373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2440075487264907701523661 915028307724340388071373)
                ·
                  refine ⟨343135615396627645526765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 915028307724340388071373 343135615396627645526765)
                  ·
                    refine ⟨128675855773735367072537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343135615396627645526765 128675855773735367072537)
                    ·
                      rfl

theorem cell22_375893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_375893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375893 prefixEnd_375893 := by exact prefixLift 375893
  have htrace : WordTrace (prefixWord ++ tailWord_375893) baseStart_375893 baseEnd_375893 := by
    simpa [prefixWord, tailWord_375893, baseEnd_375893] using wordTrace_append hprefix tailTrace_375893
  have hstable : (prefixWord ++ tailWord_375893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375893).length < 2 ^ (prefixWord ++ tailWord_375893).sum := by decide
  have hdescent : baseEnd_375893 < baseStart_375893 := by decide
  rcases family_descends (prefixWord ++ tailWord_375893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375940 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_375940 : Nat := 118140960795 + 375940 * 2 ^ 59
def prefixEnd_375940 : Nat := 4983230072969 + 3 ^ 40 * 375940 * 2
def baseEnd_375940 : Nat := 42897314944747637049131

theorem tailTrace_375940 : CollatzResearch.WordTrace tailWord_375940 prefixEnd_375940 42897314944747637049131 := by
  unfold tailWord_375940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6855829129020530142726637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9141105505360706856968849 6855829129020530142726637)
  ·
    refine ⟨2570935923382698803522489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6855829129020530142726637 2570935923382698803522489)
    ·
      refine ⟨1928201942537024102641867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2570935923382698803522489 1928201942537024102641867)
      ·
        refine ⟨2892302913805536153962801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928201942537024102641867 2892302913805536153962801)
        ·
          refine ⟨2169227185354152115472101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892302913805536153962801 2169227185354152115472101)
          ·
            refine ⟨406730097253903521651019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2169227185354152115472101 406730097253903521651019)
            ·
              refine ⟨610095145880855282476529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406730097253903521651019 610095145880855282476529)
              ·
                refine ⟨457571359410641461857397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610095145880855282476529 457571359410641461857397)
                ·
                  refine ⟨42897314944747637049131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457571359410641461857397 42897314944747637049131)
                  ·
                    rfl

theorem cell22_375940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_375940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375940 prefixEnd_375940 := by exact prefixLift 375940
  have htrace : WordTrace (prefixWord ++ tailWord_375940) baseStart_375940 baseEnd_375940 := by
    simpa [prefixWord, tailWord_375940, baseEnd_375940] using wordTrace_append hprefix tailTrace_375940
  have hstable : (prefixWord ++ tailWord_375940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375940).length < 2 ^ (prefixWord ++ tailWord_375940).sum := by decide
  have hdescent : baseEnd_375940 < baseStart_375940 := by decide
  rcases family_descends (prefixWord ++ tailWord_375940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_375983 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 4, 3]
def baseStart_375983 : Nat := 118140960795 + 375983 * 2 ^ 59
def prefixEnd_375983 : Nat := 4983230072969 + 3 ^ 40 * 375983 * 2
def baseEnd_375983 : Nat := 128706664613005132322261

theorem tailTrace_375983 : CollatzResearch.WordTrace tailWord_375983 prefixEnd_375983 128706664613005132322261 := by
  unfold tailWord_375983
  simp only [CollatzResearch.WordTrace]
  refine ⟨13713226596885278629268603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9142151064590185752845735 13713226596885278629268603)
  ·
    refine ⟨20569839895327917943902905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13713226596885278629268603 20569839895327917943902905)
    ·
      refine ⟨15427379921495938457927179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20569839895327917943902905 15427379921495938457927179)
      ·
        refine ⟨23141069882243907686890769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15427379921495938457927179 23141069882243907686890769)
        ·
          refine ⟨17355802411682930765168077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23141069882243907686890769 17355802411682930765168077)
          ·
            refine ⟨6508425904381099036938029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17355802411682930765168077 6508425904381099036938029)
            ·
              refine ⟨2440659714142912138851761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6508425904381099036938029 2440659714142912138851761)
              ·
                refine ⟨1830494785607184104138821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2440659714142912138851761 1830494785607184104138821)
                ·
                  refine ⟨343217772301347019526029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1830494785607184104138821 343217772301347019526029)
                  ·
                    refine ⟨128706664613005132322261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343217772301347019526029 128706664613005132322261)
                    ·
                      rfl

theorem cell22_375983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_375983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_375983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_375983 prefixEnd_375983 := by exact prefixLift 375983
  have htrace : WordTrace (prefixWord ++ tailWord_375983) baseStart_375983 baseEnd_375983 := by
    simpa [prefixWord, tailWord_375983, baseEnd_375983] using wordTrace_append hprefix tailTrace_375983
  have hstable : (prefixWord ++ tailWord_375983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_375983).length < 2 ^ (prefixWord ++ tailWord_375983).sum := by decide
  have hdescent : baseEnd_375983 < baseStart_375983 := by decide
  rcases family_descends (prefixWord ++ tailWord_375983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376011 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_376011 : Nat := 118140960795 + 376011 * 2 ^ 59
def prefixEnd_376011 : Nat := 4983230072969 + 3 ^ 40 * 376011 * 2
def baseEnd_376011 : Nat := 128716249585222392622175

theorem tailTrace_376011 : CollatzResearch.WordTrace tailWord_376011 prefixEnd_376011 128716249585222392622175 := by
  unfold tailWord_376011
  simp only [CollatzResearch.WordTrace]
  refine ⟨13714247840783839411287887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9142831893855892940858591 13714247840783839411287887)
  ·
    refine ⟨20571371761175759116931831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13714247840783839411287887 20571371761175759116931831)
    ·
      refine ⟨30857057641763638675397747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20571371761175759116931831 30857057641763638675397747)
      ·
        refine ⟨46285586462645458013096621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30857057641763638675397747 46285586462645458013096621)
        ·
          refine ⟨17357094923492046754911233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46285586462645458013096621 17357094923492046754911233)
          ·
            refine ⟨13017821192619035066183425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17357094923492046754911233 13017821192619035066183425)
            ·
              refine ⟨9763365894464276299637569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13017821192619035066183425 9763365894464276299637569)
              ·
                refine ⟨7322524420848207224728177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9763365894464276299637569 7322524420848207224728177)
                ·
                  refine ⟨5491893315636155418546133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7322524420848207224728177 5491893315636155418546133)
                  ·
                    refine ⟨128716249585222392622175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5491893315636155418546133 128716249585222392622175)
                    ·
                      rfl

theorem cell22_376011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_376011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376011 prefixEnd_376011 := by exact prefixLift 376011
  have htrace : WordTrace (prefixWord ++ tailWord_376011) baseStart_376011 baseEnd_376011 := by
    simpa [prefixWord, tailWord_376011, baseEnd_376011] using wordTrace_append hprefix tailTrace_376011
  have hstable : (prefixWord ++ tailWord_376011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376011).length < 2 ^ (prefixWord ++ tailWord_376011).sum := by decide
  have hdescent : baseEnd_376011 < baseStart_376011 := by decide
  rcases family_descends (prefixWord ++ tailWord_376011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376073 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_376073 : Nat := 118140960795 + 376073 * 2 ^ 59
def prefixEnd_376073 : Nat := 4983230072969 + 3 ^ 40 * 376073 * 2
def baseEnd_376073 : Nat := 128737473452274897571985

theorem tailTrace_376073 : CollatzResearch.WordTrace tailWord_376073 prefixEnd_376073 128737473452274897571985 := by
  unfold tailWord_376073
  simp only [CollatzResearch.WordTrace]
  refine ⟨13716509166559224000044873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9144339444372816000029915 13716509166559224000044873)
  ·
    refine ⟨10287381874919418000033655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13716509166559224000044873 10287381874919418000033655)
    ·
      refine ⟨15431072812379127000050483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10287381874919418000033655 15431072812379127000050483)
      ·
        refine ⟨23146609218568690500075725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15431072812379127000050483 23146609218568690500075725)
        ·
          refine ⟨8679978456963258937528397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23146609218568690500075725 8679978456963258937528397)
          ·
            refine ⟨3254991921361222101573149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8679978456963258937528397 3254991921361222101573149)
            ·
              refine ⟨1220621970510458288089931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3254991921361222101573149 1220621970510458288089931)
              ·
                refine ⟨1830932955765687432134897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1220621970510458288089931 1830932955765687432134897)
                ·
                  refine ⟨1373199716824265574101173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1830932955765687432134897 1373199716824265574101173)
                  ·
                    refine ⟨128737473452274897571985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1373199716824265574101173 128737473452274897571985)
                    ·
                      rfl

theorem cell22_376073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_376073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376073 prefixEnd_376073 := by exact prefixLift 376073
  have htrace : WordTrace (prefixWord ++ tailWord_376073) baseStart_376073 baseEnd_376073 := by
    simpa [prefixWord, tailWord_376073, baseEnd_376073] using wordTrace_append hprefix tailTrace_376073
  have hstable : (prefixWord ++ tailWord_376073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376073).length < 2 ^ (prefixWord ++ tailWord_376073).sum := by decide
  have hdescent : baseEnd_376073 < baseStart_376073 := by decide
  rcases family_descends (prefixWord ++ tailWord_376073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376109 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 5]
def baseStart_376109 : Nat := 118140960795 + 376109 * 2 ^ 59
def prefixEnd_376109 : Nat := 4983230072969 + 3 ^ 40 * 376109 * 2
def baseEnd_376109 : Nat := 42916598995994267890625

theorem tailTrace_376109 : CollatzResearch.WordTrace tailWord_376109 prefixEnd_376109 42916598995994267890625 := by
  unfold tailWord_376109
  simp only [CollatzResearch.WordTrace]
  refine ⟨13717822194428802148355381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9145214796285868098903587 13717822194428802148355381)
  ·
    refine ⟨1286045830727700201408317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13717822194428802148355381 1286045830727700201408317)
    ·
      refine ⟨482267186522887575528119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1286045830727700201408317 482267186522887575528119)
      ·
        refine ⟨723400779784331363292179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482267186522887575528119 723400779784331363292179)
        ·
          refine ⟨1085101169676497044938269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723400779784331363292179 1085101169676497044938269)
          ·
            refine ⟨406912938628686391851851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1085101169676497044938269 406912938628686391851851)
            ·
              refine ⟨610369407943029587777777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406912938628686391851851 610369407943029587777777)
              ·
                refine ⟨457777055957272190833333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610369407943029587777777 457777055957272190833333)
                ·
                  refine ⟨42916598995994267890625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457777055957272190833333 42916598995994267890625)
                  ·
                    rfl

theorem cell22_376109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_376109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376109 prefixEnd_376109 := by exact prefixLift 376109
  have htrace : WordTrace (prefixWord ++ tailWord_376109) baseStart_376109 baseEnd_376109 := by
    simpa [prefixWord, tailWord_376109, baseEnd_376109] using wordTrace_append hprefix tailTrace_376109
  have hstable : (prefixWord ++ tailWord_376109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376109).length < 2 ^ (prefixWord ++ tailWord_376109).sum := by decide
  have hdescent : baseEnd_376109 < baseStart_376109 := by decide
  rcases family_descends (prefixWord ++ tailWord_376109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376135 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 1, 5]
def baseStart_376135 : Nat := 118140960795 + 376135 * 2 ^ 59
def prefixEnd_376135 : Nat := 4983230072969 + 3 ^ 40 * 376135 * 2
def baseEnd_376135 : Nat := 128758697319327402521795

theorem tailTrace_376135 : CollatzResearch.WordTrace tailWord_376135 prefixEnd_376135 128758697319327402521795 := by
  unfold tailWord_376135
  simp only [CollatzResearch.WordTrace]
  refine ⟨13718770492334608588801859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9145846994889739059201239 13718770492334608588801859)
  ·
    refine ⟨20578155738501912883202789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13718770492334608588801859 20578155738501912883202789)
    ·
      refine ⟨3858404200969108665600523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20578155738501912883202789 3858404200969108665600523)
      ·
        refine ⟨5787606301453662998400785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858404200969108665600523 5787606301453662998400785)
        ·
          refine ⟨4340704726090247248800589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787606301453662998400785 4340704726090247248800589)
          ·
            refine ⟨1627764272283842718300221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4340704726090247248800589 1627764272283842718300221)
            ·
              refine ⟨610411602106441019362583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1627764272283842718300221 610411602106441019362583)
              ·
                refine ⟨915617403159661529043875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 610411602106441019362583 915617403159661529043875)
                ·
                  refine ⟨1373426104739492293565813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 915617403159661529043875 1373426104739492293565813)
                  ·
                    refine ⟨128758697319327402521795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1373426104739492293565813 128758697319327402521795)
                    ·
                      rfl

theorem cell22_376135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_376135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376135 prefixEnd_376135 := by exact prefixLift 376135
  have htrace : WordTrace (prefixWord ++ tailWord_376135) baseStart_376135 baseEnd_376135 := by
    simpa [prefixWord, tailWord_376135, baseEnd_376135] using wordTrace_append hprefix tailTrace_376135
  have hstable : (prefixWord ++ tailWord_376135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376135).length < 2 ^ (prefixWord ++ tailWord_376135).sum := by decide
  have hdescent : baseEnd_376135 < baseStart_376135 := by decide
  rcases family_descends (prefixWord ++ tailWord_376135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376167 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 2, 4]
def baseStart_376167 : Nat := 118140960795 + 376167 * 2 ^ 59
def prefixEnd_376167 : Nat := 4983230072969 + 3 ^ 40 * 376167 * 2
def baseEnd_376167 : Nat := 128769651573289985721697

theorem tailTrace_376167 : CollatzResearch.WordTrace tailWord_376167 prefixEnd_376167 128769651573289985721697 := by
  unfold tailWord_376167
  simp only [CollatzResearch.WordTrace]
  refine ⟨13719937628218678053966755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9146625085479118702644503 13719937628218678053966755)
  ·
    refine ⟨20579906442328017080950133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13719937628218678053966755 20579906442328017080950133)
    ·
      refine ⟨1929366228968251601339075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20579906442328017080950133 1929366228968251601339075)
      ·
        refine ⟨2894049343452377402008613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1929366228968251601339075 2894049343452377402008613)
        ·
          refine ⟨542634251897320762876615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2894049343452377402008613 542634251897320762876615)
          ·
            refine ⟨813951377845981144314923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542634251897320762876615 813951377845981144314923)
            ·
              refine ⟨1220927066768971716472385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813951377845981144314923 1220927066768971716472385)
              ·
                refine ⟨915695300076728787354289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1220927066768971716472385 915695300076728787354289)
                ·
                  refine ⟨686771475057546590515717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915695300076728787354289 686771475057546590515717)
                  ·
                    refine ⟨128769651573289985721697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 686771475057546590515717 128769651573289985721697)
                    ·
                      rfl

theorem cell22_376167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_376167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376167 prefixEnd_376167 := by exact prefixLift 376167
  have htrace : WordTrace (prefixWord ++ tailWord_376167) baseStart_376167 baseEnd_376167 := by
    simpa [prefixWord, tailWord_376167, baseEnd_376167] using wordTrace_append hprefix tailTrace_376167
  have hstable : (prefixWord ++ tailWord_376167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376167).length < 2 ^ (prefixWord ++ tailWord_376167).sum := by decide
  have hdescent : baseEnd_376167 < baseStart_376167 := by decide
  rcases family_descends (prefixWord ++ tailWord_376167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376287 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 4, 3]
def baseStart_376287 : Nat := 118140960795 + 376287 * 2 ^ 59
def prefixEnd_376287 : Nat := 4983230072969 + 3 ^ 40 * 376287 * 2
def baseEnd_376287 : Nat := 128810730025649672721329

theorem tailTrace_376287 : CollatzResearch.WordTrace tailWord_376287 prefixEnd_376287 128810730025649672721329 := by
  unfold tailWord_376287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13724314387783938548335115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9149542925189292365556743 13724314387783938548335115)
  ·
    refine ⟨20586471581675907822502673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13724314387783938548335115 20586471581675907822502673)
    ·
      refine ⟨15439853686256930866877005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20586471581675907822502673 15439853686256930866877005)
      ·
        refine ⟨5789945132346349075078877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15439853686256930866877005 5789945132346349075078877)
        ·
          refine ⟨2171229424629880903154579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5789945132346349075078877 2171229424629880903154579)
          ·
            refine ⟨3256844136944821354731869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2171229424629880903154579 3256844136944821354731869)
            ·
              refine ⟨1221316551354308008024451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3256844136944821354731869 1221316551354308008024451)
              ·
                refine ⟨1831974827031462012036677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1221316551354308008024451 1831974827031462012036677)
                ·
                  refine ⟨343495280068399127256877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1831974827031462012036677 343495280068399127256877)
                  ·
                    refine ⟨128810730025649672721329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343495280068399127256877 128810730025649672721329)
                    ·
                      rfl

theorem cell22_376287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_376287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376287 prefixEnd_376287 := by exact prefixLift 376287
  have htrace : WordTrace (prefixWord ++ tailWord_376287) baseStart_376287 baseEnd_376287 := by
    simpa [prefixWord, tailWord_376287, baseEnd_376287] using wordTrace_append hprefix tailTrace_376287
  have hstable : (prefixWord ++ tailWord_376287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376287).length < 2 ^ (prefixWord ++ tailWord_376287).sum := by decide
  have hdescent : baseEnd_376287 < baseStart_376287 := by decide
  rcases family_descends (prefixWord ++ tailWord_376287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376317 : List Nat := [1, 4, 1, 1, 1, 4, 4, 6]
def baseStart_376317 : Nat := 118140960795 + 376317 * 2 ^ 59
def prefixEnd_376317 : Nat := 4983230072969 + 3 ^ 40 * 376317 * 2
def baseEnd_376317 : Nat := 14313444404304399385693

theorem tailTrace_376317 : CollatzResearch.WordTrace tailWord_376317 prefixEnd_376317 14313444404304399385693 := by
  unfold tailWord_376317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13725408577675253671927205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9150272385116835781284803 13725408577675253671927205)
  ·
    refine ⟨2573514108314110063486351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13725408577675253671927205 2573514108314110063486351)
    ·
      refine ⟨3860271162471165095229527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573514108314110063486351 3860271162471165095229527)
      ·
        refine ⟨5790406743706747642844291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3860271162471165095229527 5790406743706747642844291)
        ·
          refine ⟨8685610115560121464266437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5790406743706747642844291 8685610115560121464266437)
          ·
            refine ⟨1628551896667522774549957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8685610115560121464266437 1628551896667522774549957)
            ·
              refine ⟨305353480625160520228117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1628551896667522774549957 305353480625160520228117)
              ·
                refine ⟨14313444404304399385693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 305353480625160520228117 14313444404304399385693)
                ·
                  rfl

theorem cell22_376317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 6].length) (baseStart_376317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376317 prefixEnd_376317 := by exact prefixLift 376317
  have htrace : WordTrace (prefixWord ++ tailWord_376317) baseStart_376317 baseEnd_376317 := by
    simpa [prefixWord, tailWord_376317, baseEnd_376317] using wordTrace_append hprefix tailTrace_376317
  have hstable : (prefixWord ++ tailWord_376317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376317).length < 2 ^ (prefixWord ++ tailWord_376317).sum := by decide
  have hdescent : baseEnd_376317 < baseStart_376317 := by decide
  rcases family_descends (prefixWord ++ tailWord_376317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376334 : List Nat := [4, 1, 1, 2, 5, 1, 8]
def baseStart_376334 : Nat := 118140960795 + 376334 * 2 ^ 59
def prefixEnd_376334 : Nat := 4983230072969 + 3 ^ 40 * 376334 * 2
def baseEnd_376334 : Nat := 4771363669857674696155

theorem tailTrace_376334 : CollatzResearch.WordTrace tailWord_376334 prefixEnd_376334 4771363669857674696155 := by
  unfold tailWord_376334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715753577326708196912007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9150685745742443716864037 1715753577326708196912007)
  ·
    refine ⟨2573630365990062295368011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715753577326708196912007 2573630365990062295368011)
    ·
      refine ⟨3860445548985093443052017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2573630365990062295368011 3860445548985093443052017)
      ·
        refine ⟨2895334161738820082289013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3860445548985093443052017 2895334161738820082289013)
        ·
          refine ⟨271437577663014382714595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2895334161738820082289013 271437577663014382714595)
          ·
            refine ⟨407156366494521574071893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271437577663014382714595 407156366494521574071893)
            ·
              refine ⟨4771363669857674696155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 407156366494521574071893 4771363669857674696155)
              ·
                rfl

theorem cell22_376334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 8].length) (baseStart_376334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376334 prefixEnd_376334 := by exact prefixLift 376334
  have htrace : WordTrace (prefixWord ++ tailWord_376334) baseStart_376334 baseEnd_376334 := by
    simpa [prefixWord, tailWord_376334, baseEnd_376334] using wordTrace_append hprefix tailTrace_376334
  have hstable : (prefixWord ++ tailWord_376334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376334).length < 2 ^ (prefixWord ++ tailWord_376334).sum := by decide
  have hdescent : baseEnd_376334 < baseStart_376334 := by decide
  rcases family_descends (prefixWord ++ tailWord_376334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376424 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 6]
def baseStart_376424 : Nat := 118140960795 + 376424 * 2 ^ 59
def prefixEnd_376424 : Nat := 4983230072969 + 3 ^ 40 * 376424 * 2
def baseEnd_376424 : Nat := 42952542641808994015303

theorem tailTrace_376424 : CollatzResearch.WordTrace tailWord_376424 prefixEnd_376424 42952542641808994015303 := by
  unfold tailWord_376424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6864655594143805473036163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9152874125525073964048217 6864655594143805473036163)
  ·
    refine ⟨10296983391215708209554245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6864655594143805473036163 10296983391215708209554245)
    ·
      refine ⟨1930684385852945289291421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10296983391215708209554245 1930684385852945289291421)
      ·
        refine ⟨724006644694854483484283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1930684385852945289291421 724006644694854483484283)
        ·
          refine ⟨1086009967042281725226425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724006644694854483484283 1086009967042281725226425)
          ·
            refine ⟨814507475281711293919819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086009967042281725226425 814507475281711293919819)
            ·
              refine ⟨1221761212922566940879729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814507475281711293919819 1221761212922566940879729)
              ·
                refine ⟨916320909691925205659797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221761212922566940879729 916320909691925205659797)
                ·
                  refine ⟨42952542641808994015303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 916320909691925205659797 42952542641808994015303)
                  ·
                    rfl

theorem cell22_376424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_376424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376424 prefixEnd_376424 := by exact prefixLift 376424
  have htrace : WordTrace (prefixWord ++ tailWord_376424) baseStart_376424 baseEnd_376424 := by
    simpa [prefixWord, tailWord_376424, baseEnd_376424] using wordTrace_append hprefix tailTrace_376424
  have hstable : (prefixWord ++ tailWord_376424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376424).length < 2 ^ (prefixWord ++ tailWord_376424).sum := by decide
  have hdescent : baseEnd_376424 < baseStart_376424 := by decide
  rcases family_descends (prefixWord ++ tailWord_376424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376636 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_376636 : Nat := 118140960795 + 376636 * 2 ^ 59
def prefixEnd_376636 : Nat := 4983230072969 + 3 ^ 40 * 376636 * 2
def baseEnd_376636 : Nat := 128930199857929095745259

theorem tailTrace_376636 : CollatzResearch.WordTrace tailWord_376636 prefixEnd_376636 128930199857929095745259 := by
  unfold tailWord_376636
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868521731759785576394881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9158028975679714101859841 6868521731759785576394881)
  ·
    refine ⟨5151391298819839182296161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6868521731759785576394881 5151391298819839182296161)
    ·
      refine ⟨3863543474114879386722121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5151391298819839182296161 3863543474114879386722121)
      ·
        refine ⟨2897657605586159540041591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3863543474114879386722121 2897657605586159540041591)
        ·
          refine ⟨4346486408379239310062387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2897657605586159540041591 4346486408379239310062387)
          ·
            refine ⟨6519729612568858965093581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4346486408379239310062387 6519729612568858965093581)
            ·
              refine ⟨2444898604713322111910093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6519729612568858965093581 2444898604713322111910093)
              ·
                refine ⟨916836976767495791966285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2444898604713322111910093 916836976767495791966285)
                ·
                  refine ⟨343813866287810921987357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 916836976767495791966285 343813866287810921987357)
                  ·
                    refine ⟨128930199857929095745259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343813866287810921987357 128930199857929095745259)
                    ·
                      rfl

theorem cell22_376636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_376636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376636 prefixEnd_376636 := by exact prefixLift 376636
  have htrace : WordTrace (prefixWord ++ tailWord_376636) baseStart_376636 baseEnd_376636 := by
    simpa [prefixWord, tailWord_376636, baseEnd_376636] using wordTrace_append hprefix tailTrace_376636
  have hstable : (prefixWord ++ tailWord_376636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376636).length < 2 ^ (prefixWord ++ tailWord_376636).sum := by decide
  have hdescent : baseEnd_376636 < baseStart_376636 := by decide
  rcases family_descends (prefixWord ++ tailWord_376636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376730 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_376730 : Nat := 118140960795 + 376730 * 2 ^ 59
def prefixEnd_376730 : Nat := 4983230072969 + 3 ^ 40 * 376730 * 2
def baseEnd_376730 : Nat := 128962377978944183894971

theorem tailTrace_376730 : CollatzResearch.WordTrace tailWord_376730 prefixEnd_376730 128962377978944183894971 := by
  unfold tailWord_376730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3435117981294756301677911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9160314616786016804474429 3435117981294756301677911)
  ·
    refine ⟨5152676971942134452516867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3435117981294756301677911 5152676971942134452516867)
    ·
      refine ⟨7729015457913201678775301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5152676971942134452516867 7729015457913201678775301)
      ·
        refine ⟨1449190398358725314770369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7729015457913201678775301 1449190398358725314770369)
        ·
          refine ⟨1086892798769043986077777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1449190398358725314770369 1086892798769043986077777)
          ·
            refine ⟨815169599076782989558333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086892798769043986077777 815169599076782989558333)
            ·
              refine ⟨305688599653793621084375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815169599076782989558333 305688599653793621084375)
              ·
                refine ⟨458532899480690431626563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305688599653793621084375 458532899480690431626563)
                ·
                  refine ⟨687799349221035647439845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458532899480690431626563 687799349221035647439845)
                  ·
                    refine ⟨128962377978944183894971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687799349221035647439845 128962377978944183894971)
                    ·
                      rfl

theorem cell22_376730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_376730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376730 prefixEnd_376730 := by exact prefixLift 376730
  have htrace : WordTrace (prefixWord ++ tailWord_376730) baseStart_376730 baseEnd_376730 := by
    simpa [prefixWord, tailWord_376730, baseEnd_376730] using wordTrace_append hprefix tailTrace_376730
  have hstable : (prefixWord ++ tailWord_376730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376730).length < 2 ^ (prefixWord ++ tailWord_376730).sum := by decide
  have hdescent : baseEnd_376730 < baseStart_376730 := by decide
  rcases family_descends (prefixWord ++ tailWord_376730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376788 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_376788 : Nat := 118140960795 + 376788 * 2 ^ 59
def prefixEnd_376788 : Nat := 4983230072969 + 3 ^ 40 * 376788 * 2
def baseEnd_376788 : Nat := 128982232564251365944793

theorem tailTrace_376788 : CollatzResearch.WordTrace tailWord_376788 prefixEnd_376788 128982232564251365944793 := by
  unfold tailWord_376788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871293679484450556161509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9161724905979267408215345 6871293679484450556161509)
  ·
    refine ⟨1288367564903334479280283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6871293679484450556161509 1288367564903334479280283)
    ·
      refine ⟨1932551347355001718920425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288367564903334479280283 1932551347355001718920425)
      ·
        refine ⟨1449413510516251289190319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1932551347355001718920425 1449413510516251289190319)
        ·
          refine ⟨2174120265774376933785479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1449413510516251289190319 2174120265774376933785479)
          ·
            refine ⟨3261180398661565400678219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2174120265774376933785479 3261180398661565400678219)
            ·
              refine ⟨4891770597992348101017329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3261180398661565400678219 4891770597992348101017329)
              ·
                refine ⟨3668827948494261075762997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4891770597992348101017329 3668827948494261075762997)
                ·
                  refine ⟨343952620171336975852781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3668827948494261075762997 343952620171336975852781)
                  ·
                    refine ⟨128982232564251365944793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343952620171336975852781 128982232564251365944793)
                    ·
                      rfl

theorem cell22_376788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_376788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376788 prefixEnd_376788 := by exact prefixLift 376788
  have htrace : WordTrace (prefixWord ++ tailWord_376788) baseStart_376788 baseEnd_376788 := by
    simpa [prefixWord, tailWord_376788, baseEnd_376788] using wordTrace_append hprefix tailTrace_376788
  have hstable : (prefixWord ++ tailWord_376788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376788).length < 2 ^ (prefixWord ++ tailWord_376788).sum := by decide
  have hdescent : baseEnd_376788 < baseStart_376788 := by decide
  rcases family_descends (prefixWord ++ tailWord_376788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376816 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_376816 : Nat := 118140960795 + 376816 * 2 ^ 59
def prefixEnd_376816 : Nat := 4983230072969 + 3 ^ 40 * 376816 * 2
def baseEnd_376816 : Nat := 128991817536468626244707

theorem tailTrace_376816 : CollatzResearch.WordTrace tailWord_376816 prefixEnd_376816 128991817536468626244707 := by
  unfold tailWord_376816
  simp only [CollatzResearch.WordTrace]
  refine ⟨6871804301433730947171151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9162405735244974596228201 6871804301433730947171151)
  ·
    refine ⟨10307706452150596420756727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6871804301433730947171151 10307706452150596420756727)
    ·
      refine ⟨15461559678225894631135091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10307706452150596420756727 15461559678225894631135091)
      ·
        refine ⟨23192339517338841946702637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15461559678225894631135091 23192339517338841946702637)
        ·
          refine ⟨8697127319002065730013489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23192339517338841946702637 8697127319002065730013489)
          ·
            refine ⟨6522845489251549297510117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8697127319002065730013489 6522845489251549297510117)
            ·
              refine ⟨1223033529234665493283147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6522845489251549297510117 1223033529234665493283147)
              ·
                refine ⟨1834550293851998239924721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223033529234665493283147 1834550293851998239924721)
                ·
                  refine ⟨1375912720388998679943541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1834550293851998239924721 1375912720388998679943541)
                  ·
                    refine ⟨128991817536468626244707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1375912720388998679943541 128991817536468626244707)
                    ·
                      rfl

theorem cell22_376816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_376816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376816 prefixEnd_376816 := by exact prefixLift 376816
  have htrace : WordTrace (prefixWord ++ tailWord_376816) baseStart_376816 baseEnd_376816 := by
    simpa [prefixWord, tailWord_376816, baseEnd_376816] using wordTrace_append hprefix tailTrace_376816
  have hstable : (prefixWord ++ tailWord_376816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376816).length < 2 ^ (prefixWord ++ tailWord_376816).sum := by decide
  have hdescent : baseEnd_376816 < baseStart_376816 := by decide
  rcases family_descends (prefixWord ++ tailWord_376816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376831 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_376831 : Nat := 118140960795 + 376831 * 2 ^ 59
def prefixEnd_376831 : Nat := 4983230072969 + 3 ^ 40 * 376831 * 2
def baseEnd_376831 : Nat := 128996952343013587119661

theorem tailTrace_376831 : CollatzResearch.WordTrace tailWord_376831 prefixEnd_376831 128996952343013587119661 := by
  unfold tailWord_376831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13744155697813119456138347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9162770465208746304092231 13744155697813119456138347)
  ·
    refine ⟨20616233546719679184207521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13744155697813119456138347 20616233546719679184207521)
    ·
      refine ⟨15462175160039759388155641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20616233546719679184207521 15462175160039759388155641)
      ·
        refine ⟨11596631370029819541116731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15462175160039759388155641 11596631370029819541116731)
        ·
          refine ⟨17394947055044729311675097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11596631370029819541116731 17394947055044729311675097)
          ·
            refine ⟨13046210291283546983756323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17394947055044729311675097 13046210291283546983756323)
            ·
              refine ⟨19569315436925320475634485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13046210291283546983756323 19569315436925320475634485)
              ·
                refine ⟨1834623322211748794590733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19569315436925320475634485 1834623322211748794590733)
                ·
                  refine ⟨687983745829405797971525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1834623322211748794590733 687983745829405797971525)
                  ·
                    refine ⟨128996952343013587119661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687983745829405797971525 128996952343013587119661)
                    ·
                      rfl

theorem cell22_376831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_376831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376831 prefixEnd_376831 := by exact prefixLift 376831
  have htrace : WordTrace (prefixWord ++ tailWord_376831) baseStart_376831 baseEnd_376831 := by
    simpa [prefixWord, tailWord_376831, baseEnd_376831] using wordTrace_append hprefix tailTrace_376831
  have hstable : (prefixWord ++ tailWord_376831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376831).length < 2 ^ (prefixWord ++ tailWord_376831).sum := by decide
  have hdescent : baseEnd_376831 < baseStart_376831 := by decide
  rcases family_descends (prefixWord ++ tailWord_376831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376876 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_376876 : Nat := 118140960795 + 376876 * 2 ^ 59
def prefixEnd_376876 : Nat := 4983230072969 + 3 ^ 40 * 376876 * 2
def baseEnd_376876 : Nat := 129012356762648469744523

theorem tailTrace_376876 : CollatzResearch.WordTrace tailWord_376876 prefixEnd_376876 129012356762648469744523 := by
  unfold tailWord_376876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872898491325046070763241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9163864655100061427684321 6872898491325046070763241)
  ·
    refine ⟨5154673868493784553072431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6872898491325046070763241 5154673868493784553072431)
    ·
      refine ⟨7732010802740676829608647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5154673868493784553072431 7732010802740676829608647)
      ·
        refine ⟨11598016204111015244412971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7732010802740676829608647 11598016204111015244412971)
        ·
          refine ⟨17397024306166522866619457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11598016204111015244412971 17397024306166522866619457)
          ·
            refine ⟨13047768229624892149964593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17397024306166522866619457 13047768229624892149964593)
            ·
              refine ⟨9785826172218669112473445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13047768229624892149964593 9785826172218669112473445)
              ·
                refine ⟨1834842407291000458588771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9785826172218669112473445 1834842407291000458588771)
                ·
                  refine ⟨2752263610936500687883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1834842407291000458588771 2752263610936500687883157)
                  ·
                    refine ⟨129012356762648469744523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2752263610936500687883157 129012356762648469744523)
                    ·
                      rfl

theorem cell22_376876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_376876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376876 prefixEnd_376876 := by exact prefixLift 376876
  have htrace : WordTrace (prefixWord ++ tailWord_376876) baseStart_376876 baseEnd_376876 := by
    simpa [prefixWord, tailWord_376876, baseEnd_376876] using wordTrace_append hprefix tailTrace_376876
  have hstable : (prefixWord ++ tailWord_376876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376876).length < 2 ^ (prefixWord ++ tailWord_376876).sum := by decide
  have hdescent : baseEnd_376876 < baseStart_376876 := by decide
  rcases family_descends (prefixWord ++ tailWord_376876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376914 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_376914 : Nat := 118140960795 + 376914 * 2 ^ 59
def prefixEnd_376914 : Nat := 4983230072969 + 3 ^ 40 * 376914 * 2
def baseEnd_376914 : Nat := 43008454979743012431469

theorem tailTrace_376914 : CollatzResearch.WordTrace tailWord_376914 prefixEnd_376914 43008454979743012431469 := by
  unfold tailWord_376914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436795739128106157852449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9164788637674949754273197 3436795739128106157852449)
  ·
    refine ⟨2577596804346079618389337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3436795739128106157852449 2577596804346079618389337)
    ·
      refine ⟨1933197603259559713792003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2577596804346079618389337 1933197603259559713792003)
      ·
        refine ⟨2899796404889339570688005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933197603259559713792003 2899796404889339570688005)
        ·
          refine ⟨543711825916751169504001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2899796404889339570688005 543711825916751169504001)
          ·
            refine ⟨407783869437563377128001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543711825916751169504001 407783869437563377128001)
            ·
              refine ⟨305837902078172532846001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 407783869437563377128001 305837902078172532846001)
              ·
                refine ⟨229378426558629399634501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305837902078172532846001 229378426558629399634501)
                ·
                  refine ⟨43008454979743012431469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229378426558629399634501 43008454979743012431469)
                  ·
                    rfl

theorem cell22_376914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_376914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376914 prefixEnd_376914 := by exact prefixLift 376914
  have htrace : WordTrace (prefixWord ++ tailWord_376914) baseStart_376914 baseEnd_376914 := by
    simpa [prefixWord, tailWord_376914, baseEnd_376914] using wordTrace_append hprefix tailTrace_376914
  have hstable : (prefixWord ++ tailWord_376914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376914).length < 2 ^ (prefixWord ++ tailWord_376914).sum := by decide
  have hdescent : baseEnd_376914 < baseStart_376914 := by decide
  rcases family_descends (prefixWord ++ tailWord_376914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376921 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_376921 : Nat := 118140960795 + 376921 * 2 ^ 59
def prefixEnd_376921 : Nat := 4983230072969 + 3 ^ 40 * 376921 * 2
def baseEnd_376921 : Nat := 129027761182283352369385

theorem tailTrace_376921 : CollatzResearch.WordTrace tailWord_376921 prefixEnd_376921 129027761182283352369385 := by
  unfold tailWord_376921
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747438267487064826914617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9164958844991376551276411 13747438267487064826914617)
  ·
    refine ⟨10310578700615298620185963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13747438267487064826914617 10310578700615298620185963)
    ·
      refine ⟨15465868050922947930278945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10310578700615298620185963 15465868050922947930278945)
      ·
        refine ⟨11599401038192210947709209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15465868050922947930278945 11599401038192210947709209)
        ·
          refine ⟨8699550778644158210781907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11599401038192210947709209 8699550778644158210781907)
          ·
            refine ⟨13049326167966237316172861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699550778644158210781907 13049326167966237316172861)
            ·
              refine ⟨4893497312987338993564823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13049326167966237316172861 4893497312987338993564823)
              ·
                refine ⟨7340245969481008490347235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4893497312987338993564823 7340245969481008490347235)
                ·
                  refine ⟨11010368954221512735520853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7340245969481008490347235 11010368954221512735520853)
                  ·
                    refine ⟨129027761182283352369385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11010368954221512735520853 129027761182283352369385)
                    ·
                      rfl

theorem cell22_376921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_376921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376921 prefixEnd_376921 := by exact prefixLift 376921
  have htrace : WordTrace (prefixWord ++ tailWord_376921) baseStart_376921 baseEnd_376921 := by
    simpa [prefixWord, tailWord_376921, baseEnd_376921] using wordTrace_append hprefix tailTrace_376921
  have hstable : (prefixWord ++ tailWord_376921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376921).length < 2 ^ (prefixWord ++ tailWord_376921).sum := by decide
  have hdescent : baseEnd_376921 < baseStart_376921 := by decide
  rcases family_descends (prefixWord ++ tailWord_376921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376925 : List Nat := [1, 4, 4, 1, 1, 1, 3, 7]
def baseStart_376925 : Nat := 118140960795 + 376925 * 2 ^ 59
def prefixEnd_376925 : Nat := 4983230072969 + 3 ^ 40 * 376925 * 2
def baseEnd_376925 : Nat := 14336570051558741696597

theorem tailTrace_376925 : CollatzResearch.WordTrace tailWord_376925 prefixEnd_376925 14336570051558741696597 := by
  unfold tailWord_376925
  simp only [CollatzResearch.WordTrace]
  refine ⟨13747584159472573510060229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9165056106315049006706819 13747584159472573510060229)
  ·
    refine ⟨2577672029901107533136293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13747584159472573510060229 2577672029901107533136293)
    ·
      refine ⟨483313505606457662463055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2577672029901107533136293 483313505606457662463055)
      ·
        refine ⟨724970258409686493694583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483313505606457662463055 724970258409686493694583)
        ·
          refine ⟨1087455387614529740541875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 724970258409686493694583 1087455387614529740541875)
          ·
            refine ⟨1631183081421794610812813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087455387614529740541875 1631183081421794610812813)
            ·
              refine ⟨611693655533172979054805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631183081421794610812813 611693655533172979054805)
              ·
                refine ⟨14336570051558741696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 611693655533172979054805 14336570051558741696597)
                ·
                  rfl

theorem cell22_376925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 7].length) (baseStart_376925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376925 prefixEnd_376925 := by exact prefixLift 376925
  have htrace : WordTrace (prefixWord ++ tailWord_376925) baseStart_376925 baseEnd_376925 := by
    simpa [prefixWord, tailWord_376925, baseEnd_376925] using wordTrace_append hprefix tailTrace_376925
  have hstable : (prefixWord ++ tailWord_376925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376925).length < 2 ^ (prefixWord ++ tailWord_376925).sum := by decide
  have hdescent : baseEnd_376925 < baseStart_376925 := by decide
  rcases family_descends (prefixWord ++ tailWord_376925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376940 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_376940 : Nat := 118140960795 + 376940 * 2 ^ 59
def prefixEnd_376940 : Nat := 4983230072969 + 3 ^ 40 * 376940 * 2
def baseEnd_376940 : Nat := 129034265270573636144327

theorem tailTrace_376940 : CollatzResearch.WordTrace tailWord_376940 prefixEnd_376940 129034265270573636144327 := by
  unfold tailWord_376940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6874065627209115535928137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9165420836278820714570849 6874065627209115535928137)
  ·
    refine ⟨5155549220406836651946103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6874065627209115535928137 5155549220406836651946103)
    ·
      refine ⟨7733323830610254977919155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155549220406836651946103 7733323830610254977919155)
      ·
        refine ⟨11599985745915382466878733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7733323830610254977919155 11599985745915382466878733)
        ·
          refine ⟨4349994654718268425079525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11599985745915382466878733 4349994654718268425079525)
          ·
            refine ⟨815623997759675329702411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4349994654718268425079525 815623997759675329702411)
            ·
              refine ⟨1223435996639512994553617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 815623997759675329702411 1223435996639512994553617)
              ·
                refine ⟨917576997479634745915213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223435996639512994553617 917576997479634745915213)
                ·
                  refine ⟨344091374054863029718205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 917576997479634745915213 344091374054863029718205)
                  ·
                    refine ⟨129034265270573636144327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344091374054863029718205 129034265270573636144327)
                    ·
                      rfl

theorem cell22_376940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_376940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376940 prefixEnd_376940 := by exact prefixLift 376940
  have htrace : WordTrace (prefixWord ++ tailWord_376940) baseStart_376940 baseEnd_376940 := by
    simpa [prefixWord, tailWord_376940, baseEnd_376940] using wordTrace_append hprefix tailTrace_376940
  have hstable : (prefixWord ++ tailWord_376940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376940).length < 2 ^ (prefixWord ++ tailWord_376940).sum := by decide
  have hdescent : baseEnd_376940 < baseStart_376940 := by decide
  rcases family_descends (prefixWord ++ tailWord_376940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376957 : List Nat := [1, 4, 1, 1, 3, 2, 1, 5, 1, 3]
def baseStart_376957 : Nat := 118140960795 + 376957 * 2 ^ 59
def prefixEnd_376957 : Nat := 4983230072969 + 3 ^ 40 * 376957 * 2
def baseEnd_376957 : Nat := 129040084717991258469275

theorem tailTrace_376957 : CollatzResearch.WordTrace tailWord_376957 prefixEnd_376957 129040084717991258469275 := by
  unfold tailWord_376957
  simp only [CollatzResearch.WordTrace]
  refine ⟨13748751295356642975225125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9165834196904428650150083 13748751295356642975225125)
  ·
    refine ⟨2577890867879370557854711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13748751295356642975225125 2577890867879370557854711)
    ·
      refine ⟨3866836301819055836782067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2577890867879370557854711 3866836301819055836782067)
      ·
        refine ⟨5800254452728583755173101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866836301819055836782067 5800254452728583755173101)
        ·
          refine ⟨2175095419773218908189913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5800254452728583755173101 2175095419773218908189913)
          ·
            refine ⟨1631321564829914181142435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175095419773218908189913 1631321564829914181142435)
            ·
              refine ⟨2446982347244871271713653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631321564829914181142435 2446982347244871271713653)
              ·
                refine ⟨229404595054206681723155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2446982347244871271713653 229404595054206681723155)
                ·
                  refine ⟨344106892581310022584733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229404595054206681723155 344106892581310022584733)
                  ·
                    refine ⟨129040084717991258469275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344106892581310022584733 129040084717991258469275)
                    ·
                      rfl

theorem cell22_376957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_376957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376957 prefixEnd_376957 := by exact prefixLift 376957
  have htrace : WordTrace (prefixWord ++ tailWord_376957) baseStart_376957 baseEnd_376957 := by
    simpa [prefixWord, tailWord_376957, baseEnd_376957] using wordTrace_append hprefix tailTrace_376957
  have hstable : (prefixWord ++ tailWord_376957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376957).length < 2 ^ (prefixWord ++ tailWord_376957).sum := by decide
  have hdescent : baseEnd_376957 < baseStart_376957 := by decide
  rcases family_descends (prefixWord ++ tailWord_376957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_376970 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_376970 : Nat := 118140960795 + 376970 * 2 ^ 59
def prefixEnd_376970 : Nat := 4983230072969 + 3 ^ 40 * 376970 * 2
def baseEnd_376970 : Nat := 43014844961221185964745

theorem tailTrace_376970 : CollatzResearch.WordTrace tailWord_376970 prefixEnd_376970 43014844961221185964745 := by
  unfold tailWord_376970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437306361077386548862091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9166150296206364130298909 3437306361077386548862091)
  ·
    refine ⟨5155959541616079823293137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437306361077386548862091 5155959541616079823293137)
    ·
      refine ⟨3866969656212059867469853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5155959541616079823293137 3866969656212059867469853)
      ·
        refine ⟨1450113621079522450301195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3866969656212059867469853 1450113621079522450301195)
        ·
          refine ⟨2175170431619283675451793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450113621079522450301195 2175170431619283675451793)
          ·
            refine ⟨1631377823714462756588845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175170431619283675451793 1631377823714462756588845)
            ·
              refine ⟨611766683892923533720817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631377823714462756588845 611766683892923533720817)
              ·
                refine ⟨458825012919692650290613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611766683892923533720817 458825012919692650290613)
                ·
                  refine ⟨43014844961221185964745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 458825012919692650290613 43014844961221185964745)
                  ·
                    rfl

theorem cell22_376970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_376970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_376970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_376970 prefixEnd_376970 := by exact prefixLift 376970
  have htrace : WordTrace (prefixWord ++ tailWord_376970) baseStart_376970 baseEnd_376970 := by
    simpa [prefixWord, tailWord_376970, baseEnd_376970] using wordTrace_append hprefix tailTrace_376970
  have hstable : (prefixWord ++ tailWord_376970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_376970).length < 2 ^ (prefixWord ++ tailWord_376970).sum := by decide
  have hdescent : baseEnd_376970 < baseStart_376970 := by decide
  rcases family_descends (prefixWord ++ tailWord_376970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377088 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_377088 : Nat := 118140960795 + 377088 * 2 ^ 59
def prefixEnd_377088 : Nat := 4983230072969 + 3 ^ 40 * 377088 * 2
def baseEnd_377088 : Nat := 43028309565050194481291

theorem tailTrace_377088 : CollatzResearch.WordTrace tailWord_377088 prefixEnd_377088 43028309565050194481291 := by
  unfold tailWord_377088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6876764628941026174121959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9169019505254701565495945 6876764628941026174121959)
  ·
    refine ⟨10315146943411539261182939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6876764628941026174121959 10315146943411539261182939)
    ·
      refine ⟨15472720415117308891774409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10315146943411539261182939 15472720415117308891774409)
      ·
        refine ⟨11604540311337981668830807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15472720415117308891774409 11604540311337981668830807)
        ·
          refine ⟨17406810467006972503246211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11604540311337981668830807 17406810467006972503246211)
          ·
            refine ⟨26110215700510458754869317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17406810467006972503246211 26110215700510458754869317)
            ·
              refine ⟨4895665443845711016537997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26110215700510458754869317 4895665443845711016537997)
              ·
                refine ⟨1835874541442141631201749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4895665443845711016537997 1835874541442141631201749)
                ·
                  refine ⟨43028309565050194481291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1835874541442141631201749 43028309565050194481291)
                  ·
                    rfl

theorem cell22_377088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_377088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377088 prefixEnd_377088 := by exact prefixLift 377088
  have htrace : WordTrace (prefixWord ++ tailWord_377088) baseStart_377088 baseEnd_377088 := by
    simpa [prefixWord, tailWord_377088, baseEnd_377088] using wordTrace_append hprefix tailTrace_377088
  have hstable : (prefixWord ++ tailWord_377088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377088).length < 2 ^ (prefixWord ++ tailWord_377088).sum := by decide
  have hdescent : baseEnd_377088 < baseStart_377088 := by decide
  rcases family_descends (prefixWord ++ tailWord_377088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377105 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 5]
def baseStart_377105 : Nat := 118140960795 + 377105 * 2 ^ 59
def prefixEnd_377105 : Nat := 4983230072969 + 3 ^ 40 * 377105 * 2
def baseEnd_377105 : Nat := 43030249380856068589607

theorem tailTrace_377105 : CollatzResearch.WordTrace tailWord_377105 prefixEnd_377105 43030249380856068589607 := by
  unfold tailWord_377105
  simp only [CollatzResearch.WordTrace]
  refine ⟨13754149298820464251612769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9169432865880309501075179 13754149298820464251612769)
  ·
    refine ⟨10315611974115348188709577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13754149298820464251612769 10315611974115348188709577)
    ·
      refine ⟨7736708980586511141532183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10315611974115348188709577 7736708980586511141532183)
      ·
        refine ⟨11605063470879766712298275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736708980586511141532183 11605063470879766712298275)
        ·
          refine ⟨17407595206319650068447413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11605063470879766712298275 17407595206319650068447413)
          ·
            refine ⟨1631962050592467193916945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17407595206319650068447413 1631962050592467193916945)
            ·
              refine ⟨1223971537944350395437709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631962050592467193916945 1223971537944350395437709)
              ·
                refine ⟨458989326729131398289141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1223971537944350395437709 458989326729131398289141)
                ·
                  refine ⟨43030249380856068589607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 458989326729131398289141 43030249380856068589607)
                  ·
                    rfl

theorem cell22_377105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_377105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377105 prefixEnd_377105 := by exact prefixLift 377105
  have htrace : WordTrace (prefixWord ++ tailWord_377105) baseStart_377105 baseEnd_377105 := by
    simpa [prefixWord, tailWord_377105, baseEnd_377105] using wordTrace_append hprefix tailTrace_377105
  have hstable : (prefixWord ++ tailWord_377105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377105).length < 2 ^ (prefixWord ++ tailWord_377105).sum := by decide
  have hdescent : baseEnd_377105 < baseStart_377105 := by decide
  rcases family_descends (prefixWord ++ tailWord_377105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377156 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 5]
def baseStart_377156 : Nat := 118140960795 + 377156 * 2 ^ 59
def prefixEnd_377156 : Nat := 4983230072969 + 3 ^ 40 * 377156 * 2
def baseEnd_377156 : Nat := 43036068828273690914555

theorem tailTrace_377156 : CollatzResearch.WordTrace tailWord_377156 prefixEnd_377156 43036068828273690914555 := by
  unfold tailWord_377156
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878004710817849980859661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9170672947757133307812881 6878004710817849980859661)
  ·
    refine ⟨2579251766556693742822373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6878004710817849980859661 2579251766556693742822373)
    ·
      refine ⟨483609706229380076779195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2579251766556693742822373 483609706229380076779195)
      ·
        refine ⟨725414559344070115168793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483609706229380076779195 725414559344070115168793)
        ·
          refine ⟨544060919508052586376595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 725414559344070115168793 544060919508052586376595)
          ·
            refine ⟨816091379262078879564893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544060919508052586376595 816091379262078879564893)
            ·
              refine ⟨306034267223279579836835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 816091379262078879564893 306034267223279579836835)
              ·
                refine ⟨459051400834919369755253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306034267223279579836835 459051400834919369755253)
                ·
                  refine ⟨43036068828273690914555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 459051400834919369755253 43036068828273690914555)
                  ·
                    rfl

theorem cell22_377156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_377156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377156 prefixEnd_377156 := by exact prefixLift 377156
  have htrace : WordTrace (prefixWord ++ tailWord_377156) baseStart_377156 baseEnd_377156 := by
    simpa [prefixWord, tailWord_377156, baseEnd_377156] using wordTrace_append hprefix tailTrace_377156
  have hstable : (prefixWord ++ tailWord_377156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377156).length < 2 ^ (prefixWord ++ tailWord_377156).sum := by decide
  have hdescent : baseEnd_377156 < baseStart_377156 := by decide
  rcases family_descends (prefixWord ++ tailWord_377156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377197 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_377197 : Nat := 118140960795 + 377197 * 2 ^ 59
def prefixEnd_377197 : Nat := 4983230072969 + 3 ^ 40 * 377197 * 2
def baseEnd_377197 : Nat := 129122241622710632468539

theorem tailTrace_377197 : CollatzResearch.WordTrace tailWord_377197 prefixEnd_377197 129122241622710632468539 := by
  unfold tailWord_377197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13757504814487163963961845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9171669876324775975974563 13757504814487163963961845)
  ·
    refine ⟨1289766076358171621621423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13757504814487163963961845 1289766076358171621621423)
    ·
      refine ⟨1934649114537257432432135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289766076358171621621423 1934649114537257432432135)
      ·
        refine ⟨2901973671805886148648203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934649114537257432432135 2901973671805886148648203)
        ·
          refine ⟨4352960507708829222972305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901973671805886148648203 4352960507708829222972305)
          ·
            refine ⟨3264720380781621917229229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352960507708829222972305 3264720380781621917229229)
            ·
              refine ⟨1224270142793108218960961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3264720380781621917229229 1224270142793108218960961)
              ·
                refine ⟨918202607094831164220721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224270142793108218960961 918202607094831164220721)
                ·
                  refine ⟨688651955321123373165541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918202607094831164220721 688651955321123373165541)
                  ·
                    refine ⟨129122241622710632468539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688651955321123373165541 129122241622710632468539)
                    ·
                      rfl

theorem cell22_377197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_377197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377197 prefixEnd_377197 := by exact prefixLift 377197
  have htrace : WordTrace (prefixWord ++ tailWord_377197) baseStart_377197 baseEnd_377197 := by
    simpa [prefixWord, tailWord_377197, baseEnd_377197] using wordTrace_append hprefix tailTrace_377197
  have hstable : (prefixWord ++ tailWord_377197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377197).length < 2 ^ (prefixWord ++ tailWord_377197).sum := by decide
  have hdescent : baseEnd_377197 < baseStart_377197 := by decide
  rcases family_descends (prefixWord ++ tailWord_377197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377287 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_377287 : Nat := 118140960795 + 377287 * 2 ^ 59
def prefixEnd_377287 : Nat := 4983230072969 + 3 ^ 40 * 377287 * 2
def baseEnd_377287 : Nat := 129153050461980397718263

theorem tailTrace_377287 : CollatzResearch.WordTrace tailWord_377287 prefixEnd_377287 129153050461980397718263 := by
  unfold tailWord_377287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13760787384161109334738115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9173858256107406223158743 13760787384161109334738115)
  ·
    refine ⟨20641181076241664002107173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13760787384161109334738115 20641181076241664002107173)
    ·
      refine ⟨3870221451795312000395095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20641181076241664002107173 3870221451795312000395095)
      ·
        refine ⟨5805332177692968000592643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870221451795312000395095 5805332177692968000592643)
        ·
          refine ⟨8707998266539452000888965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5805332177692968000592643 8707998266539452000888965)
          ·
            refine ⟨1632749674976147250166681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8707998266539452000888965 1632749674976147250166681)
            ·
              refine ⟨1224562256232110437625011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1632749674976147250166681 1224562256232110437625011)
              ·
                refine ⟨1836843384348165656437517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224562256232110437625011 1836843384348165656437517)
                ·
                  refine ⟨688816269130562121164069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1836843384348165656437517 688816269130562121164069)
                  ·
                    refine ⟨129153050461980397718263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688816269130562121164069 129153050461980397718263)
                    ·
                      rfl

theorem cell22_377287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_377287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377287 prefixEnd_377287 := by exact prefixLift 377287
  have htrace : WordTrace (prefixWord ++ tailWord_377287) baseStart_377287 baseEnd_377287 := by
    simpa [prefixWord, tailWord_377287, baseEnd_377287] using wordTrace_append hprefix tailTrace_377287
  have hstable : (prefixWord ++ tailWord_377287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377287).length < 2 ^ (prefixWord ++ tailWord_377287).sum := by decide
  have hdescent : baseEnd_377287 < baseStart_377287 := by decide
  rcases family_descends (prefixWord ++ tailWord_377287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377319 : List Nat := [1, 1, 5, 2, 1, 1, 1, 6, 4]
def baseStart_377319 : Nat := 118140960795 + 377319 * 2 ^ 59
def prefixEnd_377319 : Nat := 4983230072969 + 3 ^ 40 * 377319 * 2
def baseEnd_377319 : Nat := 43054668238647660306055

theorem tailTrace_377319 : CollatzResearch.WordTrace tailWord_377319 prefixEnd_377319 43054668238647660306055 := by
  unfold tailWord_377319
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761954520045178799903011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9174636346696785866602007 13761954520045178799903011)
  ·
    refine ⟨20642931780067768199854517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13761954520045178799903011 20642931780067768199854517)
    ·
      refine ⟨1935274854381353268736361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20642931780067768199854517 1935274854381353268736361)
      ·
        refine ⟨1451456140786014951552271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1935274854381353268736361 1451456140786014951552271)
        ·
          refine ⟨2177184211179022427328407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451456140786014951552271 2177184211179022427328407)
          ·
            refine ⟨3265776316768533640992611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177184211179022427328407 3265776316768533640992611)
            ·
              refine ⟨4898664475152800461488917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265776316768533640992611 4898664475152800461488917)
              ·
                refine ⟨229624897272787521632293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4898664475152800461488917 229624897272787521632293)
                ·
                  refine ⟨43054668238647660306055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 229624897272787521632293 43054668238647660306055)
                  ·
                    rfl

theorem cell22_377319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 6, 4].length) (baseStart_377319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377319 prefixEnd_377319 := by exact prefixLift 377319
  have htrace : WordTrace (prefixWord ++ tailWord_377319) baseStart_377319 baseEnd_377319 := by
    simpa [prefixWord, tailWord_377319, baseEnd_377319] using wordTrace_append hprefix tailTrace_377319
  have hstable : (prefixWord ++ tailWord_377319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377319).length < 2 ^ (prefixWord ++ tailWord_377319).sum := by decide
  have hdescent : baseEnd_377319 < baseStart_377319 := by decide
  rcases family_descends (prefixWord ++ tailWord_377319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377364 : List Nat := [2, 4, 3, 1, 1, 1, 10]
def baseStart_377364 : Nat := 118140960795 + 377364 * 2 ^ 59
def prefixEnd_377364 : Nat := 4983230072969 + 3 ^ 40 * 377364 * 2
def baseEnd_377364 : Nat := 4784422560576957909001

theorem tailTrace_377364 : CollatzResearch.WordTrace tailWord_377364 prefixEnd_377364 4784422560576957909001 := by
  unfold tailWord_377364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6881797902441075742645573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9175730536588100990194097 6881797902441075742645573)
  ·
    refine ⟨1290337106707701701746045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6881797902441075742645573 1290337106707701701746045)
    ·
      refine ⟨483876415015388138154767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1290337106707701701746045 483876415015388138154767)
      ·
        refine ⟨725814622523082207232151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483876415015388138154767 725814622523082207232151)
        ·
          refine ⟨1088721933784623310848227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725814622523082207232151 1088721933784623310848227)
          ·
            refine ⟨1633082900676934966272341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088721933784623310848227 1633082900676934966272341)
            ·
              refine ⟨4784422560576957909001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1633082900676934966272341 4784422560576957909001)
              ·
                rfl

theorem cell22_377364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 10].length) (baseStart_377364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377364 prefixEnd_377364 := by exact prefixLift 377364
  have htrace : WordTrace (prefixWord ++ tailWord_377364) baseStart_377364 baseEnd_377364 := by
    simpa [prefixWord, tailWord_377364, baseEnd_377364] using wordTrace_append hprefix tailTrace_377364
  have hstable : (prefixWord ++ tailWord_377364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377364).length < 2 ^ (prefixWord ++ tailWord_377364).sum := by decide
  have hdescent : baseEnd_377364 < baseStart_377364 := by decide
  rcases family_descends (prefixWord ++ tailWord_377364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377377 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_377377 : Nat := 118140960795 + 377377 * 2 ^ 59
def prefixEnd_377377 : Nat := 4983230072969 + 3 ^ 40 * 377377 * 2
def baseEnd_377377 : Nat := 129183859301250162967987

theorem tailTrace_377377 : CollatzResearch.WordTrace tailWord_377377 prefixEnd_377377 129183859301250162967987 := by
  unfold tailWord_377377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13764069953835054705514385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9176046635890036470342923 13764069953835054705514385)
  ·
    refine ⟨10323052465376291029135789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13764069953835054705514385 10323052465376291029135789)
    ·
      refine ⟨3871144674516109135925921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10323052465376291029135789 3871144674516109135925921)
      ·
        refine ⟨2903358505887081851944441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3871144674516109135925921 2903358505887081851944441)
        ·
          refine ⟨2177518879415311388958331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903358505887081851944441 2177518879415311388958331)
          ·
            refine ⟨3266278319122967083437497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177518879415311388958331 3266278319122967083437497)
            ·
              refine ⟨2449708739342225312578123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3266278319122967083437497 2449708739342225312578123)
              ·
                refine ⟨3674563109013337968867185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449708739342225312578123 3674563109013337968867185)
                ·
                  refine ⟨2755922331760003476650389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3674563109013337968867185 2755922331760003476650389)
                  ·
                    refine ⟨129183859301250162967987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2755922331760003476650389 129183859301250162967987)
                    ·
                      rfl

theorem cell22_377377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_377377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377377 prefixEnd_377377 := by exact prefixLift 377377
  have htrace : WordTrace (prefixWord ++ tailWord_377377) baseStart_377377 baseEnd_377377 := by
    simpa [prefixWord, tailWord_377377, baseEnd_377377] using wordTrace_append hprefix tailTrace_377377
  have hstable : (prefixWord ++ tailWord_377377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377377).length < 2 ^ (prefixWord ++ tailWord_377377).sum := by decide
  have hdescent : baseEnd_377377 < baseStart_377377 := by decide
  rcases family_descends (prefixWord ++ tailWord_377377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377454 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_377454 : Nat := 118140960795 + 377454 * 2 ^ 59
def prefixEnd_377454 : Nat := 4983230072969 + 3 ^ 40 * 377454 * 2
def baseEnd_377454 : Nat := 43070072658282542930917

theorem tailTrace_377454 : CollatzResearch.WordTrace tailWord_377454 prefixEnd_377454 43070072658282542930917 := by
  unfold tailWord_377454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720859796819512107008427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9177918916370731237378277 1720859796819512107008427)
  ·
    refine ⟨2581289695229268160512641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1720859796819512107008427 2581289695229268160512641)
    ·
      refine ⟨1935967271421951120384481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2581289695229268160512641 1935967271421951120384481)
      ·
        refine ⟨1451975453566463340288361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1935967271421951120384481 1451975453566463340288361)
        ·
          refine ⟨1088981590174847505216271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1451975453566463340288361 1088981590174847505216271)
          ·
            refine ⟨1633472385262271257824407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088981590174847505216271 1633472385262271257824407)
            ·
              refine ⟨2450208577893406886736611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633472385262271257824407 2450208577893406886736611)
              ·
                refine ⟨3675312866840110330104917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2450208577893406886736611 3675312866840110330104917)
                ·
                  refine ⟨43070072658282542930917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3675312866840110330104917 43070072658282542930917)
                  ·
                    rfl

theorem cell22_377454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_377454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377454 prefixEnd_377454 := by exact prefixLift 377454
  have htrace : WordTrace (prefixWord ++ tailWord_377454) baseStart_377454 baseEnd_377454 := by
    simpa [prefixWord, tailWord_377454, baseEnd_377454] using wordTrace_append hprefix tailTrace_377454
  have hstable : (prefixWord ++ tailWord_377454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377454).length < 2 ^ (prefixWord ++ tailWord_377454).sum := by decide
  have hdescent : baseEnd_377454 < baseStart_377454 := by decide
  rcases family_descends (prefixWord ++ tailWord_377454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377486 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_377486 : Nat := 118140960795 + 377486 * 2 ^ 59
def prefixEnd_377486 : Nat := 4983230072969 + 3 ^ 40 * 377486 * 2
def baseEnd_377486 : Nat := 129221172228810211992653

theorem tailTrace_377486 : CollatzResearch.WordTrace tailWord_377486 prefixEnd_377486 129221172228810211992653 := by
  unfold tailWord_377486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721005688805020790154039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9178697006960110880821541 1721005688805020790154039)
  ·
    refine ⟨2581508533207531185231059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721005688805020790154039 2581508533207531185231059)
    ·
      refine ⟨3872262799811296777846589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2581508533207531185231059 3872262799811296777846589)
      ·
        refine ⟨1452098549929236291692471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3872262799811296777846589 1452098549929236291692471)
        ·
          refine ⟨2178147824893854437538707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452098549929236291692471 2178147824893854437538707)
          ·
            refine ⟨3267221737340781656308061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2178147824893854437538707 3267221737340781656308061)
            ·
              refine ⟨1225208151502793121115523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3267221737340781656308061 1225208151502793121115523)
              ·
                refine ⟨1837812227254189681673285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225208151502793121115523 1837812227254189681673285)
                ·
                  refine ⟨344589792610160565313741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1837812227254189681673285 344589792610160565313741)
                  ·
                    refine ⟨129221172228810211992653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344589792610160565313741 129221172228810211992653)
                    ·
                      rfl

theorem cell22_377486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_377486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377486 prefixEnd_377486 := by exact prefixLift 377486
  have htrace : WordTrace (prefixWord ++ tailWord_377486) baseStart_377486 baseEnd_377486 := by
    simpa [prefixWord, tailWord_377486, baseEnd_377486] using wordTrace_append hprefix tailTrace_377486
  have hstable : (prefixWord ++ tailWord_377486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377486).length < 2 ^ (prefixWord ++ tailWord_377486).sum := by decide
  have hdescent : baseEnd_377486 < baseStart_377486 := by decide
  rcases family_descends (prefixWord ++ tailWord_377486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377544 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_377544 : Nat := 118140960795 + 377544 * 2 ^ 59
def prefixEnd_377544 : Nat := 4983230072969 + 3 ^ 40 * 377544 * 2
def baseEnd_377544 : Nat := 43080342271372464680825

theorem tailTrace_377544 : CollatzResearch.WordTrace tailWord_377544 prefixEnd_377544 43080342271372464680825 := by
  unfold tailWord_377544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6885080472115021113421843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9180107296153361484562457 6885080472115021113421843)
  ·
    refine ⟨10327620708172531670132765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6885080472115021113421843 10327620708172531670132765)
    ·
      refine ⟨3872857765564699376299787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10327620708172531670132765 3872857765564699376299787)
      ·
        refine ⟨5809286648347049064449681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872857765564699376299787 5809286648347049064449681)
        ·
          refine ⟨4356964986260286798337261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5809286648347049064449681 4356964986260286798337261)
          ·
            refine ⟨1633861869847607549376473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4356964986260286798337261 1633861869847607549376473)
            ·
              refine ⟨1225396402385705662032355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1633861869847607549376473 1225396402385705662032355)
              ·
                refine ⟨1838094603578558493048533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225396402385705662032355 1838094603578558493048533)
                ·
                  refine ⟨43080342271372464680825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1838094603578558493048533 43080342271372464680825)
                  ·
                    rfl

theorem cell22_377544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_377544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377544 prefixEnd_377544 := by exact prefixLift 377544
  have htrace : WordTrace (prefixWord ++ tailWord_377544) baseStart_377544 baseEnd_377544 := by
    simpa [prefixWord, tailWord_377544, baseEnd_377544] using wordTrace_append hprefix tailTrace_377544
  have hstable : (prefixWord ++ tailWord_377544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377544).length < 2 ^ (prefixWord ++ tailWord_377544).sum := by decide
  have hdescent : baseEnd_377544 < baseStart_377544 := by decide
  rcases family_descends (prefixWord ++ tailWord_377544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377548 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_377548 : Nat := 118140960795 + 377548 * 2 ^ 59
def prefixEnd_377548 : Nat := 4983230072969 + 3 ^ 40 * 377548 * 2
def baseEnd_377548 : Nat := 129242396095862716942463

theorem tailTrace_377548 : CollatzResearch.WordTrace tailWord_377548 prefixEnd_377548 129242396095862716942463 := by
  unfold tailWord_377548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6885153418107775454994649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9180204557477033939992865 6885153418107775454994649)
  ·
    refine ⟨5163865063580831591245987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6885153418107775454994649 5163865063580831591245987)
    ·
      refine ⟨7745797595371247386868981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163865063580831591245987 7745797595371247386868981)
      ·
        refine ⟨726168524566054442518967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7745797595371247386868981 726168524566054442518967)
        ·
          refine ⟨1089252786849081663778451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726168524566054442518967 1089252786849081663778451)
          ·
            refine ⟨1633879180273622495667677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089252786849081663778451 1633879180273622495667677)
            ·
              refine ⟨612704692602608435875379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1633879180273622495667677 612704692602608435875379)
              ·
                refine ⟨919057038903912653813069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612704692602608435875379 919057038903912653813069)
                ·
                  refine ⟨344646389588967245179901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 919057038903912653813069 344646389588967245179901)
                  ·
                    refine ⟨129242396095862716942463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344646389588967245179901 129242396095862716942463)
                    ·
                      rfl

theorem cell22_377548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_377548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377548 prefixEnd_377548 := by exact prefixLift 377548
  have htrace : WordTrace (prefixWord ++ tailWord_377548) baseStart_377548 baseEnd_377548 := by
    simpa [prefixWord, tailWord_377548, baseEnd_377548] using wordTrace_append hprefix tailTrace_377548
  have hstable : (prefixWord ++ tailWord_377548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377548).length < 2 ^ (prefixWord ++ tailWord_377548).sum := by decide
  have hdescent : baseEnd_377548 < baseStart_377548 := by decide
  rcases family_descends (prefixWord ++ tailWord_377548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377619 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_377619 : Nat := 118140960795 + 377619 * 2 ^ 59
def prefixEnd_377619 : Nat := 4983230072969 + 3 ^ 40 * 377619 * 2
def baseEnd_377619 : Nat := 129266700846842198417245

theorem tailTrace_377619 : CollatzResearch.WordTrace tailWord_377619 prefixEnd_377619 129266700846842198417245 := by
  unfold tailWord_377619
  simp only [CollatzResearch.WordTrace]
  refine ⟨13772896418958330035823911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9181930945972220023882607 13772896418958330035823911)
  ·
    refine ⟨20659344628437495053735867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13772896418958330035823911 20659344628437495053735867)
    ·
      refine ⟨30989016942656242580603801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20659344628437495053735867 30989016942656242580603801)
      ·
        refine ⟨23241762706992181935452851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30989016942656242580603801 23241762706992181935452851)
        ·
          refine ⟨34862644060488272903179277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23241762706992181935452851 34862644060488272903179277)
          ·
            refine ⟨13073491522683102338692229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34862644060488272903179277 13073491522683102338692229)
            ·
              refine ⟨2451279660503081688504793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13073491522683102338692229 2451279660503081688504793)
              ·
                refine ⟨1838459745377311266378595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451279660503081688504793 1838459745377311266378595)
                ·
                  refine ⟨2757689618065966899567893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838459745377311266378595 2757689618065966899567893)
                  ·
                    refine ⟨129266700846842198417245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2757689618065966899567893 129266700846842198417245)
                    ·
                      rfl

theorem cell22_377619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_377619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377619 prefixEnd_377619 := by exact prefixLift 377619
  have htrace : WordTrace (prefixWord ++ tailWord_377619) baseStart_377619 baseEnd_377619 := by
    simpa [prefixWord, tailWord_377619, baseEnd_377619] using wordTrace_append hprefix tailTrace_377619
  have hstable : (prefixWord ++ tailWord_377619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377619).length < 2 ^ (prefixWord ++ tailWord_377619).sum := by decide
  have hdescent : baseEnd_377619 < baseStart_377619 := by decide
  rcases family_descends (prefixWord ++ tailWord_377619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377621 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_377621 : Nat := 118140960795 + 377621 * 2 ^ 59
def prefixEnd_377621 : Nat := 4983230072969 + 3 ^ 40 * 377621 * 2
def baseEnd_377621 : Nat := 129267385487714859867239

theorem tailTrace_377621 : CollatzResearch.WordTrace tailWord_377621 prefixEnd_377621 129267385487714859867239 := by
  unfold tailWord_377621
  simp only [CollatzResearch.WordTrace]
  refine ⟨13772969364951084377396717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9181979576634056251597811 13772969364951084377396717)
  ·
    refine ⟨5164863511856656641523769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13772969364951084377396717 5164863511856656641523769)
    ·
      refine ⟨3873647633892492481142827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5164863511856656641523769 3873647633892492481142827)
      ·
        refine ⟨5810471450838738721714241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873647633892492481142827 5810471450838738721714241)
        ·
          refine ⟨4357853588129054041285681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5810471450838738721714241 4357853588129054041285681)
          ·
            refine ⟨3268390191096790530964261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4357853588129054041285681 3268390191096790530964261)
            ·
              refine ⟨612823160830648224555799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3268390191096790530964261 612823160830648224555799)
              ·
                refine ⟨919234741245972336833699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612823160830648224555799 919234741245972336833699)
                ·
                  refine ⟨1378852111868958505250549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919234741245972336833699 1378852111868958505250549)
                  ·
                    refine ⟨129267385487714859867239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1378852111868958505250549 129267385487714859867239)
                    ·
                      rfl

theorem cell22_377621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_377621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377621 prefixEnd_377621 := by exact prefixLift 377621
  have htrace : WordTrace (prefixWord ++ tailWord_377621) baseStart_377621 baseEnd_377621 := by
    simpa [prefixWord, tailWord_377621, baseEnd_377621] using wordTrace_append hprefix tailTrace_377621
  have hstable : (prefixWord ++ tailWord_377621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377621).length < 2 ^ (prefixWord ++ tailWord_377621).sum := by decide
  have hdescent : baseEnd_377621 < baseStart_377621 := by decide
  rcases family_descends (prefixWord ++ tailWord_377621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377664 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_377664 : Nat := 118140960795 + 377664 * 2 ^ 59
def prefixEnd_377664 : Nat := 4983230072969 + 3 ^ 40 * 377664 * 2
def baseEnd_377664 : Nat := 129282105266477081042107

theorem tailTrace_377664 : CollatzResearch.WordTrace tailWord_377664 prefixEnd_377664 129282105266477081042107 := by
  unfold tailWord_377664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887268851897651360606023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9183025135863535147474697 6887268851897651360606023)
  ·
    refine ⟨10330903277846477040909035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6887268851897651360606023 10330903277846477040909035)
    ·
      refine ⟨15496354916769715561363553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330903277846477040909035 15496354916769715561363553)
      ·
        refine ⟨11622266187577286671022665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15496354916769715561363553 11622266187577286671022665)
        ·
          refine ⟨8716699640682965003266999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11622266187577286671022665 8716699640682965003266999)
          ·
            refine ⟨13075049461024447504900499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716699640682965003266999 13075049461024447504900499)
            ·
              refine ⟨19612574191536671257350749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13075049461024447504900499 19612574191536671257350749)
              ·
                refine ⟨7354715321826251721506531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19612574191536671257350749 7354715321826251721506531)
                ·
                  refine ⟨11032072982739377582259797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354715321826251721506531 11032072982739377582259797)
                  ·
                    refine ⟨129282105266477081042107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11032072982739377582259797 129282105266477081042107)
                    ·
                      rfl

theorem cell22_377664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_377664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377664 prefixEnd_377664 := by exact prefixLift 377664
  have htrace : WordTrace (prefixWord ++ tailWord_377664) baseStart_377664 baseEnd_377664 := by
    simpa [prefixWord, tailWord_377664, baseEnd_377664] using wordTrace_append hprefix tailTrace_377664
  have hstable : (prefixWord ++ tailWord_377664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377664).length < 2 ^ (prefixWord ++ tailWord_377664).sum := by decide
  have hdescent : baseEnd_377664 < baseStart_377664 := by decide
  rcases family_descends (prefixWord ++ tailWord_377664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377790 : List Nat := [4, 2, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_377790 : Nat := 118140960795 + 377790 * 2 ^ 59
def prefixEnd_377790 : Nat := 4983230072969 + 3 ^ 40 * 377790 * 2
def baseEnd_377790 : Nat := 129325237641454752391721

theorem tailTrace_377790 : CollatzResearch.WordTrace tailWord_377790 prefixEnd_377790 129325237641454752391721 := by
  unfold tailWord_377790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722391662667353280037353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9186088867559217493532549 1722391662667353280037353)
  ·
    refine ⟨1291793747000514960028015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1722391662667353280037353 1291793747000514960028015)
    ·
      refine ⟨1937690620500772440042023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1291793747000514960028015 1937690620500772440042023)
      ·
        refine ⟨2906535930751158660063035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937690620500772440042023 2906535930751158660063035)
        ·
          refine ⟨4359803896126737990094553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906535930751158660063035 4359803896126737990094553)
          ·
            refine ⟨3269852922095053492570915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4359803896126737990094553 3269852922095053492570915)
            ·
              refine ⟨4904779383142580238856373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3269852922095053492570915 4904779383142580238856373)
              ·
                refine ⟨459823067169616897392785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4904779383142580238856373 459823067169616897392785)
                ·
                  refine ⟨344867300377212673044589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459823067169616897392785 344867300377212673044589)
                  ·
                    refine ⟨129325237641454752391721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344867300377212673044589 129325237641454752391721)
                    ·
                      rfl

theorem cell22_377790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_377790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377790 prefixEnd_377790 := by exact prefixLift 377790
  have htrace : WordTrace (prefixWord ++ tailWord_377790) baseStart_377790 baseEnd_377790 := by
    simpa [prefixWord, tailWord_377790, baseEnd_377790] using wordTrace_append hprefix tailTrace_377790
  have hstable : (prefixWord ++ tailWord_377790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377790).length < 2 ^ (prefixWord ++ tailWord_377790).sum := by decide
  have hdescent : baseEnd_377790 < baseStart_377790 := by decide
  rcases family_descends (prefixWord ++ tailWord_377790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377803 : List Nat := [1, 1, 1, 1, 3, 6, 3, 6]
def baseStart_377803 : Nat := 118140960795 + 377803 * 2 ^ 59
def prefixEnd_377803 : Nat := 4983230072969 + 3 ^ 40 * 377803 * 2
def baseEnd_377803 : Nat := 14369965311903005757409

theorem tailTrace_377803 : CollatzResearch.WordTrace tailWord_377803 prefixEnd_377803 14369965311903005757409 := by
  unfold tailWord_377803
  simp only [CollatzResearch.WordTrace]
  refine ⟨13779607450291729460522063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9186404966861152973681375 13779607450291729460522063)
  ·
    refine ⟨20669411175437594190783095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13779607450291729460522063 20669411175437594190783095)
    ·
      refine ⟨31004116763156391286174643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20669411175437594190783095 31004116763156391286174643)
      ·
        refine ⟨46506175144734586929261965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31004116763156391286174643 46506175144734586929261965)
        ·
          refine ⟨17439815679275470098473237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46506175144734586929261965 17439815679275470098473237)
          ·
            refine ⟨817491359966037660865933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17439815679275470098473237 817491359966037660865933)
            ·
              refine ⟨306559259987264122824725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 817491359966037660865933 306559259987264122824725)
              ·
                refine ⟨14369965311903005757409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306559259987264122824725 14369965311903005757409)
                ·
                  rfl

theorem cell22_377803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 6].length) (baseStart_377803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377803 prefixEnd_377803 := by exact prefixLift 377803
  have htrace : WordTrace (prefixWord ++ tailWord_377803) baseStart_377803 baseEnd_377803 := by
    simpa [prefixWord, tailWord_377803, baseEnd_377803] using wordTrace_append hprefix tailTrace_377803
  have hstable : (prefixWord ++ tailWord_377803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377803).length < 2 ^ (prefixWord ++ tailWord_377803).sum := by decide
  have hdescent : baseEnd_377803 < baseStart_377803 := by decide
  rcases family_descends (prefixWord ++ tailWord_377803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377854 : List Nat := [4, 2, 2, 2, 3, 1, 2, 6]
def baseStart_377854 : Nat := 118140960795 + 377854 * 2 ^ 59
def prefixEnd_377854 : Nat := 4983230072969 + 3 ^ 40 * 377854 * 2
def baseEnd_377854 : Nat := 14371905127708879865725

theorem tailTrace_377854 : CollatzResearch.WordTrace tailWord_377854 prefixEnd_377854 14371905127708879865725 := by
  unfold tailWord_377854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1722683446638370646328577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9187645048737976780419077 1722683446638370646328577)
  ·
    refine ⟨1292012584978777984746433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1722683446638370646328577 1292012584978777984746433)
    ·
      refine ⟨969009438734083488559825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292012584978777984746433 969009438734083488559825)
      ·
        refine ⟨726757079050562616419869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 969009438734083488559825 726757079050562616419869)
        ·
          refine ⟨272533904643960981157451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726757079050562616419869 272533904643960981157451)
          ·
            refine ⟨408800856965941471736177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272533904643960981157451 408800856965941471736177)
            ·
              refine ⟨306600642724456103802133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408800856965941471736177 306600642724456103802133)
              ·
                refine ⟨14371905127708879865725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306600642724456103802133 14371905127708879865725)
                ·
                  rfl

theorem cell22_377854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_377854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377854 prefixEnd_377854 := by exact prefixLift 377854
  have htrace : WordTrace (prefixWord ++ tailWord_377854) baseStart_377854 baseEnd_377854 := by
    simpa [prefixWord, tailWord_377854, baseEnd_377854] using wordTrace_append hprefix tailTrace_377854
  have hstable : (prefixWord ++ tailWord_377854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377854).length < 2 ^ (prefixWord ++ tailWord_377854).sum := by decide
  have hdescent : baseEnd_377854 < baseStart_377854 := by decide
  rcases family_descends (prefixWord ++ tailWord_377854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377912 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 1, 4]
def baseStart_377912 : Nat := 118140960795 + 377912 * 2 ^ 59
def prefixEnd_377912 : Nat := 4983230072969 + 3 ^ 40 * 377912 * 2
def baseEnd_377912 : Nat := 129367000734687100841347

theorem tailTrace_377912 : CollatzResearch.WordTrace tailWord_377912 prefixEnd_377912 129367000734687100841347 := by
  unfold tailWord_377912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891791503448420538119995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9189055337931227384159993 6891791503448420538119995)
  ·
    refine ⟨10337687255172630807179993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891791503448420538119995 10337687255172630807179993)
    ·
      refine ⟨7753265441379473105384995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10337687255172630807179993 7753265441379473105384995)
      ·
        refine ⟨11629898162069209658077493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753265441379473105384995 11629898162069209658077493)
        ·
          refine ⟨1090302952693988405444765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11629898162069209658077493 1090302952693988405444765)
          ·
            refine ⟨408863607260245652041787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1090302952693988405444765 408863607260245652041787)
            ·
              refine ⟨613295410890368478062681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 408863607260245652041787 613295410890368478062681)
              ·
                refine ⟨459971558167776358547011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613295410890368478062681 459971558167776358547011)
                ·
                  refine ⟨689957337251664537820517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459971558167776358547011 689957337251664537820517)
                  ·
                    refine ⟨129367000734687100841347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 689957337251664537820517 129367000734687100841347)
                    ·
                      rfl

theorem cell22_377912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_377912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377912 prefixEnd_377912 := by exact prefixLift 377912
  have htrace : WordTrace (prefixWord ++ tailWord_377912) baseStart_377912 baseEnd_377912 := by
    simpa [prefixWord, tailWord_377912, baseEnd_377912] using wordTrace_append hprefix tailTrace_377912
  have hstable : (prefixWord ++ tailWord_377912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377912).length < 2 ^ (prefixWord ++ tailWord_377912).sum := by decide
  have hdescent : baseEnd_377912 < baseStart_377912 := by decide
  rcases family_descends (prefixWord ++ tailWord_377912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377938 : List Nat := [3, 2, 2, 1, 3, 11]
def baseStart_377938 : Nat := 118140960795 + 377938 * 2 ^ 59
def prefixEnd_377938 : Nat := 4983230072969 + 3 ^ 40 * 377938 * 2
def baseEnd_377938 : Nat := 1597233346494218514707

theorem tailTrace_377938 : CollatzResearch.WordTrace tailWord_377938 prefixEnd_377938 1597233346494218514707 := by
  unfold tailWord_377938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446132826200661879171617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9189687536535098344457645 3446132826200661879171617)
  ·
    refine ⟨2584599619650496409378713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3446132826200661879171617 2584599619650496409378713)
    ·
      refine ⟨1938449714737872307034035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2584599619650496409378713 1938449714737872307034035)
      ·
        refine ⟨2907674572106808460551053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938449714737872307034035 2907674572106808460551053)
        ·
          refine ⟨1090377964540053172706645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2907674572106808460551053 1090377964540053172706645)
          ·
            refine ⟨1597233346494218514707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1090377964540053172706645 1597233346494218514707)
            ·
              rfl

theorem cell22_377938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 11].length) (baseStart_377938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377938 prefixEnd_377938 := by exact prefixLift 377938
  have htrace : WordTrace (prefixWord ++ tailWord_377938) baseStart_377938 baseEnd_377938 := by
    simpa [prefixWord, tailWord_377938, baseEnd_377938] using wordTrace_append hprefix tailTrace_377938
  have hstable : (prefixWord ++ tailWord_377938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377938).length < 2 ^ (prefixWord ++ tailWord_377938).sum := by decide
  have hdescent : baseEnd_377938 < baseStart_377938 := by decide
  rcases family_descends (prefixWord ++ tailWord_377938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377940 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_377940 : Nat := 118140960795 + 377940 * 2 ^ 59
def prefixEnd_377940 : Nat := 4983230072969 + 3 ^ 40 * 377940 * 2
def baseEnd_377940 : Nat := 129376585706904361141261

theorem tailTrace_377940 : CollatzResearch.WordTrace tailWord_377940 prefixEnd_377940 129376585706904361141261 := by
  unfold tailWord_377940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892302125397700929129637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9189736167196934572172849 6892302125397700929129637)
  ·
    refine ⟨1292306648512068924211807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6892302125397700929129637 1292306648512068924211807)
    ·
      refine ⟨1938459972768103386317711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292306648512068924211807 1938459972768103386317711)
      ·
        refine ⟨2907689959152155079476567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1938459972768103386317711 2907689959152155079476567)
        ·
          refine ⟨4361534938728232619214851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907689959152155079476567 4361534938728232619214851)
          ·
            refine ⟨6542302408092348928822277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361534938728232619214851 6542302408092348928822277)
            ·
              refine ⟨1226681701517315424154177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6542302408092348928822277 1226681701517315424154177)
              ·
                refine ⟨920011276137986568115633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226681701517315424154177 920011276137986568115633)
                ·
                  refine ⟨690008457103489926086725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920011276137986568115633 690008457103489926086725)
                  ·
                    refine ⟨129376585706904361141261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690008457103489926086725 129376585706904361141261)
                    ·
                      rfl

theorem cell22_377940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_377940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377940 prefixEnd_377940 := by exact prefixLift 377940
  have htrace : WordTrace (prefixWord ++ tailWord_377940) baseStart_377940 baseEnd_377940 := by
    simpa [prefixWord, tailWord_377940, baseEnd_377940] using wordTrace_append hprefix tailTrace_377940
  have hstable : (prefixWord ++ tailWord_377940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377940).length < 2 ^ (prefixWord ++ tailWord_377940).sum := by decide
  have hdescent : baseEnd_377940 < baseStart_377940 := by decide
  rcases family_descends (prefixWord ++ tailWord_377940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_377968 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_377968 : Nat := 118140960795 + 377968 * 2 ^ 59
def prefixEnd_377968 : Nat := 4983230072969 + 3 ^ 40 * 377968 * 2
def baseEnd_377968 : Nat := 129386170679121621441175

theorem tailTrace_377968 : CollatzResearch.WordTrace tailWord_377968 prefixEnd_377968 129386170679121621441175 := by
  unfold tailWord_377968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892812747346981320139279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9190416996462641760185705 6892812747346981320139279)
  ·
    refine ⟨10339219121020471980208919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892812747346981320139279 10339219121020471980208919)
    ·
      refine ⟨15508828681530707970313379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10339219121020471980208919 15508828681530707970313379)
      ·
        refine ⟨23263243022296061955470069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15508828681530707970313379 23263243022296061955470069)
        ·
          refine ⟨2180929033340255808325319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23263243022296061955470069 2180929033340255808325319)
          ·
            refine ⟨3271393550010383712487979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180929033340255808325319 3271393550010383712487979)
            ·
              refine ⟨4907090325015575568731969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3271393550010383712487979 4907090325015575568731969)
              ·
                refine ⟨3680317743761681676548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4907090325015575568731969 3680317743761681676548977)
                ·
                  refine ⟨2760238307821261257411733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680317743761681676548977 2760238307821261257411733)
                  ·
                    refine ⟨129386170679121621441175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2760238307821261257411733 129386170679121621441175)
                    ·
                      rfl

theorem cell22_377968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_377968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_377968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_377968 prefixEnd_377968 := by exact prefixLift 377968
  have htrace : WordTrace (prefixWord ++ tailWord_377968) baseStart_377968 baseEnd_377968 := by
    simpa [prefixWord, tailWord_377968, baseEnd_377968] using wordTrace_append hprefix tailTrace_377968
  have hstable : (prefixWord ++ tailWord_377968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_377968).length < 2 ^ (prefixWord ++ tailWord_377968).sum := by decide
  have hdescent : baseEnd_377968 < baseStart_377968 := by decide
  rcases family_descends (prefixWord ++ tailWord_377968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378017 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 5]
def baseStart_378017 : Nat := 118140960795 + 378017 * 2 ^ 59
def prefixEnd_378017 : Nat := 4983230072969 + 3 ^ 40 * 378017 * 2
def baseEnd_378017 : Nat := 43134314793500608988675

theorem tailTrace_378017 : CollatzResearch.WordTrace tailWord_378017 prefixEnd_378017 43134314793500608988675 := by
  unfold tailWord_378017
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787412671516444008812305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9191608447677629339208203 13787412671516444008812305)
  ·
    refine ⟨10340559503637333006609229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13787412671516444008812305 10340559503637333006609229)
    ·
      refine ⟨3877709813863999877478461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10340559503637333006609229 3877709813863999877478461)
      ·
        refine ⟨1454141180198999954054423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3877709813863999877478461 1454141180198999954054423)
        ·
          refine ⟨2181211770298499931081635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454141180198999954054423 2181211770298499931081635)
          ·
            refine ⟨3271817655447749896622453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181211770298499931081635 3271817655447749896622453)
            ·
              refine ⟨306732905198226552808355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3271817655447749896622453 306732905198226552808355)
              ·
                refine ⟨460099357797339829212533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306732905198226552808355 460099357797339829212533)
                ·
                  refine ⟨43134314793500608988675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 460099357797339829212533 43134314793500608988675)
                  ·
                    rfl

theorem cell22_378017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_378017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378017 prefixEnd_378017 := by exact prefixLift 378017
  have htrace : WordTrace (prefixWord ++ tailWord_378017) baseStart_378017 baseEnd_378017 := by
    simpa [prefixWord, tailWord_378017, baseEnd_378017] using wordTrace_append hprefix tailTrace_378017
  have hstable : (prefixWord ++ tailWord_378017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378017).length < 2 ^ (prefixWord ++ tailWord_378017).sum := by decide
  have hdescent : baseEnd_378017 < baseStart_378017 := by decide
  rcases family_descends (prefixWord ++ tailWord_378017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378028 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_378028 : Nat := 118140960795 + 378028 * 2 ^ 59
def prefixEnd_378028 : Nat := 4983230072969 + 3 ^ 40 * 378028 * 2
def baseEnd_378028 : Nat := 43135569968433821646997

theorem tailTrace_378028 : CollatzResearch.WordTrace tailWord_378028 prefixEnd_378028 43135569968433821646997 := by
  unfold tailWord_378028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893906937238296443731369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9191875916317728591641825 6893906937238296443731369)
  ·
    refine ⟨5170430202928722332798527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6893906937238296443731369 5170430202928722332798527)
    ·
      refine ⟨7755645304393083499197791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170430202928722332798527 7755645304393083499197791)
      ·
        refine ⟨11633467956589625248796687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755645304393083499197791 11633467956589625248796687)
        ·
          refine ⟨17450201934884437873195031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633467956589625248796687 17450201934884437873195031)
          ·
            refine ⟨26175302902326656809792547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17450201934884437873195031 26175302902326656809792547)
            ·
              refine ⟨39262954353489985214688821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26175302902326656809792547 39262954353489985214688821)
              ·
                refine ⟨3680901970639686113877077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39262954353489985214688821 3680901970639686113877077)
                ·
                  refine ⟨43135569968433821646997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3680901970639686113877077 43135569968433821646997)
                  ·
                    rfl

theorem cell22_378028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_378028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378028 prefixEnd_378028 := by exact prefixLift 378028
  have htrace : WordTrace (prefixWord ++ tailWord_378028) baseStart_378028 baseEnd_378028 := by
    simpa [prefixWord, tailWord_378028, baseEnd_378028] using wordTrace_append hprefix tailTrace_378028
  have hstable : (prefixWord ++ tailWord_378028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378028).length < 2 ^ (prefixWord ++ tailWord_378028).sum := by decide
  have hdescent : baseEnd_378028 < baseStart_378028 := by decide
  rcases family_descends (prefixWord ++ tailWord_378028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378068 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_378068 : Nat := 118140960795 + 378068 * 2 ^ 59
def prefixEnd_378068 : Nat := 4983230072969 + 3 ^ 40 * 378068 * 2
def baseEnd_378068 : Nat := 43140134240918231313623

theorem tailTrace_378068 : CollatzResearch.WordTrace tailWord_378068 prefixEnd_378068 43140134240918231313623 := by
  unfold tailWord_378068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6894636397165839859459429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9192848529554453145945905 6894636397165839859459429)
  ·
    refine ⟨1292744324468594973648643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6894636397165839859459429 1292744324468594973648643)
    ·
      refine ⟨1939116486702892460472965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292744324468594973648643 1939116486702892460472965)
      ·
        refine ⟨363584341256792336338681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1939116486702892460472965 363584341256792336338681)
        ·
          refine ⟨272688255942594252254011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363584341256792336338681 272688255942594252254011)
          ·
            refine ⟨409032383913891378381017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272688255942594252254011 409032383913891378381017)
            ·
              refine ⟨306774287935418533785763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409032383913891378381017 306774287935418533785763)
              ·
                refine ⟨460161431903127800678645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306774287935418533785763 460161431903127800678645)
                ·
                  refine ⟨43140134240918231313623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 460161431903127800678645 43140134240918231313623)
                  ·
                    rfl

theorem cell22_378068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_378068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378068 prefixEnd_378068 := by exact prefixLift 378068
  have htrace : WordTrace (prefixWord ++ tailWord_378068) baseStart_378068 baseEnd_378068 := by
    simpa [prefixWord, tailWord_378068, baseEnd_378068] using wordTrace_append hprefix tailTrace_378068
  have hstable : (prefixWord ++ tailWord_378068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378068).length < 2 ^ (prefixWord ++ tailWord_378068).sum := by decide
  have hdescent : baseEnd_378068 < baseStart_378068 := by decide
  rcases family_descends (prefixWord ++ tailWord_378068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378090 : List Nat := [3, 1, 3, 1, 1, 3, 2, 8]
def baseStart_378090 : Nat := 118140960795 + 378090 * 2 ^ 59
def prefixEnd_378090 : Nat := 4983230072969 + 3 ^ 40 * 378090 * 2
def baseEnd_378090 : Nat := 14380881530261552210089

theorem tailTrace_378090 : CollatzResearch.WordTrace tailWord_378090 prefixEnd_378090 14380881530261552210089 := by
  unfold tailWord_378090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447518800062994369054931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9193383466834651650813149 3447518800062994369054931)
  ·
    refine ⟨5171278200094491553582397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447518800062994369054931 5171278200094491553582397)
    ·
      refine ⟨1939229325035434332593399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5171278200094491553582397 1939229325035434332593399)
      ·
        refine ⟨2908843987553151498890099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939229325035434332593399 2908843987553151498890099)
        ·
          refine ⟨4363265981329727248335149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908843987553151498890099 4363265981329727248335149)
          ·
            refine ⟨1636224742998647718125681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4363265981329727248335149 1636224742998647718125681)
            ·
              refine ⟨1227168557248985788594261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636224742998647718125681 1227168557248985788594261)
              ·
                refine ⟨14380881530261552210089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1227168557248985788594261 14380881530261552210089)
                ·
                  rfl

theorem cell22_378090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_378090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378090 prefixEnd_378090 := by exact prefixLift 378090
  have htrace : WordTrace (prefixWord ++ tailWord_378090) baseStart_378090 baseEnd_378090 := by
    simpa [prefixWord, tailWord_378090, baseEnd_378090] using wordTrace_append hprefix tailTrace_378090
  have hstable : (prefixWord ++ tailWord_378090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378090).length < 2 ^ (prefixWord ++ tailWord_378090).sum := by decide
  have hdescent : baseEnd_378090 < baseStart_378090 := by decide
  rcases family_descends (prefixWord ++ tailWord_378090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378092 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_378092 : Nat := 118140960795 + 378092 * 2 ^ 59
def prefixEnd_378092 : Nat := 4983230072969 + 3 ^ 40 * 378092 * 2
def baseEnd_378092 : Nat := 129428618413226631340795

theorem tailTrace_378092 : CollatzResearch.WordTrace tailWord_378092 prefixEnd_378092 129428618413226631340795 := by
  unfold tailWord_378092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895074073122365908896265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9193432097496487878528353 6895074073122365908896265)
  ·
    refine ⟨5171305554841774431672199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6895074073122365908896265 5171305554841774431672199)
    ·
      refine ⟨7756958332262661647508299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171305554841774431672199 7756958332262661647508299)
      ·
        refine ⟨11635437498393992471262449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756958332262661647508299 11635437498393992471262449)
        ·
          refine ⟨8726578123795494353446837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11635437498393992471262449 8726578123795494353446837)
          ·
            refine ⟨818116699105827595635641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8726578123795494353446837 818116699105827595635641)
            ·
              refine ⟨613587524329370696726731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818116699105827595635641 613587524329370696726731)
              ·
                refine ⟨920381286494056045090097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613587524329370696726731 920381286494056045090097)
                ·
                  refine ⟨690285964870542033817573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920381286494056045090097 690285964870542033817573)
                  ·
                    refine ⟨129428618413226631340795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690285964870542033817573 129428618413226631340795)
                    ·
                      rfl

theorem cell22_378092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_378092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378092 prefixEnd_378092 := by exact prefixLift 378092
  have htrace : WordTrace (prefixWord ++ tailWord_378092) baseStart_378092 baseEnd_378092 := by
    simpa [prefixWord, tailWord_378092, baseEnd_378092] using wordTrace_append hprefix tailTrace_378092
  have hstable : (prefixWord ++ tailWord_378092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378092).length < 2 ^ (prefixWord ++ tailWord_378092).sum := by decide
  have hdescent : baseEnd_378092 < baseStart_378092 := by decide
  rcases family_descends (prefixWord ++ tailWord_378092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378122 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_378122 : Nat := 118140960795 + 378122 * 2 ^ 59
def prefixEnd_378122 : Nat := 4983230072969 + 3 ^ 40 * 378122 * 2
def baseEnd_378122 : Nat := 129438888026316553090703

theorem tailTrace_378122 : CollatzResearch.WordTrace tailWord_378122 prefixEnd_378122 129438888026316553090703 := by
  unfold tailWord_378122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447810584034011735346155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9194161557424031294256413 3447810584034011735346155)
  ·
    refine ⟨5171715876051017603019233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447810584034011735346155 5171715876051017603019233)
    ·
      refine ⟨3878786907038263202264425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5171715876051017603019233 3878786907038263202264425)
      ·
        refine ⟨2909090180278697401698319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3878786907038263202264425 2909090180278697401698319)
        ·
          refine ⟨4363635270418046102547479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909090180278697401698319 4363635270418046102547479)
          ·
            refine ⟨6545452905627069153821219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363635270418046102547479 6545452905627069153821219)
            ·
              refine ⟨9818179358440603730731829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6545452905627069153821219 9818179358440603730731829)
              ·
                refine ⟨920454314853806599756109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9818179358440603730731829 920454314853806599756109)
                ·
                  refine ⟨345170368070177474908541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 920454314853806599756109 345170368070177474908541)
                  ·
                    refine ⟨129438888026316553090703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345170368070177474908541 129438888026316553090703)
                    ·
                      rfl

theorem cell22_378122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_378122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378122 prefixEnd_378122 := by exact prefixLift 378122
  have htrace : WordTrace (prefixWord ++ tailWord_378122) baseStart_378122 baseEnd_378122 := by
    simpa [prefixWord, tailWord_378122, baseEnd_378122] using wordTrace_append hprefix tailTrace_378122
  have hstable : (prefixWord ++ tailWord_378122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378122).length < 2 ^ (prefixWord ++ tailWord_378122).sum := by decide
  have hdescent : baseEnd_378122 < baseStart_378122 := by decide
  rcases family_descends (prefixWord ++ tailWord_378122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378197 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 6]
def baseStart_378197 : Nat := 118140960795 + 378197 * 2 ^ 59
def prefixEnd_378197 : Nat := 4983230072969 + 3 ^ 40 * 378197 * 2
def baseEnd_378197 : Nat := 43154854019680452488491

theorem tailTrace_378197 : CollatzResearch.WordTrace tailWord_378197 prefixEnd_378197 43154854019680452488491 := by
  unfold tailWord_378197
  simp only [CollatzResearch.WordTrace]
  refine ⟨13793977810864334750364845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9195985207242889833576563 13793977810864334750364845)
  ·
    refine ⟨5172741679074125531386817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13793977810864334750364845 5172741679074125531386817)
    ·
      refine ⟨3879556259305594148540113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5172741679074125531386817 3879556259305594148540113)
      ·
        refine ⟨2909667194479195611405085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3879556259305594148540113 2909667194479195611405085)
        ·
          refine ⟨1091125197929698354276907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2909667194479195611405085 1091125197929698354276907)
          ·
            refine ⟨1636687796894547531415361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091125197929698354276907 1636687796894547531415361)
            ·
              refine ⟨1227515847670910648561521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636687796894547531415361 1227515847670910648561521)
              ·
                refine ⟨920636885753182986421141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227515847670910648561521 920636885753182986421141)
                ·
                  refine ⟨43154854019680452488491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 920636885753182986421141 43154854019680452488491)
                  ·
                    rfl

theorem cell22_378197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_378197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378197 prefixEnd_378197 := by exact prefixLift 378197
  have htrace : WordTrace (prefixWord ++ tailWord_378197) baseStart_378197 baseEnd_378197 := by
    simpa [prefixWord, tailWord_378197, baseEnd_378197] using wordTrace_append hprefix tailTrace_378197
  have hstable : (prefixWord ++ tailWord_378197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378197).length < 2 ^ (prefixWord ++ tailWord_378197).sum := by decide
  have hdescent : baseEnd_378197 < baseStart_378197 := by decide
  rcases family_descends (prefixWord ++ tailWord_378197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378199 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 1, 4]
def baseStart_378199 : Nat := 118140960795 + 378199 * 2 ^ 59
def prefixEnd_378199 : Nat := 4983230072969 + 3 ^ 40 * 378199 * 2
def baseEnd_378199 : Nat := 129465246699914018915467

theorem tailTrace_378199 : CollatzResearch.WordTrace tailWord_378199 prefixEnd_378199 129465246699914018915467 := by
  unfold tailWord_378199
  simp only [CollatzResearch.WordTrace]
  refine ⟨13794050756857089091937651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9196033837904726061291767 13794050756857089091937651)
  ·
    refine ⟨20691076135285633637906477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13794050756857089091937651 20691076135285633637906477)
    ·
      refine ⟨7759153550732112614214929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20691076135285633637906477 7759153550732112614214929)
      ·
        refine ⟨5819365163049084460661197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7759153550732112614214929 5819365163049084460661197)
        ·
          refine ⟨2182261936143406672747949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5819365163049084460661197 2182261936143406672747949)
          ·
            refine ⟨818348226053777502280481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2182261936143406672747949 818348226053777502280481)
            ·
              refine ⟨613761169540333126710361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818348226053777502280481 613761169540333126710361)
              ·
                refine ⟨460320877155249845032771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613761169540333126710361 460320877155249845032771)
                ·
                  refine ⟨690481315732874767549157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460320877155249845032771 690481315732874767549157)
                  ·
                    refine ⟨129465246699914018915467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690481315732874767549157 129465246699914018915467)
                    ·
                      rfl

theorem cell22_378199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_378199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378199 prefixEnd_378199 := by exact prefixLift 378199
  have htrace : WordTrace (prefixWord ++ tailWord_378199) baseStart_378199 baseEnd_378199 := by
    simpa [prefixWord, tailWord_378199, baseEnd_378199] using wordTrace_append hprefix tailTrace_378199
  have hstable : (prefixWord ++ tailWord_378199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378199).length < 2 ^ (prefixWord ++ tailWord_378199).sum := by decide
  have hdescent : baseEnd_378199 < baseStart_378199 := by decide
  rcases family_descends (prefixWord ++ tailWord_378199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378225 : List Nat := [1, 2, 2, 2, 1, 2, 12]
def baseStart_378225 : Nat := 118140960795 + 378225 * 2 ^ 59
def prefixEnd_378225 : Nat := 4983230072969 + 3 ^ 40 * 378225 * 2
def baseEnd_378225 : Nat := 4795338778935504361681

theorem tailTrace_378225 : CollatzResearch.WordTrace tailWord_378225 prefixEnd_378225 4795338778935504361681 := by
  unfold tailWord_378225
  simp only [CollatzResearch.WordTrace]
  refine ⟨13794999054762895532384129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9196666036508597021589419 13794999054762895532384129)
  ·
    refine ⟨10346249291072171649288097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13794999054762895532384129 10346249291072171649288097)
    ·
      refine ⟨7759686968304128736966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10346249291072171649288097 7759686968304128736966073)
      ·
        refine ⟨5819765226228096552724555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7759686968304128736966073 5819765226228096552724555)
        ·
          refine ⟨8729647839342144829086833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819765226228096552724555 8729647839342144829086833)
          ·
            refine ⟨6547235879506608621815125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729647839342144829086833 6547235879506608621815125)
            ·
              refine ⟨4795338778935504361681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 6547235879506608621815125 4795338778935504361681)
              ·
                rfl

theorem cell22_378225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 12].length) (baseStart_378225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378225 prefixEnd_378225 := by exact prefixLift 378225
  have htrace : WordTrace (prefixWord ++ tailWord_378225) baseStart_378225 baseEnd_378225 := by
    simpa [prefixWord, tailWord_378225, baseEnd_378225] using wordTrace_append hprefix tailTrace_378225
  have hstable : (prefixWord ++ tailWord_378225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378225).length < 2 ^ (prefixWord ++ tailWord_378225).sum := by decide
  have hdescent : baseEnd_378225 < baseStart_378225 := by decide
  rcases family_descends (prefixWord ++ tailWord_378225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378362 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_378362 : Nat := 118140960795 + 378362 * 2 ^ 59
def prefixEnd_378362 : Nat := 4983230072969 + 3 ^ 40 * 378362 * 2
def baseEnd_378362 : Nat := 129521044931035927089967

theorem tailTrace_378362 : CollatzResearch.WordTrace tailWord_378362 prefixEnd_378362 129521044931035927089967 := by
  unfold tailWord_378362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449998963816641982530335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9199997236844378620080893 3449998963816641982530335)
  ·
    refine ⟨5174998445724962973795503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3449998963816641982530335 5174998445724962973795503)
    ·
      refine ⟨7762497668587444460693255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5174998445724962973795503 7762497668587444460693255)
      ·
        refine ⟨11643746502881166691039883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762497668587444460693255 11643746502881166691039883)
        ·
          refine ⟨17465619754321750036559825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11643746502881166691039883 17465619754321750036559825)
          ·
            refine ⟨13099214815741312527419869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17465619754321750036559825 13099214815741312527419869)
            ·
              refine ⟨4912205555902992197782451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13099214815741312527419869 4912205555902992197782451)
              ·
                refine ⟨7368308333854488296673677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912205555902992197782451 7368308333854488296673677)
                ·
                  refine ⟨2763115625195433111252629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7368308333854488296673677 2763115625195433111252629)
                  ·
                    refine ⟨129521044931035927089967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2763115625195433111252629 129521044931035927089967)
                    ·
                      rfl

theorem cell22_378362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_378362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378362 prefixEnd_378362 := by exact prefixLift 378362
  have htrace : WordTrace (prefixWord ++ tailWord_378362) baseStart_378362 baseEnd_378362 := by
    simpa [prefixWord, tailWord_378362, baseEnd_378362] using wordTrace_append hprefix tailTrace_378362
  have hstable : (prefixWord ++ tailWord_378362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378362).length < 2 ^ (prefixWord ++ tailWord_378362).sum := by decide
  have hdescent : baseEnd_378362 < baseStart_378362 := by decide
  rcases family_descends (prefixWord ++ tailWord_378362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378364 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_378364 : Nat := 118140960795 + 378364 * 2 ^ 59
def prefixEnd_378364 : Nat := 4983230072969 + 3 ^ 40 * 378364 * 2
def baseEnd_378364 : Nat := 129521729571908588539961

theorem tailTrace_378364 : CollatzResearch.WordTrace tailWord_378364 prefixEnd_378364 129521729571908588539961 := by
  unfold tailWord_378364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900034400629661135847073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9200045867506214847796097 6900034400629661135847073)
  ·
    refine ⟨5175025800472245851885305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6900034400629661135847073 5175025800472245851885305)
    ·
      refine ⟨3881269350354184388913979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5175025800472245851885305 3881269350354184388913979)
      ·
        refine ⟨5821904025531276583370969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3881269350354184388913979 5821904025531276583370969)
        ·
          refine ⟨4366428019148457437528227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5821904025531276583370969 4366428019148457437528227)
          ·
            refine ⟨6549642028722686156292341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366428019148457437528227 6549642028722686156292341)
            ·
              refine ⟨614028940192751827152407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6549642028722686156292341 614028940192751827152407)
              ·
                refine ⟨921043410289127740728611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614028940192751827152407 921043410289127740728611)
                ·
                  refine ⟨1381565115433691611092917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921043410289127740728611 1381565115433691611092917)
                  ·
                    refine ⟨129521729571908588539961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1381565115433691611092917 129521729571908588539961)
                    ·
                      rfl

theorem cell22_378364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_378364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378364 prefixEnd_378364 := by exact prefixLift 378364
  have htrace : WordTrace (prefixWord ++ tailWord_378364) baseStart_378364 baseEnd_378364 := by
    simpa [prefixWord, tailWord_378364, baseEnd_378364] using wordTrace_append hprefix tailTrace_378364
  have hstable : (prefixWord ++ tailWord_378364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378364).length < 2 ^ (prefixWord ++ tailWord_378364).sum := by decide
  have hdescent : baseEnd_378364 < baseStart_378364 := by decide
  rcases family_descends (prefixWord ++ tailWord_378364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378377 : List Nat := [1, 2, 1, 1, 3, 1, 5, 8]
def baseStart_378377 : Nat := 118140960795 + 378377 * 2 ^ 59
def prefixEnd_378377 : Nat := 4983230072969 + 3 ^ 40 * 378377 * 2
def baseEnd_378377 : Nat := 14391797748620098662769

theorem tailTrace_378377 : CollatzResearch.WordTrace tailWord_378377 prefixEnd_378377 14391797748620098662769 := by
  unfold tailWord_378377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800542950212225491917385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9200361966808150327944923 13800542950212225491917385)
  ·
    refine ⟨10350407212659169118938039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13800542950212225491917385 10350407212659169118938039)
    ·
      refine ⟨15525610818988753678407059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10350407212659169118938039 15525610818988753678407059)
      ·
        refine ⟨23288416228483130517610589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15525610818988753678407059 23288416228483130517610589)
        ·
          refine ⟨8733156085681173944103971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23288416228483130517610589 8733156085681173944103971)
          ·
            refine ⟨13099734128521760916155957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8733156085681173944103971 13099734128521760916155957)
            ·
              refine ⟨1228100074548915085889621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13099734128521760916155957 1228100074548915085889621)
              ·
                refine ⟨14391797748620098662769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1228100074548915085889621 14391797748620098662769)
                ·
                  rfl

theorem cell22_378377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 8].length) (baseStart_378377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378377 prefixEnd_378377 := by exact prefixLift 378377
  have htrace : WordTrace (prefixWord ++ tailWord_378377) baseStart_378377 baseEnd_378377 := by
    simpa [prefixWord, tailWord_378377, baseEnd_378377] using wordTrace_append hprefix tailTrace_378377
  have hstable : (prefixWord ++ tailWord_378377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378377).length < 2 ^ (prefixWord ++ tailWord_378377).sum := by decide
  have hdescent : baseEnd_378377 < baseStart_378377 := by decide
  rcases family_descends (prefixWord ++ tailWord_378377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378460 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_378460 : Nat := 118140960795 + 378460 * 2 ^ 59
def prefixEnd_378460 : Nat := 4983230072969 + 3 ^ 40 * 378460 * 2
def baseEnd_378460 : Nat := 129554592333796338139667

theorem tailTrace_378460 : CollatzResearch.WordTrace tailWord_378460 prefixEnd_378460 129554592333796338139667 := by
  unfold tailWord_378460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901785104455765333594417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9202380139274353778125889 6901785104455765333594417)
  ·
    refine ⟨5176338828341824000195813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6901785104455765333594417 5176338828341824000195813)
    ·
      refine ⟨970563530314092000036715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5176338828341824000195813 970563530314092000036715)
      ·
        refine ⟨1455845295471138000055073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970563530314092000036715 1455845295471138000055073)
        ·
          refine ⟨1091883971603353500041305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455845295471138000055073 1091883971603353500041305)
          ·
            refine ⟨818912978702515125030979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091883971603353500041305 818912978702515125030979)
            ·
              refine ⟨1228369468053772687546469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818912978702515125030979 1228369468053772687546469)
              ·
                refine ⟨230319275260082378914963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1228369468053772687546469 230319275260082378914963)
                ·
                  refine ⟨345478912890123568372445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230319275260082378914963 345478912890123568372445)
                  ·
                    refine ⟨129554592333796338139667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345478912890123568372445 129554592333796338139667)
                    ·
                      rfl

theorem cell22_378460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_378460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378460 prefixEnd_378460 := by exact prefixLift 378460
  have htrace : WordTrace (prefixWord ++ tailWord_378460) baseStart_378460 baseEnd_378460 := by
    simpa [prefixWord, tailWord_378460, baseEnd_378460] using wordTrace_append hprefix tailTrace_378460
  have hstable : (prefixWord ++ tailWord_378460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378460).length < 2 ^ (prefixWord ++ tailWord_378460).sum := by decide
  have hdescent : baseEnd_378460 < baseStart_378460 := by decide
  rcases family_descends (prefixWord ++ tailWord_378460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378503 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 1, 4]
def baseStart_378503 : Nat := 118140960795 + 378503 * 2 ^ 59
def prefixEnd_378503 : Nat := 4983230072969 + 3 ^ 40 * 378503 * 2
def baseEnd_378503 : Nat := 129569312112558559314535

theorem tailTrace_378503 : CollatzResearch.WordTrace tailWord_378503 prefixEnd_378503 129569312112558559314535 := by
  unfold tailWord_378503
  simp only [CollatzResearch.WordTrace]
  refine ⟨13805138547755749011004163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9203425698503832674002775 13805138547755749011004163)
  ·
    refine ⟨20707707821633623516506245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13805138547755749011004163 20707707821633623516506245)
    ·
      refine ⟨3882695216556304409344921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20707707821633623516506245 3882695216556304409344921)
      ·
        refine ⟨2912021412417228307008691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3882695216556304409344921 2912021412417228307008691)
        ·
          refine ⟨4368032118625842460513037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2912021412417228307008691 4368032118625842460513037)
          ·
            refine ⟨1638012044484690922692389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4368032118625842460513037 1638012044484690922692389)
            ·
              refine ⟨307127258340879548004823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1638012044484690922692389 307127258340879548004823)
              ·
                refine ⟨460690887511319322007235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307127258340879548004823 460690887511319322007235)
                ·
                  refine ⟨691036331266978983010853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460690887511319322007235 691036331266978983010853)
                  ·
                    refine ⟨129569312112558559314535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691036331266978983010853 129569312112558559314535)
                    ·
                      rfl

theorem cell22_378503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_378503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378503 prefixEnd_378503 := by exact prefixLift 378503
  have htrace : WordTrace (prefixWord ++ tailWord_378503) baseStart_378503 baseEnd_378503 := by
    simpa [prefixWord, tailWord_378503, baseEnd_378503] using wordTrace_append hprefix tailTrace_378503
  have hstable : (prefixWord ++ tailWord_378503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378503).length < 2 ^ (prefixWord ++ tailWord_378503).sum := by decide
  have hdescent : baseEnd_378503 < baseStart_378503 := by decide
  rcases family_descends (prefixWord ++ tailWord_378503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378546 : List Nat := [3, 2, 1, 1, 1, 2, 6, 6]
def baseStart_378546 : Nat := 118140960795 + 378546 * 2 ^ 59
def prefixEnd_378546 : Nat := 4983230072969 + 3 ^ 40 * 378546 * 2
def baseEnd_378546 : Nat := 14398225765702308943267

theorem tailTrace_378546 : CollatzResearch.WordTrace tailWord_378546 prefixEnd_378546 14398225765702308943267 := by
  unfold tailWord_378546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451676721649991838704873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9204471257733311569879661 3451676721649991838704873)
  ·
    refine ⟨2588757541237493879028655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3451676721649991838704873 2588757541237493879028655)
    ·
      refine ⟨3883136311856240818542983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588757541237493879028655 3883136311856240818542983)
      ·
        refine ⟨5824704467784361227814475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3883136311856240818542983 5824704467784361227814475)
        ·
          refine ⟨8737056701676541841721713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824704467784361227814475 8737056701676541841721713)
          ·
            refine ⟨6552792526257406381291285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737056701676541841721713 6552792526257406381291285)
            ·
              refine ⟨307162149668315924123029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6552792526257406381291285 307162149668315924123029)
              ·
                refine ⟨14398225765702308943267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307162149668315924123029 14398225765702308943267)
                ·
                  rfl

theorem cell22_378546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_378546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378546 prefixEnd_378546 := by exact prefixLift 378546
  have htrace : WordTrace (prefixWord ++ tailWord_378546) baseStart_378546 baseEnd_378546 := by
    simpa [prefixWord, tailWord_378546, baseEnd_378546] using wordTrace_append hprefix tailTrace_378546
  have hstable : (prefixWord ++ tailWord_378546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378546).length < 2 ^ (prefixWord ++ tailWord_378546).sum := by decide
  have hdescent : baseEnd_378546 < baseStart_378546 := by decide
  rcases family_descends (prefixWord ++ tailWord_378546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378550 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_378550 : Nat := 118140960795 + 378550 * 2 ^ 59
def prefixEnd_378550 : Nat := 4983230072969 + 3 ^ 40 * 378550 * 2
def baseEnd_378550 : Nat := 129585401173066103389391

theorem tailTrace_378550 : CollatzResearch.WordTrace tailWord_378550 prefixEnd_378550 129585401173066103389391 := by
  unfold tailWord_378550
  simp only [CollatzResearch.WordTrace]
  refine ⟨862928298661592252372819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9204568519056984025310069 862928298661592252372819)
  ·
    refine ⟨1294392447992388378559229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 862928298661592252372819 1294392447992388378559229)
    ·
      refine ⟨485397167997145641959711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1294392447992388378559229 485397167997145641959711)
      ·
        refine ⟨728095751995718462939567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485397167997145641959711 728095751995718462939567)
        ·
          refine ⟨1092143627993577694409351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728095751995718462939567 1092143627993577694409351)
          ·
            refine ⟨1638215441990366541614027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092143627993577694409351 1638215441990366541614027)
            ·
              refine ⟨2457323162985549812421041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638215441990366541614027 2457323162985549812421041)
              ·
                refine ⟨1842992372239162359315781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457323162985549812421041 1842992372239162359315781)
                ·
                  refine ⟨345561069794842942371709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1842992372239162359315781 345561069794842942371709)
                  ·
                    refine ⟨129585401173066103389391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345561069794842942371709 129585401173066103389391)
                    ·
                      rfl

theorem cell22_378550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_378550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378550 prefixEnd_378550 := by exact prefixLift 378550
  have htrace : WordTrace (prefixWord ++ tailWord_378550) baseStart_378550 baseEnd_378550 := by
    simpa [prefixWord, tailWord_378550, baseEnd_378550] using wordTrace_append hprefix tailTrace_378550
  have hstable : (prefixWord ++ tailWord_378550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378550).length < 2 ^ (prefixWord ++ tailWord_378550).sum := by decide
  have hdescent : baseEnd_378550 < baseStart_378550 := by decide
  rcases family_descends (prefixWord ++ tailWord_378550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378591 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 5]
def baseStart_378591 : Nat := 118140960795 + 378591 * 2 ^ 59
def prefixEnd_378591 : Nat := 4983230072969 + 3 ^ 40 * 378591 * 2
def baseEnd_378591 : Nat := 43199812103651887704755

theorem tailTrace_378591 : CollatzResearch.WordTrace tailWord_378591 prefixEnd_378591 43199812103651887704755 := by
  unfold tailWord_378591
  simp only [CollatzResearch.WordTrace]
  refine ⟨13808348171436940040207627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9205565447624626693471751 13808348171436940040207627)
  ·
    refine ⟨20712522257155410060311441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13808348171436940040207627 20712522257155410060311441)
    ·
      refine ⟨15534391692866557545233581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20712522257155410060311441 15534391692866557545233581)
      ·
        refine ⟨5825396884824959079462593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15534391692866557545233581 5825396884824959079462593)
        ·
          refine ⟨4369047663618719309596945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5825396884824959079462593 4369047663618719309596945)
          ·
            refine ⟨3276785747714039482197709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369047663618719309596945 3276785747714039482197709)
            ·
              refine ⟨1228794655392764805824141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3276785747714039482197709 1228794655392764805824141)
              ·
                refine ⟨460797995772286802184053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1228794655392764805824141 460797995772286802184053)
                ·
                  refine ⟨43199812103651887704755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 460797995772286802184053 43199812103651887704755)
                  ·
                    rfl

theorem cell22_378591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 5].length) (baseStart_378591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378591 prefixEnd_378591 := by exact prefixLift 378591
  have htrace : WordTrace (prefixWord ++ tailWord_378591) baseStart_378591 baseEnd_378591 := by
    simpa [prefixWord, tailWord_378591, baseEnd_378591] using wordTrace_append hprefix tailTrace_378591
  have hstable : (prefixWord ++ tailWord_378591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378591).length < 2 ^ (prefixWord ++ tailWord_378591).sum := by decide
  have hdescent : baseEnd_378591 < baseStart_378591 := by decide
  rcases family_descends (prefixWord ++ tailWord_378591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378619 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 10]
def baseStart_378619 : Nat := 118140960795 + 378619 * 2 ^ 59
def prefixEnd_378619 : Nat := 4983230072969 + 3 ^ 40 * 378619 * 2
def baseEnd_378619 : Nat := 43203007094390974471393

theorem tailTrace_378619 : CollatzResearch.WordTrace tailWord_378619 prefixEnd_378619 43203007094390974471393 := by
  unfold tailWord_378619
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809369415335500822226911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9206246276890333881484607 13809369415335500822226911)
  ·
    refine ⟨20714054123003251233340367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13809369415335500822226911 20714054123003251233340367)
    ·
      refine ⟨31071081184504876850010551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20714054123003251233340367 31071081184504876850010551)
      ·
        refine ⟨46606621776757315275015827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31071081184504876850010551 46606621776757315275015827)
        ·
          refine ⟨69909932665135972912523741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46606621776757315275015827 69909932665135972912523741)
          ·
            refine ⟨26216224749425989842196403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69909932665135972912523741 26216224749425989842196403)
            ·
              refine ⟨39324337124138984763294605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26216224749425989842196403 39324337124138984763294605)
              ·
                refine ⟨14746626421552119286235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39324337124138984763294605 14746626421552119286235477)
                ·
                  refine ⟨43203007094390974471393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14746626421552119286235477 43203007094390974471393)
                  ·
                    rfl

theorem cell22_378619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_378619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378619 prefixEnd_378619 := by exact prefixLift 378619
  have htrace : WordTrace (prefixWord ++ tailWord_378619) baseStart_378619 baseEnd_378619 := by
    simpa [prefixWord, tailWord_378619, baseEnd_378619] using wordTrace_append hprefix tailTrace_378619
  have hstable : (prefixWord ++ tailWord_378619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378619).length < 2 ^ (prefixWord ++ tailWord_378619).sum := by decide
  have hdescent : baseEnd_378619 < baseStart_378619 := by decide
  rcases family_descends (prefixWord ++ tailWord_378619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378685 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_378685 : Nat := 118140960795 + 378685 * 2 ^ 59
def prefixEnd_378685 : Nat := 4983230072969 + 3 ^ 40 * 378685 * 2
def baseEnd_378685 : Nat := 129631614431970751263977

theorem tailTrace_378685 : CollatzResearch.WordTrace tailWord_378685 prefixEnd_378685 129631614431970751263977 := by
  unfold tailWord_378685
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811776633096394094129509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9207851088730929396086339 13811776633096394094129509)
  ·
    refine ⟨2589708118705573892649283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13811776633096394094129509 2589708118705573892649283)
    ·
      refine ⟨3884562178058360838973925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2589708118705573892649283 3884562178058360838973925)
      ·
        refine ⟨728355408385942657307611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3884562178058360838973925 728355408385942657307611)
        ·
          refine ⟨1092533112578913985961417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728355408385942657307611 1092533112578913985961417)
          ·
            refine ⟨819399834434185489471063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092533112578913985961417 819399834434185489471063)
            ·
              refine ⟨1229099751651278234206595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819399834434185489471063 1229099751651278234206595)
              ·
                refine ⟨1843649627476917351309893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229099751651278234206595 1843649627476917351309893)
                ·
                  refine ⟨345684305151922003370605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1843649627476917351309893 345684305151922003370605)
                  ·
                    refine ⟨129631614431970751263977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345684305151922003370605 129631614431970751263977)
                    ·
                      rfl

theorem cell22_378685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_378685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378685 prefixEnd_378685 := by exact prefixLift 378685
  have htrace : WordTrace (prefixWord ++ tailWord_378685) baseStart_378685 baseEnd_378685 := by
    simpa [prefixWord, tailWord_378685, baseEnd_378685] using wordTrace_append hprefix tailTrace_378685
  have hstable : (prefixWord ++ tailWord_378685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378685).length < 2 ^ (prefixWord ++ tailWord_378685).sum := by decide
  have hdescent : baseEnd_378685 < baseStart_378685 := by decide
  rcases family_descends (prefixWord ++ tailWord_378685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378713 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_378713 : Nat := 118140960795 + 378713 * 2 ^ 59
def prefixEnd_378713 : Nat := 4983230072969 + 3 ^ 40 * 378713 * 2
def baseEnd_378713 : Nat := 129641199404188011563891

theorem tailTrace_378713 : CollatzResearch.WordTrace tailWord_378713 prefixEnd_378713 129641199404188011563891 := by
  unfold tailWord_378713
  simp only [CollatzResearch.WordTrace]
  refine ⟨13812797876994954876148793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9208531917996636584099195 13812797876994954876148793)
  ·
    refine ⟨10359598407746216157111595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13812797876994954876148793 10359598407746216157111595)
    ·
      refine ⟨15539397611619324235667393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10359598407746216157111595 15539397611619324235667393)
      ·
        refine ⟨11654548208714493176750545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15539397611619324235667393 11654548208714493176750545)
        ·
          refine ⟨8740911156535869882562909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11654548208714493176750545 8740911156535869882562909)
          ·
            refine ⟨3277841683700951205961091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8740911156535869882562909 3277841683700951205961091)
            ·
              refine ⟨4916762525551426808941637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277841683700951205961091 4916762525551426808941637)
              ·
                refine ⟨921892973540892526676557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4916762525551426808941637 921892973540892526676557)
                ·
                  refine ⟨345709865077834697503709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921892973540892526676557 345709865077834697503709)
                  ·
                    refine ⟨129641199404188011563891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345709865077834697503709 129641199404188011563891)
                    ·
                      rfl

theorem cell22_378713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_378713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378713 prefixEnd_378713 := by exact prefixLift 378713
  have htrace : WordTrace (prefixWord ++ tailWord_378713) baseStart_378713 baseEnd_378713 := by
    simpa [prefixWord, tailWord_378713, baseEnd_378713] using wordTrace_append hprefix tailTrace_378713
  have hstable : (prefixWord ++ tailWord_378713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378713).length < 2 ^ (prefixWord ++ tailWord_378713).sum := by decide
  have hdescent : baseEnd_378713 < baseStart_378713 := by decide
  rcases family_descends (prefixWord ++ tailWord_378713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378760 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_378760 : Nat := 118140960795 + 378760 * 2 ^ 59
def prefixEnd_378760 : Nat := 4983230072969 + 3 ^ 40 * 378760 * 2
def baseEnd_378760 : Nat := 43219096154898518546249

theorem tailTrace_378760 : CollatzResearch.WordTrace tailWord_378760 prefixEnd_378760 43219096154898518546249 := by
  unfold tailWord_378760
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907256053912340951554867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9209674738549787935406489 6907256053912340951554867)
  ·
    refine ⟨10360884080868511427332301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6907256053912340951554867 10360884080868511427332301)
    ·
      refine ⟨3885331530325691785249613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10360884080868511427332301 3885331530325691785249613)
      ·
        refine ⟨1456999323872134419468605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3885331530325691785249613 1456999323872134419468605)
        ·
          refine ⟨546374746452050407300727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1456999323872134419468605 546374746452050407300727)
          ·
            refine ⟨819562119678075610951091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546374746452050407300727 819562119678075610951091)
            ·
              refine ⟨1229343179517113416426637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819562119678075610951091 1229343179517113416426637)
              ·
                refine ⟨461003692318917531159989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1229343179517113416426637 461003692318917531159989)
                ·
                  refine ⟨43219096154898518546249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461003692318917531159989 43219096154898518546249)
                  ·
                    rfl

theorem cell22_378760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_378760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378760 prefixEnd_378760 := by exact prefixLift 378760
  have htrace : WordTrace (prefixWord ++ tailWord_378760) baseStart_378760 baseEnd_378760 := by
    simpa [prefixWord, tailWord_378760, baseEnd_378760] using wordTrace_append hprefix tailTrace_378760
  have hstable : (prefixWord ++ tailWord_378760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378760).length < 2 ^ (prefixWord ++ tailWord_378760).sum := by decide
  have hdescent : baseEnd_378760 < baseStart_378760 := by decide
  rcases family_descends (prefixWord ++ tailWord_378760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378773 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_378773 : Nat := 118140960795 + 378773 * 2 ^ 59
def prefixEnd_378773 : Nat := 4983230072969 + 3 ^ 40 * 378773 * 2
def baseEnd_378773 : Nat := 129661738630367855063707

theorem tailTrace_378773 : CollatzResearch.WordTrace tailWord_378773 prefixEnd_378773 129661738630367855063707 := by
  unfold tailWord_378773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814986256777585123332973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9209990837851723415555315 13814986256777585123332973)
  ·
    refine ⟨5180619846291594421249865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13814986256777585123332973 5180619846291594421249865)
    ·
      refine ⟨3885464884718695815937399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5180619846291594421249865 3885464884718695815937399)
      ·
        refine ⟨5828197327078043723906099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885464884718695815937399 5828197327078043723906099)
        ·
          refine ⟨8742295990617065585859149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828197327078043723906099 8742295990617065585859149)
          ·
            refine ⟨3278360996481399594697181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8742295990617065585859149 3278360996481399594697181)
            ·
              refine ⟨1229385373680524848011443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3278360996481399594697181 1229385373680524848011443)
              ·
                refine ⟨1844078060520787272017165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229385373680524848011443 1844078060520787272017165)
                ·
                  refine ⟨691529272695295227006437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1844078060520787272017165 691529272695295227006437)
                  ·
                    refine ⟨129661738630367855063707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691529272695295227006437 129661738630367855063707)
                    ·
                      rfl

theorem cell22_378773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_378773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378773 prefixEnd_378773 := by exact prefixLift 378773
  have htrace : WordTrace (prefixWord ++ tailWord_378773) baseStart_378773 baseEnd_378773 := by
    simpa [prefixWord, tailWord_378773, baseEnd_378773] using wordTrace_append hprefix tailTrace_378773
  have hstable : (prefixWord ++ tailWord_378773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378773).length < 2 ^ (prefixWord ++ tailWord_378773).sum := by decide
  have hdescent : baseEnd_378773 < baseStart_378773 := by decide
  rcases family_descends (prefixWord ++ tailWord_378773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378798 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_378798 : Nat := 118140960795 + 378798 * 2 ^ 59
def prefixEnd_378798 : Nat := 4983230072969 + 3 ^ 40 * 378798 * 2
def baseEnd_378798 : Nat := 129670296641276123188631

theorem tailTrace_378798 : CollatzResearch.WordTrace tailWord_378798 prefixEnd_378798 129670296641276123188631 := by
  unfold tailWord_378798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726987260210876799124131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9210598721124676261995365 1726987260210876799124131)
  ·
    refine ⟨2590480890316315198686197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726987260210876799124131 2590480890316315198686197)
    ·
      refine ⟨242857583467154549876831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2590480890316315198686197 242857583467154549876831)
      ·
        refine ⟨364286375200731824815247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242857583467154549876831 364286375200731824815247)
        ·
          refine ⟨546429562801097737222871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364286375200731824815247 546429562801097737222871)
          ·
            refine ⟨819644344201646605834307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546429562801097737222871 819644344201646605834307)
            ·
              refine ⟨1229466516302469908751461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819644344201646605834307 1229466516302469908751461)
              ·
                refine ⟨230524971806713107890899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1229466516302469908751461 230524971806713107890899)
                ·
                  refine ⟨345787457710069661836349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230524971806713107890899 345787457710069661836349)
                  ·
                    refine ⟨129670296641276123188631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345787457710069661836349 129670296641276123188631)
                    ·
                      rfl

theorem cell22_378798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_378798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378798 prefixEnd_378798 := by exact prefixLift 378798
  have htrace : WordTrace (prefixWord ++ tailWord_378798) baseStart_378798 baseEnd_378798 := by
    simpa [prefixWord, tailWord_378798, baseEnd_378798] using wordTrace_append hprefix tailTrace_378798
  have hstable : (prefixWord ++ tailWord_378798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378798).length < 2 ^ (prefixWord ++ tailWord_378798).sum := by decide
  have hdescent : baseEnd_378798 < baseStart_378798 := by decide
  rcases family_descends (prefixWord ++ tailWord_378798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378884 : List Nat := [2, 3, 2, 4, 1, 2, 2, 6]
def baseStart_378884 : Nat := 118140960795 + 378884 * 2 ^ 59
def prefixEnd_378884 : Nat := 4983230072969 + 3 ^ 40 * 378884 * 2
def baseEnd_378884 : Nat := 14411081799866729504263

theorem tailTrace_378884 : CollatzResearch.WordTrace tailWord_378884 prefixEnd_378884 14411081799866729504263 := by
  unfold tailWord_378884
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909517379687725540311853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9212689839583634053749137 6909517379687725540311853)
  ·
    refine ⟨2591069017382897077616945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6909517379687725540311853 2591069017382897077616945)
    ·
      refine ⟨1943301763037172808212709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2591069017382897077616945 1943301763037172808212709)
      ·
        refine ⟨364369080569469901539883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1943301763037172808212709 364369080569469901539883)
        ·
          refine ⟨546553620854204852309825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364369080569469901539883 546553620854204852309825)
          ·
            refine ⟨409915215640653639232369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546553620854204852309825 409915215640653639232369)
            ·
              refine ⟨307436411730490229424277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409915215640653639232369 307436411730490229424277)
              ·
                refine ⟨14411081799866729504263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307436411730490229424277 14411081799866729504263)
                ·
                  rfl

theorem cell22_378884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 6].length) (baseStart_378884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378884 prefixEnd_378884 := by exact prefixLift 378884
  have htrace : WordTrace (prefixWord ++ tailWord_378884) baseStart_378884 baseEnd_378884 := by
    simpa [prefixWord, tailWord_378884, baseEnd_378884] using wordTrace_append hprefix tailTrace_378884
  have hstable : (prefixWord ++ tailWord_378884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378884).length < 2 ^ (prefixWord ++ tailWord_378884).sum := by decide
  have hdescent : baseEnd_378884 < baseStart_378884 := by decide
  rcases family_descends (prefixWord ++ tailWord_378884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378916 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_378916 : Nat := 118140960795 + 378916 * 2 ^ 59
def prefixEnd_378916 : Nat := 4983230072969 + 3 ^ 40 * 378916 * 2
def baseEnd_378916 : Nat := 129710690452763148738269

theorem tailTrace_378916 : CollatzResearch.WordTrace tailWord_378916 prefixEnd_378916 129710690452763148738269 := by
  unfold tailWord_378916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910100947629760272894301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9213467930173013697192401 6910100947629760272894301)
  ·
    refine ⟨2591287855361160102335363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6910100947629760272894301 2591287855361160102335363)
    ·
      refine ⟨3886931783041740153503045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591287855361160102335363 3886931783041740153503045)
      ·
        refine ⟨728799709320326278781821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3886931783041740153503045 728799709320326278781821)
        ·
          refine ⟨273299890995122354543183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 728799709320326278781821 273299890995122354543183)
          ·
            refine ⟨409949836492683531814775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273299890995122354543183 409949836492683531814775)
            ·
              refine ⟨614924754739025297722163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409949836492683531814775 614924754739025297722163)
              ·
                refine ⟨922387132108537946583245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614924754739025297722163 922387132108537946583245)
                ·
                  refine ⟨345895174540701729968717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922387132108537946583245 345895174540701729968717)
                  ·
                    refine ⟨129710690452763148738269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345895174540701729968717 129710690452763148738269)
                    ·
                      rfl

theorem cell22_378916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_378916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378916 prefixEnd_378916 := by exact prefixLift 378916
  have htrace : WordTrace (prefixWord ++ tailWord_378916) baseStart_378916 baseEnd_378916 := by
    simpa [prefixWord, tailWord_378916, baseEnd_378916] using wordTrace_append hprefix tailTrace_378916
  have hstable : (prefixWord ++ tailWord_378916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378916).length < 2 ^ (prefixWord ++ tailWord_378916).sum := by decide
  have hdescent : baseEnd_378916 < baseStart_378916 := by decide
  rcases family_descends (prefixWord ++ tailWord_378916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378923 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 6]
def baseStart_378923 : Nat := 118140960795 + 378923 * 2 ^ 59
def prefixEnd_378923 : Nat := 4983230072969 + 3 ^ 40 * 378923 * 2
def baseEnd_378923 : Nat := 43237695565272487937749

theorem tailTrace_378923 : CollatzResearch.WordTrace tailWord_378923 prefixEnd_378923 43237695565272487937749 := by
  unfold tailWord_378923
  simp only [CollatzResearch.WordTrace]
  refine ⟨13820457206234160741293423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9213638137489440494195615 13820457206234160741293423)
  ·
    refine ⟨20730685809351241111940135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13820457206234160741293423 20730685809351241111940135)
    ·
      refine ⟨31096028714026861667910203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20730685809351241111940135 31096028714026861667910203)
      ·
        refine ⟨46644043071040292501865305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31096028714026861667910203 46644043071040292501865305)
        ·
          refine ⟨34983032303280219376398979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46644043071040292501865305 34983032303280219376398979)
          ·
            refine ⟨52474548454920329064598469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34983032303280219376398979 52474548454920329064598469)
            ·
              refine ⟨9838977835297561699612213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52474548454920329064598469 9838977835297561699612213)
              ·
                refine ⟨922404172059146409338645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9838977835297561699612213 922404172059146409338645)
                ·
                  refine ⟨43237695565272487937749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 922404172059146409338645 43237695565272487937749)
                  ·
                    rfl

theorem cell22_378923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_378923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378923 prefixEnd_378923 := by exact prefixLift 378923
  have htrace : WordTrace (prefixWord ++ tailWord_378923) baseStart_378923 baseEnd_378923 := by
    simpa [prefixWord, tailWord_378923, baseEnd_378923] using wordTrace_append hprefix tailTrace_378923
  have hstable : (prefixWord ++ tailWord_378923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378923).length < 2 ^ (prefixWord ++ tailWord_378923).sum := by decide
  have hdescent : baseEnd_378923 < baseStart_378923 := by decide
  rcases family_descends (prefixWord ++ tailWord_378923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378968 : List Nat := [2, 1, 2, 2, 1, 14]
def baseStart_378968 : Nat := 118140960795 + 378968 * 2 ^ 59
def prefixEnd_378968 : Nat := 4983230072969 + 3 ^ 40 * 378968 * 2
def baseEnd_378968 : Nat := 1601586310067312918989

theorem tailTrace_378968 : CollatzResearch.WordTrace tailWord_378968 prefixEnd_378968 1601586310067312918989 := by
  unfold tailWord_378968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911049245535566713340779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9214732327380755617787705 6911049245535566713340779)
  ·
    refine ⟨10366573868303350070011169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6911049245535566713340779 10366573868303350070011169)
    ·
      refine ⟨7774930401227512552508377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10366573868303350070011169 7774930401227512552508377)
      ·
        refine ⟨5831197800920634414381283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7774930401227512552508377 5831197800920634414381283)
        ·
          refine ⟨8746796701380951621571925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831197800920634414381283 8746796701380951621571925)
          ·
            refine ⟨1601586310067312918989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 8746796701380951621571925 1601586310067312918989)
            ·
              rfl

theorem cell22_378968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 14].length) (baseStart_378968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378968 prefixEnd_378968 := by exact prefixLift 378968
  have htrace : WordTrace (prefixWord ++ tailWord_378968) baseStart_378968 baseEnd_378968 := by
    simpa [prefixWord, tailWord_378968, baseEnd_378968] using wordTrace_append hprefix tailTrace_378968
  have hstable : (prefixWord ++ tailWord_378968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378968).length < 2 ^ (prefixWord ++ tailWord_378968).sum := by decide
  have hdescent : baseEnd_378968 < baseStart_378968 := by decide
  rcases family_descends (prefixWord ++ tailWord_378968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378970 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_378970 : Nat := 118140960795 + 378970 * 2 ^ 59
def prefixEnd_378970 : Nat := 4983230072969 + 3 ^ 40 * 378970 * 2
def baseEnd_378970 : Nat := 129729175756325007888103

theorem tailTrace_378970 : CollatzResearch.WordTrace tailWord_378970 prefixEnd_378970 129729175756325007888103 := by
  unfold tailWord_378970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455542859265971942063591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9214780958042591845502909 3455542859265971942063591)
  ·
    refine ⟨5183314288898957913095387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3455542859265971942063591 5183314288898957913095387)
    ·
      refine ⟨7774971433348436869643081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5183314288898957913095387 7774971433348436869643081)
      ·
        refine ⟨5831228575011327652232311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7774971433348436869643081 5831228575011327652232311)
        ·
          refine ⟨8746842862516991478348467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831228575011327652232311 8746842862516991478348467)
          ·
            refine ⟨13120264293775487217522701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746842862516991478348467 13120264293775487217522701)
            ·
              refine ⟨4920099110165807706571013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13120264293775487217522701 4920099110165807706571013)
              ·
                refine ⟨922518583156088944982065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4920099110165807706571013 922518583156088944982065)
                ·
                  refine ⟨691888937367066708736549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 922518583156088944982065 691888937367066708736549)
                  ·
                    refine ⟨129729175756325007888103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691888937367066708736549 129729175756325007888103)
                    ·
                      rfl

theorem cell22_378970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_378970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_378970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_378970 prefixEnd_378970 := by exact prefixLift 378970
  have htrace : WordTrace (prefixWord ++ tailWord_378970) baseStart_378970 baseEnd_378970 := by
    simpa [prefixWord, tailWord_378970, baseEnd_378970] using wordTrace_append hprefix tailTrace_378970
  have hstable : (prefixWord ++ tailWord_378970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378970).length < 2 ^ (prefixWord ++ tailWord_378970).sum := by decide
  have hdescent : baseEnd_378970 < baseStart_378970 := by decide
  rcases family_descends (prefixWord ++ tailWord_378970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379045 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_379045 : Nat := 118140960795 + 379045 * 2 ^ 59
def prefixEnd_379045 : Nat := 4983230072969 + 3 ^ 40 * 379045 * 2
def baseEnd_379045 : Nat := 129754849789049812262873

theorem tailTrace_379045 : CollatzResearch.WordTrace tailWord_379045 prefixEnd_379045 129754849789049812262873 := by
  unfold tailWord_379045
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824906911792175577234589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9216604607861450384823059 13824906911792175577234589)
  ·
    refine ⟨5184340091922065841462971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13824906911792175577234589 5184340091922065841462971)
    ·
      refine ⟨7776510137883098762194457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184340091922065841462971 7776510137883098762194457)
      ·
        refine ⟨5832382603412324071645843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7776510137883098762194457 5832382603412324071645843)
        ·
          refine ⟨8748573905118486107468765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5832382603412324071645843 8748573905118486107468765)
          ·
            refine ⟨3280715214419432290300787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8748573905118486107468765 3280715214419432290300787)
            ·
              refine ⟨4921072821629148435451181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280715214419432290300787 4921072821629148435451181)
              ·
                refine ⟨1845402308110930663294193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4921072821629148435451181 1845402308110930663294193)
                ·
                  refine ⟨1384051731083197997470645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845402308110930663294193 1384051731083197997470645)
                  ·
                    refine ⟨129754849789049812262873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1384051731083197997470645 129754849789049812262873)
                    ·
                      rfl

theorem cell22_379045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_379045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379045 prefixEnd_379045 := by exact prefixLift 379045
  have htrace : WordTrace (prefixWord ++ tailWord_379045) baseStart_379045 baseEnd_379045 := by
    simpa [prefixWord, tailWord_379045, baseEnd_379045] using wordTrace_append hprefix tailTrace_379045
  have hstable : (prefixWord ++ tailWord_379045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379045).length < 2 ^ (prefixWord ++ tailWord_379045).sum := by decide
  have hdescent : baseEnd_379045 < baseStart_379045 := by decide
  rcases family_descends (prefixWord ++ tailWord_379045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379068 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_379068 : Nat := 118140960795 + 379068 * 2 ^ 59
def prefixEnd_379068 : Nat := 4983230072969 + 3 ^ 40 * 379068 * 2
def baseEnd_379068 : Nat := 129762723159085418937803

theorem tailTrace_379068 : CollatzResearch.WordTrace tailWord_379068 prefixEnd_379068 129762723159085418937803 := by
  unfold tailWord_379068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912872895354425252660929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9217163860472567003547905 6912872895354425252660929)
  ·
    refine ⟨5184654671515818939495697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6912872895354425252660929 5184654671515818939495697)
    ·
      refine ⟨3888491003636864204621773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5184654671515818939495697 3888491003636864204621773)
      ·
        refine ⟨1458184126363824076733165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3888491003636864204621773 1458184126363824076733165)
        ·
          refine ⟨546819047386434028774937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1458184126363824076733165 546819047386434028774937)
          ·
            refine ⟨410114285539825521581203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546819047386434028774937 410114285539825521581203)
            ·
              refine ⟨615171428309738282371805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410114285539825521581203 615171428309738282371805)
              ·
                refine ⟨230689285616151855889427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615171428309738282371805 230689285616151855889427)
                ·
                  refine ⟨346033928424227783834141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230689285616151855889427 346033928424227783834141)
                  ·
                    refine ⟨129762723159085418937803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346033928424227783834141 129762723159085418937803)
                    ·
                      rfl

theorem cell22_379068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_379068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379068 prefixEnd_379068 := by exact prefixLift 379068
  have htrace : WordTrace (prefixWord ++ tailWord_379068) baseStart_379068 baseEnd_379068 := by
    simpa [prefixWord, tailWord_379068, baseEnd_379068] using wordTrace_append hprefix tailTrace_379068
  have hstable : (prefixWord ++ tailWord_379068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379068).length < 2 ^ (prefixWord ++ tailWord_379068).sum := by decide
  have hdescent : baseEnd_379068 < baseStart_379068 := by decide
  rcases family_descends (prefixWord ++ tailWord_379068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379077 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_379077 : Nat := 118140960795 + 379077 * 2 ^ 59
def prefixEnd_379077 : Nat := 4983230072969 + 3 ^ 40 * 379077 * 2
def baseEnd_379077 : Nat := 129765804043012395462775

theorem tailTrace_379077 : CollatzResearch.WordTrace tailWord_379077 prefixEnd_379077 129765804043012395462775 := by
  unfold tailWord_379077
  simp only [CollatzResearch.WordTrace]
  refine ⟨13826074047676245042399485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9217382698450830028266323 13826074047676245042399485)
  ·
    refine ⟨5184777767878591890899807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13826074047676245042399485 5184777767878591890899807)
    ·
      refine ⟨7777166651817887836349711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184777767878591890899807 7777166651817887836349711)
      ·
        refine ⟨11665749977726831754524567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7777166651817887836349711 11665749977726831754524567)
        ·
          refine ⟨17498624966590247631786851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11665749977726831754524567 17498624966590247631786851)
          ·
            refine ⟨26247937449885371447680277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17498624966590247631786851 26247937449885371447680277)
            ·
              refine ⟨1230372067963376786610013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26247937449885371447680277 1230372067963376786610013)
              ·
                refine ⟨461389525486266294978755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1230372067963376786610013 461389525486266294978755)
                ·
                  refine ⟨692084288229399442468133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461389525486266294978755 692084288229399442468133)
                  ·
                    refine ⟨129765804043012395462775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692084288229399442468133 129765804043012395462775)
                    ·
                      rfl

theorem cell22_379077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_379077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379077 prefixEnd_379077 := by exact prefixLift 379077
  have htrace : WordTrace (prefixWord ++ tailWord_379077) baseStart_379077 baseEnd_379077 := by
    simpa [prefixWord, tailWord_379077, baseEnd_379077] using wordTrace_append hprefix tailTrace_379077
  have hstable : (prefixWord ++ tailWord_379077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379077).length < 2 ^ (prefixWord ++ tailWord_379077).sum := by decide
  have hdescent : baseEnd_379077 < baseStart_379077 := by decide
  rcases family_descends (prefixWord ++ tailWord_379077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379111 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 1, 4]
def baseStart_379111 : Nat := 118140960795 + 379111 * 2 ^ 59
def prefixEnd_379111 : Nat := 4983230072969 + 3 ^ 40 * 379111 * 2
def baseEnd_379111 : Nat := 129777442937847640112671

theorem tailTrace_379111 : CollatzResearch.WordTrace tailWord_379111 prefixEnd_379111 129777442937847640112671 := by
  unfold tailWord_379111
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827314129553068849137187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9218209419702045899424791 13827314129553068849137187)
  ·
    refine ⟨20740971194329603273705781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13827314129553068849137187 20740971194329603273705781)
    ·
      refine ⟨1944466049468400306909917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20740971194329603273705781 1944466049468400306909917)
      ·
        refine ⟨729174768550650115091219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1944466049468400306909917 729174768550650115091219)
        ·
          refine ⟨1093762152825975172636829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729174768550650115091219 1093762152825975172636829)
          ·
            refine ⟨410160807309740689738811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1093762152825975172636829 410160807309740689738811)
            ·
              refine ⟨615241210964611034608217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410160807309740689738811 615241210964611034608217)
              ·
                refine ⟨461430908223458275956163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615241210964611034608217 461430908223458275956163)
                ·
                  refine ⟨692146362335187413934245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461430908223458275956163 692146362335187413934245)
                  ·
                    refine ⟨129777442937847640112671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692146362335187413934245 129777442937847640112671)
                    ·
                      rfl

theorem cell22_379111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_379111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379111 prefixEnd_379111 := by exact prefixLift 379111
  have htrace : WordTrace (prefixWord ++ tailWord_379111) baseStart_379111 baseEnd_379111 := by
    simpa [prefixWord, tailWord_379111, baseEnd_379111] using wordTrace_append hprefix tailTrace_379111
  have hstable : (prefixWord ++ tailWord_379111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379111).length < 2 ^ (prefixWord ++ tailWord_379111).sum := by decide
  have hdescent : baseEnd_379111 < baseStart_379111 := by decide
  rcases family_descends (prefixWord ++ tailWord_379111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379259 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 4, 3]
def baseStart_379259 : Nat := 118140960795 + 379259 * 2 ^ 59
def prefixEnd_379259 : Nat := 4983230072969 + 3 ^ 40 * 379259 * 2
def baseEnd_379259 : Nat := 129828106362424587412217

theorem tailTrace_379259 : CollatzResearch.WordTrace tailWord_379259 prefixEnd_379259 129828106362424587412217 := by
  unfold tailWord_379259
  simp only [CollatzResearch.WordTrace]
  refine ⟨13832712133016890125524831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9221808088677926750349887 13832712133016890125524831)
  ·
    refine ⟨20749068199525335188287247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13832712133016890125524831 20749068199525335188287247)
    ·
      refine ⟨31123602299288002782430871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20749068199525335188287247 31123602299288002782430871)
      ·
        refine ⟨46685403448932004173646307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31123602299288002782430871 46685403448932004173646307)
        ·
          refine ⟨70028105173398006260469461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46685403448932004173646307 70028105173398006260469461)
          ·
            refine ⟨1641283715001515771729753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70028105173398006260469461 1641283715001515771729753)
            ·
              refine ⟨1230962786251136828797315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641283715001515771729753 1230962786251136828797315)
              ·
                refine ⟨1846444179376705243195973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230962786251136828797315 1846444179376705243195973)
                ·
                  refine ⟨346208283633132233099245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1846444179376705243195973 346208283633132233099245)
                  ·
                    refine ⟨129828106362424587412217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346208283633132233099245 129828106362424587412217)
                    ·
                      rfl

theorem cell22_379259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3].length) (baseStart_379259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379259 prefixEnd_379259 := by exact prefixLift 379259
  have htrace : WordTrace (prefixWord ++ tailWord_379259) baseStart_379259 baseEnd_379259 := by
    simpa [prefixWord, tailWord_379259, baseEnd_379259] using wordTrace_append hprefix tailTrace_379259
  have hstable : (prefixWord ++ tailWord_379259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379259).length < 2 ^ (prefixWord ++ tailWord_379259).sum := by decide
  have hdescent : baseEnd_379259 < baseStart_379259 := by decide
  rcases family_descends (prefixWord ++ tailWord_379259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379276 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_379276 : Nat := 118140960795 + 379276 * 2 ^ 59
def prefixEnd_379276 : Nat := 4983230072969 + 3 ^ 40 * 379276 * 2
def baseEnd_379276 : Nat := 129833925809842209737165

theorem tailTrace_379276 : CollatzResearch.WordTrace tailWord_379276 prefixEnd_379276 129833925809842209737165 := by
  unfold tailWord_379276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916666086977651014446841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9222221449303534685929121 6916666086977651014446841)
  ·
    refine ⟨5187499565233238260835131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6916666086977651014446841 5187499565233238260835131)
    ·
      refine ⟨7781249347849857391252697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5187499565233238260835131 7781249347849857391252697)
      ·
        refine ⟨5835937010887393043439523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7781249347849857391252697 5835937010887393043439523)
        ·
          refine ⟨8753905516331089565159285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5835937010887393043439523 8753905516331089565159285)
          ·
            refine ⟨820678642156039646733683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8753905516331089565159285 820678642156039646733683)
            ·
              refine ⟨1231017963234059470100525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820678642156039646733683 1231017963234059470100525)
              ·
                refine ⟨461631736212772301287697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231017963234059470100525 461631736212772301287697)
                ·
                  refine ⟨346223802159579225965773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461631736212772301287697 346223802159579225965773)
                  ·
                    refine ⟨129833925809842209737165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346223802159579225965773 129833925809842209737165)
                    ·
                      rfl

theorem cell22_379276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_379276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379276 prefixEnd_379276 := by exact prefixLift 379276
  have htrace : WordTrace (prefixWord ++ tailWord_379276) baseStart_379276 baseEnd_379276 := by
    simpa [prefixWord, tailWord_379276, baseEnd_379276] using wordTrace_append hprefix tailTrace_379276
  have hstable : (prefixWord ++ tailWord_379276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379276).length < 2 ^ (prefixWord ++ tailWord_379276).sum := by decide
  have hdescent : baseEnd_379276 < baseStart_379276 := by decide
  rcases family_descends (prefixWord ++ tailWord_379276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379287 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_379287 : Nat := 118140960795 + 379287 * 2 ^ 59
def prefixEnd_379287 : Nat := 4983230072969 + 3 ^ 40 * 379287 * 2
def baseEnd_379287 : Nat := 129837691334641847712131

theorem tailTrace_379287 : CollatzResearch.WordTrace tailWord_379287 prefixEnd_379287 129837691334641847712131 := by
  unfold tailWord_379287
  simp only [CollatzResearch.WordTrace]
  refine ⟨13833733376915450907544115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9222488917943633938362743 13833733376915450907544115)
  ·
    refine ⟨20750600065373176361316173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13833733376915450907544115 20750600065373176361316173)
    ·
      refine ⟨7781475024514941135493565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20750600065373176361316173 7781475024514941135493565)
      ·
        refine ⟨2918053134193102925810087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7781475024514941135493565 2918053134193102925810087)
        ·
          refine ⟨4377079701289654388715131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2918053134193102925810087 4377079701289654388715131)
          ·
            refine ⟨6565619551934481583072697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4377079701289654388715131 6565619551934481583072697)
            ·
              refine ⟨4924214663950861187304523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565619551934481583072697 4924214663950861187304523)
              ·
                refine ⟨7386321995926291780956785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4924214663950861187304523 7386321995926291780956785)
                ·
                  refine ⟨5539741496944718835717589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7386321995926291780956785 5539741496944718835717589)
                  ·
                    refine ⟨129837691334641847712131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5539741496944718835717589 129837691334641847712131)
                    ·
                      rfl

theorem cell22_379287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_379287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379287 prefixEnd_379287 := by exact prefixLift 379287
  have htrace : WordTrace (prefixWord ++ tailWord_379287) baseStart_379287 baseEnd_379287 := by
    simpa [prefixWord, tailWord_379287, baseEnd_379287] using wordTrace_append hprefix tailTrace_379287
  have hstable : (prefixWord ++ tailWord_379287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379287).length < 2 ^ (prefixWord ++ tailWord_379287).sum := by decide
  have hdescent : baseEnd_379287 < baseStart_379287 := by decide
  rcases family_descends (prefixWord ++ tailWord_379287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379306 : List Nat := [3, 1, 6, 1, 11]
def baseStart_379306 : Nat := 118140960795 + 379306 * 2 ^ 59
def prefixEnd_379306 : Nat := 4983230072969 + 3 ^ 40 * 379306 * 2
def baseEnd_379306 : Nat := 534338252769268030811

theorem tailTrace_379306 : CollatzResearch.WordTrace tailWord_379306 prefixEnd_379306 534338252769268030811 := by
  unfold tailWord_379306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458606590961654288121443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9222950909231078101657181 3458606590961654288121443)
  ·
    refine ⟨5187909886442481432182165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3458606590961654288121443 5187909886442481432182165)
    ·
      refine ⟨243183275926991317133539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5187909886442481432182165 243183275926991317133539)
      ·
        refine ⟨364774913890486975700309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243183275926991317133539 364774913890486975700309)
        ·
          refine ⟨534338252769268030811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 364774913890486975700309 534338252769268030811)
          ·
            rfl

theorem cell22_379306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 11].length) (baseStart_379306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379306 prefixEnd_379306 := by exact prefixLift 379306
  have htrace : WordTrace (prefixWord ++ tailWord_379306) baseStart_379306 baseEnd_379306 := by
    simpa [prefixWord, tailWord_379306, baseEnd_379306] using wordTrace_append hprefix tailTrace_379306
  have hstable : (prefixWord ++ tailWord_379306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379306).length < 2 ^ (prefixWord ++ tailWord_379306).sum := by decide
  have hdescent : baseEnd_379306 < baseStart_379306 := by decide
  rcases family_descends (prefixWord ++ tailWord_379306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379379 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 6]
def baseStart_379379 : Nat := 118140960795 + 379379 * 2 ^ 59
def prefixEnd_379379 : Nat := 4983230072969 + 3 ^ 40 * 379379 * 2
def baseEnd_379379 : Nat := 43289728271594758137283

theorem tailTrace_379379 : CollatzResearch.WordTrace tailWord_379379 prefixEnd_379379 43289728271594758137283 := by
  unfold tailWord_379379
  simp only [CollatzResearch.WordTrace]
  refine ⟨13837088892582150619893191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9224725928388100413262127 13837088892582150619893191)
  ·
    refine ⟨20755633338873225929839787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13837088892582150619893191 20755633338873225929839787)
    ·
      refine ⟨31133450008309838894759681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20755633338873225929839787 31133450008309838894759681)
      ·
        refine ⟨23350087506232379171069761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31133450008309838894759681 23350087506232379171069761)
        ·
          refine ⟨17512565629674284378302321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23350087506232379171069761 17512565629674284378302321)
          ·
            refine ⟨13134424222255713283726741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17512565629674284378302321 13134424222255713283726741)
            ·
              refine ⟨615676135418236560174691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13134424222255713283726741 615676135418236560174691)
              ·
                refine ⟨923514203127354840262037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615676135418236560174691 923514203127354840262037)
                ·
                  refine ⟨43289728271594758137283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 923514203127354840262037 43289728271594758137283)
                  ·
                    rfl

theorem cell22_379379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 6].length) (baseStart_379379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379379 prefixEnd_379379 := by exact prefixLift 379379
  have htrace : WordTrace (prefixWord ++ tailWord_379379) baseStart_379379 baseEnd_379379 := by
    simpa [prefixWord, tailWord_379379, baseEnd_379379] using wordTrace_append hprefix tailTrace_379379
  have hstable : (prefixWord ++ tailWord_379379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379379).length < 2 ^ (prefixWord ++ tailWord_379379).sum := by decide
  have hdescent : baseEnd_379379 < baseStart_379379 := by decide
  rcases family_descends (prefixWord ++ tailWord_379379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379396 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_379396 : Nat := 118140960795 + 379396 * 2 ^ 59
def prefixEnd_379396 : Nat := 4983230072969 + 3 ^ 40 * 379396 * 2
def baseEnd_379396 : Nat := 43291668087400632245599

theorem tailTrace_379396 : CollatzResearch.WordTrace tailWord_379396 prefixEnd_379396 43291668087400632245599 := by
  unfold tailWord_379396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6918854466760281261631021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9225139289013708348841361 6918854466760281261631021)
  ·
    refine ⟨2594570425035105473111633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6918854466760281261631021 2594570425035105473111633)
    ·
      refine ⟨1945927818776329104833725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2594570425035105473111633 1945927818776329104833725)
      ·
        refine ⟨729722932041123414312647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1945927818776329104833725 729722932041123414312647)
        ·
          refine ⟨1094584398061685121468971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729722932041123414312647 1094584398061685121468971)
          ·
            refine ⟨1641876597092527682203457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094584398061685121468971 1641876597092527682203457)
            ·
              refine ⟨1231407447819395761652593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1641876597092527682203457 1231407447819395761652593)
              ·
                refine ⟨923555585864546821239445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231407447819395761652593 923555585864546821239445)
                ·
                  refine ⟨43291668087400632245599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 923555585864546821239445 43291668087400632245599)
                  ·
                    rfl

theorem cell22_379396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_379396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379396 prefixEnd_379396 := by exact prefixLift 379396
  have htrace : WordTrace (prefixWord ++ tailWord_379396) baseStart_379396 baseEnd_379396 := by
    simpa [prefixWord, tailWord_379396, baseEnd_379396] using wordTrace_append hprefix tailTrace_379396
  have hstable : (prefixWord ++ tailWord_379396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379396).length < 2 ^ (prefixWord ++ tailWord_379396).sum := by decide
  have hdescent : baseEnd_379396 < baseStart_379396 := by decide
  rcases family_descends (prefixWord ++ tailWord_379396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379456 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 3, 3]
def baseStart_379456 : Nat := 118140960795 + 379456 * 2 ^ 59
def prefixEnd_379456 : Nat := 4983230072969 + 3 ^ 40 * 379456 * 2
def baseEnd_379456 : Nat := 129895543488381740236613

theorem tailTrace_379456 : CollatzResearch.WordTrace tailWord_379456 prefixEnd_379456 129895543488381740236613 := by
  unfold tailWord_379456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919948656651596385223111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9226598208868795180297481 6919948656651596385223111)
  ·
    refine ⟨10379922984977394577834667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919948656651596385223111 10379922984977394577834667)
    ·
      refine ⟨15569884477466091866752001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10379922984977394577834667 15569884477466091866752001)
      ·
        refine ⟨11677413358099568900064001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15569884477466091866752001 11677413358099568900064001)
        ·
          refine ⟨8758060018574676675048001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11677413358099568900064001 8758060018574676675048001)
          ·
            refine ⟨6568545013931007506286001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8758060018574676675048001 6568545013931007506286001)
            ·
              refine ⟨4926408760448255629714501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6568545013931007506286001 4926408760448255629714501)
              ·
                refine ⟨923701642584047930571469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4926408760448255629714501 923701642584047930571469)
                ·
                  refine ⟨346388115969017973964301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923701642584047930571469 346388115969017973964301)
                  ·
                    refine ⟨129895543488381740236613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346388115969017973964301 129895543488381740236613)
                    ·
                      rfl

theorem cell22_379456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_379456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379456 prefixEnd_379456 := by exact prefixLift 379456
  have htrace : WordTrace (prefixWord ++ tailWord_379456) baseStart_379456 baseEnd_379456 := by
    simpa [prefixWord, tailWord_379456, baseEnd_379456] using wordTrace_append hprefix tailTrace_379456
  have hstable : (prefixWord ++ tailWord_379456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379456).length < 2 ^ (prefixWord ++ tailWord_379456).sum := by decide
  have hdescent : baseEnd_379456 < baseStart_379456 := by decide
  rcases family_descends (prefixWord ++ tailWord_379456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379501 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_379501 : Nat := 118140960795 + 379501 * 2 ^ 59
def prefixEnd_379501 : Nat := 4983230072969 + 3 ^ 40 * 379501 * 2
def baseEnd_379501 : Nat := 129910947908016622861475

theorem tailTrace_379501 : CollatzResearch.WordTrace tailWord_379501 prefixEnd_379501 129910947908016622861475 := by
  unfold tailWord_379501
  simp only [CollatzResearch.WordTrace]
  refine ⟨13841538598140165455834357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9227692398760110303889571 13841538598140165455834357)
  ·
    refine ⟨1297644243575640511484471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13841538598140165455834357 1297644243575640511484471)
    ·
      refine ⟨1946466365363460767226707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1297644243575640511484471 1946466365363460767226707)
      ·
        refine ⟨2919699548045191150840061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946466365363460767226707 2919699548045191150840061)
        ·
          refine ⟨1094887330516946681565023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2919699548045191150840061 1094887330516946681565023)
          ·
            refine ⟨1642330995775420022347535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094887330516946681565023 1642330995775420022347535)
            ·
              refine ⟨2463496493663130033521303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1642330995775420022347535 2463496493663130033521303)
              ·
                refine ⟨3695244740494695050281955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463496493663130033521303 3695244740494695050281955)
                ·
                  refine ⟨5542867110742042575422933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3695244740494695050281955 5542867110742042575422933)
                  ·
                    refine ⟨129910947908016622861475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5542867110742042575422933 129910947908016622861475)
                    ·
                      rfl

theorem cell22_379501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_379501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379501 prefixEnd_379501 := by exact prefixLift 379501
  have htrace : WordTrace (prefixWord ++ tailWord_379501) baseStart_379501 baseEnd_379501 := by
    simpa [prefixWord, tailWord_379501, baseEnd_379501] using wordTrace_append hprefix tailTrace_379501
  have hstable : (prefixWord ++ tailWord_379501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379501).length < 2 ^ (prefixWord ++ tailWord_379501).sum := by decide
  have hdescent : baseEnd_379501 < baseStart_379501 := by decide
  rcases family_descends (prefixWord ++ tailWord_379501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379516 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_379516 : Nat := 118140960795 + 379516 * 2 ^ 59
def prefixEnd_379516 : Nat := 4983230072969 + 3 ^ 40 * 379516 * 2
def baseEnd_379516 : Nat := 129916082714561583736429

theorem tailTrace_379516 : CollatzResearch.WordTrace tailWord_379516 prefixEnd_379516 129916082714561583736429 := by
  unfold tailWord_379516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921042846542911508815201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9228057128723882011753601 6921042846542911508815201)
  ·
    refine ⟨5190782134907183631611401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6921042846542911508815201 5190782134907183631611401)
    ·
      refine ⟨3893086601180387723708551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5190782134907183631611401 3893086601180387723708551)
      ·
        refine ⟨5839629901770581585562827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893086601180387723708551 5839629901770581585562827)
        ·
          refine ⟨8759444852655872378344241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5839629901770581585562827 8759444852655872378344241)
          ·
            refine ⟨6569583639491904283758181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8759444852655872378344241 6569583639491904283758181)
            ·
              refine ⟨1231796932404732053204659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6569583639491904283758181 1231796932404732053204659)
              ·
                refine ⟨1847695398607098079806989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231796932404732053204659 1847695398607098079806989)
                ·
                  refine ⟨692885774477661779927621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1847695398607098079806989 692885774477661779927621)
                  ·
                    refine ⟨129916082714561583736429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 692885774477661779927621 129916082714561583736429)
                    ·
                      rfl

theorem cell22_379516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_379516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379516 prefixEnd_379516 := by exact prefixLift 379516
  have htrace : WordTrace (prefixWord ++ tailWord_379516) baseStart_379516 baseEnd_379516 := by
    simpa [prefixWord, tailWord_379516, baseEnd_379516] using wordTrace_append hprefix tailTrace_379516
  have hstable : (prefixWord ++ tailWord_379516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379516).length < 2 ^ (prefixWord ++ tailWord_379516).sum := by decide
  have hdescent : baseEnd_379516 < baseStart_379516 := by decide
  rcases family_descends (prefixWord ++ tailWord_379516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379548 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_379548 : Nat := 118140960795 + 379548 * 2 ^ 59
def prefixEnd_379548 : Nat := 4983230072969 + 3 ^ 40 * 379548 * 2
def baseEnd_379548 : Nat := 43309012322841388978777

theorem tailTrace_379548 : CollatzResearch.WordTrace tailWord_379548 prefixEnd_379548 43309012322841388978777 := by
  unfold tailWord_379548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921626414484946241397649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9228835219313261655196865 6921626414484946241397649)
  ·
    refine ⟨5191219810863709681048237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6921626414484946241397649 5191219810863709681048237)
    ·
      refine ⟨1946707429073891130393089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5191219810863709681048237 1946707429073891130393089)
      ·
        refine ⟨1460030571805418347794817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946707429073891130393089 1460030571805418347794817)
        ·
          refine ⟨1095022928854063760846113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1460030571805418347794817 1095022928854063760846113)
          ·
            refine ⟨821267196640547820634585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095022928854063760846113 821267196640547820634585)
            ·
              refine ⟨615950397480410865475939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821267196640547820634585 615950397480410865475939)
              ·
                refine ⟨923925596220616298213909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615950397480410865475939 923925596220616298213909)
                ·
                  refine ⟨43309012322841388978777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 923925596220616298213909 43309012322841388978777)
                  ·
                    rfl

theorem cell22_379548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_379548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379548 prefixEnd_379548 := by exact prefixLift 379548
  have htrace : WordTrace (prefixWord ++ tailWord_379548) baseStart_379548 baseEnd_379548 := by
    simpa [prefixWord, tailWord_379548, baseEnd_379548] using wordTrace_append hprefix tailTrace_379548
  have hstable : (prefixWord ++ tailWord_379548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379548).length < 2 ^ (prefixWord ++ tailWord_379548).sum := by decide
  have hdescent : baseEnd_379548 < baseStart_379548 := by decide
  rcases family_descends (prefixWord ++ tailWord_379548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379655 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 5]
def baseStart_379655 : Nat := 118140960795 + 379655 * 2 ^ 59
def prefixEnd_379655 : Nat := 4983230072969 + 3 ^ 40 * 379655 * 2
def baseEnd_379655 : Nat := 43321221751737184837001

theorem tailTrace_379655 : CollatzResearch.WordTrace tailWord_379655 prefixEnd_379655 43321221751737184837001 := by
  unfold tailWord_379655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13847155439582249756940419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9231436959721499837960279 13847155439582249756940419)
  ·
    refine ⟨20770733159373374635410629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13847155439582249756940419 20770733159373374635410629)
    ·
      refine ⟨3894512467382507744139493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20770733159373374635410629 3894512467382507744139493)
      ·
        refine ⟨730221087634220202026155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3894512467382507744139493 730221087634220202026155)
        ·
          refine ⟨1095331631451330303039233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730221087634220202026155 1095331631451330303039233)
          ·
            refine ⟨821498723588497727279425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095331631451330303039233 821498723588497727279425)
            ·
              refine ⟨616124042691373295459569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821498723588497727279425 616124042691373295459569)
              ·
                refine ⟨462093032018529971594677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616124042691373295459569 462093032018529971594677)
                ·
                  refine ⟨43321221751737184837001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 462093032018529971594677 43321221751737184837001)
                  ·
                    rfl

theorem cell22_379655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 5].length) (baseStart_379655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379655 prefixEnd_379655 := by exact prefixLift 379655
  have htrace : WordTrace (prefixWord ++ tailWord_379655) baseStart_379655 baseEnd_379655 := by
    simpa [prefixWord, tailWord_379655, baseEnd_379655] using wordTrace_append hprefix tailTrace_379655
  have hstable : (prefixWord ++ tailWord_379655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379655).length < 2 ^ (prefixWord ++ tailWord_379655).sum := by decide
  have hdescent : baseEnd_379655 < baseStart_379655 := by decide
  rcases family_descends (prefixWord ++ tailWord_379655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379698 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_379698 : Nat := 118140960795 + 379698 * 2 ^ 59
def prefixEnd_379698 : Nat := 4983230072969 + 3 ^ 40 * 379698 * 2
def baseEnd_379698 : Nat := 129978385033973775685871

theorem tailTrace_379698 : CollatzResearch.WordTrace tailWord_379698 prefixEnd_379698 129978385033973775685871 := by
  unfold tailWord_379698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3462180944606617025188937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9232482518950978733837165 3462180944606617025188937)
  ·
    refine ⟨2596635708454962768891703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3462180944606617025188937 2596635708454962768891703)
    ·
      refine ⟨3894953562682444153337555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2596635708454962768891703 3894953562682444153337555)
      ·
        refine ⟨5842430344023666230006333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3894953562682444153337555 5842430344023666230006333)
        ·
          refine ⟨2190911379008874836252375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5842430344023666230006333 2190911379008874836252375)
          ·
            refine ⟨3286367068513312254378563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190911379008874836252375 3286367068513312254378563)
            ·
              refine ⟨4929550602769968381567845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3286367068513312254378563 4929550602769968381567845)
              ·
                refine ⟨924290738019369071543971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4929550602769968381567845 924290738019369071543971)
                ·
                  refine ⟨1386436107029053607315957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924290738019369071543971 1386436107029053607315957)
                  ·
                    refine ⟨129978385033973775685871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1386436107029053607315957 129978385033973775685871)
                    ·
                      rfl

theorem cell22_379698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_379698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379698 prefixEnd_379698 := by exact prefixLift 379698
  have htrace : WordTrace (prefixWord ++ tailWord_379698) baseStart_379698 baseEnd_379698 := by
    simpa [prefixWord, tailWord_379698, baseEnd_379698] using wordTrace_append hprefix tailTrace_379698
  have hstable : (prefixWord ++ tailWord_379698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379698).length < 2 ^ (prefixWord ++ tailWord_379698).sum := by decide
  have hdescent : baseEnd_379698 < baseStart_379698 := by decide
  rcases family_descends (prefixWord ++ tailWord_379698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379732 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_379732 : Nat := 118140960795 + 379732 * 2 ^ 59
def prefixEnd_379732 : Nat := 4983230072969 + 3 ^ 40 * 379732 * 2
def baseEnd_379732 : Nat := 129990023928809020335767

theorem tailTrace_379732 : CollatzResearch.WordTrace tailWord_379732 prefixEnd_379732 129990023928809020335767 := by
  unfold tailWord_379732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6924981930151645953746725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9233309240202194604995633 6924981930151645953746725)
  ·
    refine ⟨1298434111903433616327511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6924981930151645953746725 1298434111903433616327511)
    ·
      refine ⟨1947651167855150424491267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298434111903433616327511 1947651167855150424491267)
      ·
        refine ⟨2921476751782725636736901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947651167855150424491267 2921476751782725636736901)
        ·
          refine ⟨547776890959261056888169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2921476751782725636736901 547776890959261056888169)
          ·
            refine ⟨410832668219445792666127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547776890959261056888169 410832668219445792666127)
            ·
              refine ⟨616249002329168688999191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410832668219445792666127 616249002329168688999191)
              ·
                refine ⟨924373503493753033498787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616249002329168688999191 924373503493753033498787)
                ·
                  refine ⟨1386560255240629550248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924373503493753033498787 1386560255240629550248181)
                  ·
                    refine ⟨129990023928809020335767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1386560255240629550248181 129990023928809020335767)
                    ·
                      rfl

theorem cell22_379732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_379732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379732 prefixEnd_379732 := by exact prefixLift 379732
  have htrace : WordTrace (prefixWord ++ tailWord_379732) baseStart_379732 baseEnd_379732 := by
    simpa [prefixWord, tailWord_379732, baseEnd_379732] using wordTrace_append hprefix tailTrace_379732
  have hstable : (prefixWord ++ tailWord_379732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379732).length < 2 ^ (prefixWord ++ tailWord_379732).sum := by decide
  have hdescent : baseEnd_379732 < baseStart_379732 := by decide
  rcases family_descends (prefixWord ++ tailWord_379732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379773 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 7]
def baseStart_379773 : Nat := 118140960795 + 379773 * 2 ^ 59
def prefixEnd_379773 : Nat := 4983230072969 + 3 ^ 40 * 379773 * 2
def baseEnd_379773 : Nat := 43334686355566193353547

theorem tailTrace_379773 : CollatzResearch.WordTrace tailWord_379773 prefixEnd_379773 43334686355566193353547 := by
  unfold tailWord_379773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851459253154755909735973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9234306168769837273157315 13851459253154755909735973)
  ·
    refine ⟨2597148609966516733075495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13851459253154755909735973 2597148609966516733075495)
    ·
      refine ⟨3895722914949775099613243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2597148609966516733075495 3895722914949775099613243)
      ·
        refine ⟨5843584372424662649419865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3895722914949775099613243 5843584372424662649419865)
        ·
          refine ⟨4382688279318496987064899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5843584372424662649419865 4382688279318496987064899)
          ·
            refine ⟨6574032418977745480597349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4382688279318496987064899 6574032418977745480597349)
            ·
              refine ⟨1232631078558327277612003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6574032418977745480597349 1232631078558327277612003)
              ·
                refine ⟨1848946617837490916418005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232631078558327277612003 1848946617837490916418005)
                ·
                  refine ⟨43334686355566193353547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1848946617837490916418005 43334686355566193353547)
                  ·
                    rfl

theorem cell22_379773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_379773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379773 prefixEnd_379773 := by exact prefixLift 379773
  have htrace : WordTrace (prefixWord ++ tailWord_379773) baseStart_379773 baseEnd_379773 := by
    simpa [prefixWord, tailWord_379773, baseEnd_379773] using wordTrace_append hprefix tailTrace_379773
  have hstable : (prefixWord ++ tailWord_379773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379773).length < 2 ^ (prefixWord ++ tailWord_379773).sum := by decide
  have hdescent : baseEnd_379773 < baseStart_379773 := by decide
  rcases family_descends (prefixWord ++ tailWord_379773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379788 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_379788 : Nat := 118140960795 + 379788 * 2 ^ 59
def prefixEnd_379788 : Nat := 4983230072969 + 3 ^ 40 * 379788 * 2
def baseEnd_379788 : Nat := 130009193873243540935595

theorem tailTrace_379788 : CollatzResearch.WordTrace tailWord_379788 prefixEnd_379788 130009193873243540935595 := by
  unfold tailWord_379788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926003174050206735766009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9234670898733608981021345 6926003174050206735766009)
  ·
    refine ⟨5194502380537655051824507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6926003174050206735766009 5194502380537655051824507)
    ·
      refine ⟨7791753570806482577736761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5194502380537655051824507 7791753570806482577736761)
      ·
        refine ⟨5843815178104861933302571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7791753570806482577736761 5843815178104861933302571)
        ·
          refine ⟨8765722767157292899953857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5843815178104861933302571 8765722767157292899953857)
          ·
            refine ⟨6574292075367969674965393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8765722767157292899953857 6574292075367969674965393)
            ·
              refine ⟨4930719056525977256224045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6574292075367969674965393 4930719056525977256224045)
              ·
                refine ⟨1849019646197241471084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4930719056525977256224045 1849019646197241471084017)
                ·
                  refine ⟨1386764734647931103313013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1849019646197241471084017 1386764734647931103313013)
                  ·
                    refine ⟨130009193873243540935595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1386764734647931103313013 130009193873243540935595)
                    ·
                      rfl

theorem cell22_379788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_379788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379788 prefixEnd_379788 := by exact prefixLift 379788
  have htrace : WordTrace (prefixWord ++ tailWord_379788) baseStart_379788 baseEnd_379788 := by
    simpa [prefixWord, tailWord_379788, baseEnd_379788] using wordTrace_append hprefix tailTrace_379788
  have hstable : (prefixWord ++ tailWord_379788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379788).length < 2 ^ (prefixWord ++ tailWord_379788).sum := by decide
  have hdescent : baseEnd_379788 < baseStart_379788 := by decide
  rcases family_descends (prefixWord ++ tailWord_379788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379828 : List Nat := [2, 5, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_379828 : Nat := 118140960795 + 379828 * 2 ^ 59
def prefixEnd_379828 : Nat := 4983230072969 + 3 ^ 40 * 379828 * 2
def baseEnd_379828 : Nat := 130022886690696769935473

theorem tailTrace_379828 : CollatzResearch.WordTrace tailWord_379828 prefixEnd_379828 130022886690696769935473 := by
  unfold tailWord_379828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926732633977750151494069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9235643511970333535325425 6926732633977750151494069)
  ·
    refine ⟨649381184435414076702569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6926732633977750151494069 649381184435414076702569)
    ·
      refine ⟨487035888326560557526927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 649381184435414076702569 487035888326560557526927)
      ·
        refine ⟨730553832489840836290391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487035888326560557526927 730553832489840836290391)
        ·
          refine ⟨1095830748734761254435587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730553832489840836290391 1095830748734761254435587)
          ·
            refine ⟨1643746123102141881653381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095830748734761254435587 1643746123102141881653381)
            ·
              refine ⟨308202398081651602810009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1643746123102141881653381 308202398081651602810009)
              ·
                refine ⟨231151798561238702107507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308202398081651602810009 231151798561238702107507)
                ·
                  refine ⟨346727697841858053161261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231151798561238702107507 346727697841858053161261)
                  ·
                    refine ⟨130022886690696769935473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346727697841858053161261 130022886690696769935473)
                    ·
                      rfl

theorem cell22_379828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_379828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379828 prefixEnd_379828 := by exact prefixLift 379828
  have htrace : WordTrace (prefixWord ++ tailWord_379828) baseStart_379828 baseEnd_379828 := by
    simpa [prefixWord, tailWord_379828, baseEnd_379828] using wordTrace_append hprefix tailTrace_379828
  have hstable : (prefixWord ++ tailWord_379828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379828).length < 2 ^ (prefixWord ++ tailWord_379828).sum := by decide
  have hdescent : baseEnd_379828 < baseStart_379828 := by decide
  rcases family_descends (prefixWord ++ tailWord_379828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379850 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_379850 : Nat := 118140960795 + 379850 * 2 ^ 59
def prefixEnd_379850 : Nat := 4983230072969 + 3 ^ 40 * 379850 * 2
def baseEnd_379850 : Nat := 130030417740296045885405

theorem tailTrace_379850 : CollatzResearch.WordTrace tailWord_379850 prefixEnd_379850 130030417740296045885405 := by
  unfold tailWord_379850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463566918468949515072251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9236178449250532040192669 3463566918468949515072251)
  ·
    refine ⟨5195350377703424272608377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3463566918468949515072251 5195350377703424272608377)
    ·
      refine ⟨3896512783277568204456283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5195350377703424272608377 3896512783277568204456283)
      ·
        refine ⟨5844769174916352306684425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896512783277568204456283 5844769174916352306684425)
        ·
          refine ⟨4383576881187264230013319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5844769174916352306684425 4383576881187264230013319)
          ·
            refine ⟨6575365321780896345019979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383576881187264230013319 6575365321780896345019979)
            ·
              refine ⟨9863047982671344517529969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6575365321780896345019979 9863047982671344517529969)
              ·
                refine ⟨7397285987003508388147477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9863047982671344517529969 7397285987003508388147477)
                ·
                  refine ⟨346747780640789455694413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7397285987003508388147477 346747780640789455694413)
                  ·
                    refine ⟨130030417740296045885405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346747780640789455694413 130030417740296045885405)
                    ·
                      rfl

theorem cell22_379850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_379850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379850 prefixEnd_379850 := by exact prefixLift 379850
  have htrace : WordTrace (prefixWord ++ tailWord_379850) baseStart_379850 baseEnd_379850 := by
    simpa [prefixWord, tailWord_379850, baseEnd_379850] using wordTrace_append hprefix tailTrace_379850
  have hstable : (prefixWord ++ tailWord_379850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379850).length < 2 ^ (prefixWord ++ tailWord_379850).sum := by decide
  have hdescent : baseEnd_379850 < baseStart_379850 := by decide
  rcases family_descends (prefixWord ++ tailWord_379850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379865 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_379865 : Nat := 118140960795 + 379865 * 2 ^ 59
def prefixEnd_379865 : Nat := 4983230072969 + 3 ^ 40 * 379865 * 2
def baseEnd_379865 : Nat := 130035552546841006760359

theorem tailTrace_379865 : CollatzResearch.WordTrace tailWord_379865 prefixEnd_379865 130035552546841006760359 := by
  unfold tailWord_379865
  simp only [CollatzResearch.WordTrace]
  refine ⟨13854814768821455622085049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9236543179214303748056699 13854814768821455622085049)
  ·
    refine ⟨10391111076616091716563787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13854814768821455622085049 10391111076616091716563787)
    ·
      refine ⟨15586666614924137574845681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10391111076616091716563787 15586666614924137574845681)
      ·
        refine ⟨11689999961193103181134261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15586666614924137574845681 11689999961193103181134261)
        ·
          refine ⟨1095937496361853423231337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11689999961193103181134261 1095937496361853423231337)
          ·
            refine ⟨821953122271390067423503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095937496361853423231337 821953122271390067423503)
            ·
              refine ⟨1232929683407085101135255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821953122271390067423503 1232929683407085101135255)
              ·
                refine ⟨1849394525110627651702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232929683407085101135255 1849394525110627651702883)
                ·
                  refine ⟨2774091787665941477554325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1849394525110627651702883 2774091787665941477554325)
                  ·
                    refine ⟨130035552546841006760359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2774091787665941477554325 130035552546841006760359)
                    ·
                      rfl

theorem cell22_379865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_379865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379865 prefixEnd_379865 := by exact prefixLift 379865
  have htrace : WordTrace (prefixWord ++ tailWord_379865) baseStart_379865 baseEnd_379865 := by
    simpa [prefixWord, tailWord_379865, baseEnd_379865] using wordTrace_append hprefix tailTrace_379865
  have hstable : (prefixWord ++ tailWord_379865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379865).length < 2 ^ (prefixWord ++ tailWord_379865).sum := by decide
  have hdescent : baseEnd_379865 < baseStart_379865 := by decide
  rcases family_descends (prefixWord ++ tailWord_379865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379869 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 4]
def baseStart_379869 : Nat := 118140960795 + 379869 * 2 ^ 59
def prefixEnd_379869 : Nat := 4983230072969 + 3 ^ 40 * 379869 * 2
def baseEnd_379869 : Nat := 43345640609528776553449

theorem tailTrace_379869 : CollatzResearch.WordTrace tailWord_379869 prefixEnd_379869 43345640609528776553449 := by
  unfold tailWord_379869
  simp only [CollatzResearch.WordTrace]
  refine ⟨13854960660806964305230661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9236640440537976203487107 13854960660806964305230661)
  ·
    refine ⟨2597805123901305807230749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13854960660806964305230661 2597805123901305807230749)
    ·
      refine ⟨974176921462989677711531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2597805123901305807230749 974176921462989677711531)
      ·
        refine ⟨1461265382194484516567297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974176921462989677711531 1461265382194484516567297)
        ·
          refine ⟨1095949036645863387425473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1461265382194484516567297 1095949036645863387425473)
          ·
            refine ⟨821961777484397540569105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1095949036645863387425473 821961777484397540569105)
            ·
              refine ⟨616471333113298155426829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821961777484397540569105 616471333113298155426829)
              ·
                refine ⟨231176749917486808285061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616471333113298155426829 231176749917486808285061)
                ·
                  refine ⟨43345640609528776553449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231176749917486808285061 43345640609528776553449)
                  ·
                    rfl

theorem cell22_379869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_379869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379869 prefixEnd_379869 := by exact prefixLift 379869
  have htrace : WordTrace (prefixWord ++ tailWord_379869) baseStart_379869 baseEnd_379869 := by
    simpa [prefixWord, tailWord_379869, baseEnd_379869] using wordTrace_append hprefix tailTrace_379869
  have hstable : (prefixWord ++ tailWord_379869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379869).length < 2 ^ (prefixWord ++ tailWord_379869).sum := by decide
  have hdescent : baseEnd_379869 < baseStart_379869 := by decide
  rcases family_descends (prefixWord ++ tailWord_379869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379871 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 1, 4]
def baseStart_379871 : Nat := 118140960795 + 379871 * 2 ^ 59
def prefixEnd_379871 : Nat := 4983230072969 + 3 ^ 40 * 379871 * 2
def baseEnd_379871 : Nat := 130037606469458991110341

theorem tailTrace_379871 : CollatzResearch.WordTrace tailWord_379871 prefixEnd_379871 130037606469458991110341 := by
  unfold tailWord_379871
  simp only [CollatzResearch.WordTrace]
  refine ⟨13855033606799718646803467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9236689071199812431202311 13855033606799718646803467)
  ·
    refine ⟨20782550410199577970205201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13855033606799718646803467 20782550410199577970205201)
    ·
      refine ⟨15586912807649683477653901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20782550410199577970205201 15586912807649683477653901)
      ·
        refine ⟨5845092302868631304120213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15586912807649683477653901 5845092302868631304120213)
        ·
          refine ⟨273988701696967092380635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5845092302868631304120213 273988701696967092380635)
          ·
            refine ⟨410983052545450638570953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273988701696967092380635 410983052545450638570953)
            ·
              refine ⟨308237289409087978928215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410983052545450638570953 308237289409087978928215)
              ·
                refine ⟨462355934113631968392323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308237289409087978928215 462355934113631968392323)
                ·
                  refine ⟨693533901170447952588485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462355934113631968392323 693533901170447952588485)
                  ·
                    refine ⟨130037606469458991110341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 693533901170447952588485 130037606469458991110341)
                    ·
                      rfl

theorem cell22_379871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_379871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379871 prefixEnd_379871 := by exact prefixLift 379871
  have htrace : WordTrace (prefixWord ++ tailWord_379871) baseStart_379871 baseEnd_379871 := by
    simpa [prefixWord, tailWord_379871, baseEnd_379871] using wordTrace_append hprefix tailTrace_379871
  have hstable : (prefixWord ++ tailWord_379871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379871).length < 2 ^ (prefixWord ++ tailWord_379871).sum := by decide
  have hdescent : baseEnd_379871 < baseStart_379871 := by decide
  rcases family_descends (prefixWord ++ tailWord_379871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379912 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 3, 3]
def baseStart_379912 : Nat := 118140960795 + 379912 * 2 ^ 59
def prefixEnd_379912 : Nat := 4983230072969 + 3 ^ 40 * 379912 * 2
def baseEnd_379912 : Nat := 130051641607348550835215

theorem tailTrace_379912 : CollatzResearch.WordTrace tailWord_379912 prefixEnd_379912 130051641607348550835215 := by
  unfold tailWord_379912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928264499825591324522995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9237685999767455099363993 6928264499825591324522995)
  ·
    refine ⟨10392396749738386986784493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6928264499825591324522995 10392396749738386986784493)
    ·
      refine ⟨3897148781151895120044185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10392396749738386986784493 3897148781151895120044185)
      ·
        refine ⟨2922861585863921340033139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897148781151895120044185 2922861585863921340033139)
        ·
          refine ⟨4384292378795882010049709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2922861585863921340033139 4384292378795882010049709)
          ·
            refine ⟨1644109642048455753768641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4384292378795882010049709 1644109642048455753768641)
            ·
              refine ⟨1233082231536341815326481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1644109642048455753768641 1233082231536341815326481)
              ·
                refine ⟨924811673652256361494861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233082231536341815326481 924811673652256361494861)
                ·
                  refine ⟨346804377619596135560573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924811673652256361494861 346804377619596135560573)
                  ·
                    refine ⟨130051641607348550835215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346804377619596135560573 130051641607348550835215)
                    ·
                      rfl

theorem cell22_379912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_379912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379912 prefixEnd_379912 := by exact prefixLift 379912
  have htrace : WordTrace (prefixWord ++ tailWord_379912) baseStart_379912 baseEnd_379912 := by
    simpa [prefixWord, tailWord_379912, baseEnd_379912] using wordTrace_append hprefix tailTrace_379912
  have hstable : (prefixWord ++ tailWord_379912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379912).length < 2 ^ (prefixWord ++ tailWord_379912).sum := by decide
  have hdescent : baseEnd_379912 < baseStart_379912 := by decide
  rcases family_descends (prefixWord ++ tailWord_379912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379925 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 7]
def baseStart_379925 : Nat := 118140960795 + 379925 * 2 ^ 59
def prefixEnd_379925 : Nat := 4983230072969 + 3 ^ 40 * 379925 * 2
def baseEnd_379925 : Nat := 43352030591006950086725

theorem tailTrace_379925 : CollatzResearch.WordTrace tailWord_379925 prefixEnd_379925 43352030591006950086725 := by
  unfold tailWord_379925
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857003148604085869269229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238002099069390579512819 13857003148604085869269229)
  ·
    refine ⟨5196376180726532200975961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13857003148604085869269229 5196376180726532200975961)
    ·
      refine ⟨3897282135544899150731971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5196376180726532200975961 3897282135544899150731971)
      ·
        refine ⟨5845923203317348726097957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3897282135544899150731971 5845923203317348726097957)
        ·
          refine ⟨1096110600622002886143367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5845923203317348726097957 1096110600622002886143367)
          ·
            refine ⟨1644165900933004329215051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096110600622002886143367 1644165900933004329215051)
            ·
              refine ⟨2466248851399506493822577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644165900933004329215051 2466248851399506493822577)
              ·
                refine ⟨1849686638549629870366933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2466248851399506493822577 1849686638549629870366933)
                ·
                  refine ⟨43352030591006950086725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1849686638549629870366933 43352030591006950086725)
                  ·
                    rfl

theorem cell22_379925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_379925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379925 prefixEnd_379925 := by exact prefixLift 379925
  have htrace : WordTrace (prefixWord ++ tailWord_379925) baseStart_379925 baseEnd_379925 := by
    simpa [prefixWord, tailWord_379925, baseEnd_379925] using wordTrace_append hprefix tailTrace_379925
  have hstable : (prefixWord ++ tailWord_379925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379925).length < 2 ^ (prefixWord ++ tailWord_379925).sum := by decide
  have hdescent : baseEnd_379925 < baseStart_379925 := by decide
  rcases family_descends (prefixWord ++ tailWord_379925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379929 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 1, 3]
def baseStart_379929 : Nat := 118140960795 + 379929 * 2 ^ 59
def prefixEnd_379929 : Nat := 4983230072969 + 3 ^ 40 * 379929 * 2
def baseEnd_379929 : Nat := 130057461054766173160163

theorem tailTrace_379929 : CollatzResearch.WordTrace tailWord_379929 prefixEnd_379929 130057461054766173160163 := by
  unfold tailWord_379929
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857149040589594552414841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238099360393063034943227 13857149040589594552414841)
  ·
    refine ⟨10392861780442195914311131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13857149040589594552414841 10392861780442195914311131)
    ·
      refine ⟨15589292670663293871466697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10392861780442195914311131 15589292670663293871466697)
      ·
        refine ⟨11691969502997470403600023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15589292670663293871466697 11691969502997470403600023)
        ·
          refine ⟨17537954254496205605400035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11691969502997470403600023 17537954254496205605400035)
          ·
            refine ⟨26306931381744308408100053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17537954254496205605400035 26306931381744308408100053)
            ·
              refine ⟨616568704259632228314845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26306931381744308408100053 616568704259632228314845)
              ·
                refine ⟨231213264097362085618067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616568704259632228314845 231213264097362085618067)
                ·
                  refine ⟨346819896146043128427101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231213264097362085618067 346819896146043128427101)
                  ·
                    refine ⟨130057461054766173160163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346819896146043128427101 130057461054766173160163)
                    ·
                      rfl

theorem cell22_379929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_379929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379929 prefixEnd_379929 := by exact prefixLift 379929
  have htrace : WordTrace (prefixWord ++ tailWord_379929) baseStart_379929 baseEnd_379929 := by
    simpa [prefixWord, tailWord_379929, baseEnd_379929] using wordTrace_append hprefix tailTrace_379929
  have hstable : (prefixWord ++ tailWord_379929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379929).length < 2 ^ (prefixWord ++ tailWord_379929).sum := by decide
  have hdescent : baseEnd_379929 < baseStart_379929 := by decide
  rcases family_descends (prefixWord ++ tailWord_379929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379946 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_379946 : Nat := 118140960795 + 379946 * 2 ^ 59
def prefixEnd_379946 : Nat := 4983230072969 + 3 ^ 40 * 379946 * 2
def baseEnd_379946 : Nat := 130063280502183795485111

theorem tailTrace_379946 : CollatzResearch.WordTrace tailWord_379946 prefixEnd_379946 130063280502183795485111 := by
  unfold tailWord_379946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464442270382001613945923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9238512721018670970522461 3464442270382001613945923)
  ·
    refine ⟨5196663405573002420918885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464442270382001613945923 5196663405573002420918885)
    ·
      refine ⟨974374388544937953922291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5196663405573002420918885 974374388544937953922291)
      ·
        refine ⟨1461561582817406930883437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974374388544937953922291 1461561582817406930883437)
        ·
          refine ⟨548085593556527599081289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1461561582817406930883437 548085593556527599081289)
          ·
            refine ⟨411064195167395699310967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548085593556527599081289 411064195167395699310967)
            ·
              refine ⟨616596292751093548966451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411064195167395699310967 616596292751093548966451)
              ·
                refine ⟨924894439126640323449677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616596292751093548966451 924894439126640323449677)
                ·
                  refine ⟨346835414672490121293629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 924894439126640323449677 346835414672490121293629)
                  ·
                    refine ⟨130063280502183795485111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346835414672490121293629 130063280502183795485111)
                    ·
                      rfl

theorem cell22_379946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_379946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379946 prefixEnd_379946 := by exact prefixLift 379946
  have htrace : WordTrace (prefixWord ++ tailWord_379946) baseStart_379946 baseEnd_379946 := by
    simpa [prefixWord, tailWord_379946, baseEnd_379946] using wordTrace_append hprefix tailTrace_379946
  have hstable : (prefixWord ++ tailWord_379946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379946).length < 2 ^ (prefixWord ++ tailWord_379946).sum := by decide
  have hdescent : baseEnd_379946 < baseStart_379946 := by decide
  rcases family_descends (prefixWord ++ tailWord_379946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379955 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_379955 : Nat := 118140960795 + 379955 * 2 ^ 59
def prefixEnd_379955 : Nat := 4983230072969 + 3 ^ 40 * 379955 * 2
def baseEnd_379955 : Nat := 130066361386110772010083

theorem tailTrace_379955 : CollatzResearch.WordTrace tailWord_379955 prefixEnd_379955 130066361386110772010083 := by
  unfold tailWord_379955
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858097338495400992861319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238731558996933995240879 13858097338495400992861319)
  ·
    refine ⟨20787146007743101489291979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13858097338495400992861319 20787146007743101489291979)
    ·
      refine ⟨31180719011614652233937969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20787146007743101489291979 31180719011614652233937969)
      ·
        refine ⟨23385539258710989175453477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31180719011614652233937969 23385539258710989175453477)
        ·
          refine ⟨4384788611008310470397527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23385539258710989175453477 4384788611008310470397527)
          ·
            refine ⟨6577182916512465705596291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4384788611008310470397527 6577182916512465705596291)
            ·
              refine ⟨9865774374768698558394437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6577182916512465705596291 9865774374768698558394437)
              ·
                refine ⟨1849832695269130979698957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9865774374768698558394437 1849832695269130979698957)
                ·
                  refine ⟨693687260725924117387109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1849832695269130979698957 693687260725924117387109)
                  ·
                    refine ⟨130066361386110772010083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 693687260725924117387109 130066361386110772010083)
                    ·
                      rfl

theorem cell22_379955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_379955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379955 prefixEnd_379955 := by exact prefixLift 379955
  have htrace : WordTrace (prefixWord ++ tailWord_379955) baseStart_379955 baseEnd_379955 := by
    simpa [prefixWord, tailWord_379955, baseEnd_379955] using wordTrace_append hprefix tailTrace_379955
  have hstable : (prefixWord ++ tailWord_379955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379955).length < 2 ^ (prefixWord ++ tailWord_379955).sum := by decide
  have hdescent : baseEnd_379955 < baseStart_379955 := by decide
  rcases family_descends (prefixWord ++ tailWord_379955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379985 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_379985 : Nat := 118140960795 + 379985 * 2 ^ 59
def prefixEnd_379985 : Nat := 4983230072969 + 3 ^ 40 * 379985 * 2
def baseEnd_379985 : Nat := 130076630999200693759991

theorem tailTrace_379985 : CollatzResearch.WordTrace tailWord_379985 prefixEnd_379985 130076630999200693759991 := by
  unfold tailWord_379985
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859191528386716116453409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9239461018924477410968939 13859191528386716116453409)
  ·
    refine ⟨10394393646290037087340057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13859191528386716116453409 10394393646290037087340057)
    ·
      refine ⟨7795795234717527815505043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10394393646290037087340057 7795795234717527815505043)
      ·
        refine ⟨11693692852076291723257565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7795795234717527815505043 11693692852076291723257565)
        ·
          refine ⟨4385134819528609396221587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11693692852076291723257565 4385134819528609396221587)
          ·
            refine ⟨6577702229292914094332381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4385134819528609396221587 6577702229292914094332381)
            ·
              refine ⟨2466638335984842785374643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6577702229292914094332381 2466638335984842785374643)
              ·
                refine ⟨3699957503977264178061965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466638335984842785374643 3699957503977264178061965)
                ·
                  refine ⟨1387484063991474066773237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3699957503977264178061965 1387484063991474066773237)
                  ·
                    refine ⟨130076630999200693759991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1387484063991474066773237 130076630999200693759991)
                    ·
                      rfl

theorem cell22_379985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_379985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379985 prefixEnd_379985 := by exact prefixLift 379985
  have htrace : WordTrace (prefixWord ++ tailWord_379985) baseStart_379985 baseEnd_379985 := by
    simpa [prefixWord, tailWord_379985, baseEnd_379985] using wordTrace_append hprefix tailTrace_379985
  have hstable : (prefixWord ++ tailWord_379985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379985).length < 2 ^ (prefixWord ++ tailWord_379985).sum := by decide
  have hdescent : baseEnd_379985 < baseStart_379985 := by decide
  rcases family_descends (prefixWord ++ tailWord_379985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379989 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_379989 : Nat := 118140960795 + 379989 * 2 ^ 59
def prefixEnd_379989 : Nat := 4983230072969 + 3 ^ 40 * 379989 * 2
def baseEnd_379989 : Nat := 130078000280946016659979

theorem tailTrace_379989 : CollatzResearch.WordTrace tailWord_379989 prefixEnd_379989 130078000280946016659979 := by
  unfold tailWord_379989
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859337420372224799599021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9239558280248149866399347 13859337420372224799599021)
  ·
    refine ⟨5197251532639584299849633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13859337420372224799599021 5197251532639584299849633)
    ·
      refine ⟨3897938649479688224887225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5197251532639584299849633 3897938649479688224887225)
      ·
        refine ⟨2923453987109766168665419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3897938649479688224887225 2923453987109766168665419)
        ·
          refine ⟨4385180980664649252998129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923453987109766168665419 4385180980664649252998129)
          ·
            refine ⟨3288885735498486939748597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4385180980664649252998129 3288885735498486939748597)
            ·
              refine ⟨308333037702983150601431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3288885735498486939748597 308333037702983150601431)
              ·
                refine ⟨462499556554474725902147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308333037702983150601431 462499556554474725902147)
                ·
                  refine ⟨693749334831712088853221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462499556554474725902147 693749334831712088853221)
                  ·
                    refine ⟨130078000280946016659979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 693749334831712088853221 130078000280946016659979)
                    ·
                      rfl

theorem cell22_379989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_379989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379989 prefixEnd_379989 := by exact prefixLift 379989
  have htrace : WordTrace (prefixWord ++ tailWord_379989) baseStart_379989 baseEnd_379989 := by
    simpa [prefixWord, tailWord_379989, baseEnd_379989] using wordTrace_append hprefix tailTrace_379989
  have hstable : (prefixWord ++ tailWord_379989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379989).length < 2 ^ (prefixWord ++ tailWord_379989).sum := by decide
  have hdescent : baseEnd_379989 < baseStart_379989 := by decide
  rcases family_descends (prefixWord ++ tailWord_379989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379997 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_379997 : Nat := 118140960795 + 379997 * 2 ^ 59
def prefixEnd_379997 : Nat := 4983230072969 + 3 ^ 40 * 379997 * 2
def baseEnd_379997 : Nat := 130080738844436662459955

theorem tailTrace_379997 : CollatzResearch.WordTrace tailWord_379997 prefixEnd_379997 130080738844436662459955 := by
  unfold tailWord_379997
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859629204343242165890245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9239752802895494777260163 13859629204343242165890245)
  ·
    refine ⟨2598680475814357906104421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13859629204343242165890245 2598680475814357906104421)
    ·
      refine ⟨487252589215192107394579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2598680475814357906104421 487252589215192107394579)
      ·
        refine ⟨730878883822788161091869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487252589215192107394579 730878883822788161091869)
        ·
          refine ⟨274079581433545560409451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730878883822788161091869 274079581433545560409451)
          ·
            refine ⟨411119372150318340614177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274079581433545560409451 411119372150318340614177)
            ·
              refine ⟨308339529112738755460633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411119372150318340614177 308339529112738755460633)
              ·
                refine ⟨231254646834554066595475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308339529112738755460633 231254646834554066595475)
                ·
                  refine ⟨346881970251831099893213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231254646834554066595475 346881970251831099893213)
                  ·
                    refine ⟨130080738844436662459955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346881970251831099893213 130080738844436662459955)
                    ·
                      rfl

theorem cell22_379997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_379997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_379997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_379997 prefixEnd_379997 := by exact prefixLift 379997
  have htrace : WordTrace (prefixWord ++ tailWord_379997) baseStart_379997 baseEnd_379997 := by
    simpa [prefixWord, tailWord_379997, baseEnd_379997] using wordTrace_append hprefix tailTrace_379997
  have hstable : (prefixWord ++ tailWord_379997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379997).length < 2 ^ (prefixWord ++ tailWord_379997).sum := by decide
  have hdescent : baseEnd_379997 < baseStart_379997 := by decide
  rcases family_descends (prefixWord ++ tailWord_379997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380064 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_380064 : Nat := 118140960795 + 380064 * 2 ^ 59
def prefixEnd_380064 : Nat := 4983230072969 + 3 ^ 40 * 380064 * 2
def baseEnd_380064 : Nat := 130103674313670821034749

theorem tailTrace_380064 : CollatzResearch.WordTrace tailWord_380064 prefixEnd_380064 130103674313670821034749 := by
  unfold tailWord_380064
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931036447550256304289623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9241381930067008405719497 6931036447550256304289623)
  ·
    refine ⟨10396554671325384456434435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6931036447550256304289623 10396554671325384456434435)
    ·
      refine ⟨15594832006988076684651653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10396554671325384456434435 15594832006988076684651653)
      ·
        refine ⟨2924031001310264378372185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15594832006988076684651653 2924031001310264378372185)
        ·
          refine ⟨2193023250982698283779139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924031001310264378372185 2193023250982698283779139)
          ·
            refine ⟨3289534876474047425668709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193023250982698283779139 3289534876474047425668709)
            ·
              refine ⟨616787789338883892312883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3289534876474047425668709 616787789338883892312883)
              ·
                refine ⟨925181684008325838469325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616787789338883892312883 925181684008325838469325)
                ·
                  refine ⟨346943131503122189425997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925181684008325838469325 346943131503122189425997)
                  ·
                    refine ⟨130103674313670821034749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346943131503122189425997 130103674313670821034749)
                    ·
                      rfl

theorem cell22_380064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_380064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380064 prefixEnd_380064 := by exact prefixLift 380064
  have htrace : WordTrace (prefixWord ++ tailWord_380064) baseStart_380064 baseEnd_380064 := by
    simpa [prefixWord, tailWord_380064, baseEnd_380064] using wordTrace_append hprefix tailTrace_380064
  have hstable : (prefixWord ++ tailWord_380064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380064).length < 2 ^ (prefixWord ++ tailWord_380064).sum := by decide
  have hdescent : baseEnd_380064 < baseStart_380064 := by decide
  rcases family_descends (prefixWord ++ tailWord_380064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380141 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_380141 : Nat := 118140960795 + 380141 * 2 ^ 59
def prefixEnd_380141 : Nat := 4983230072969 + 3 ^ 40 * 380141 * 2
def baseEnd_380141 : Nat := 130130032987268286859513

theorem tailTrace_380141 : CollatzResearch.WordTrace tailWord_380141 prefixEnd_380141 130130032987268286859513 := by
  unfold tailWord_380141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864881315821554759132277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9243254210547703172754851 13864881315821554759132277)
  ·
    refine ⟨1299832623358270758668651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13864881315821554759132277 1299832623358270758668651)
    ·
      refine ⟨1949748935037406138002977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1299832623358270758668651 1949748935037406138002977)
      ·
        refine ⟨1462311701278054603502233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1949748935037406138002977 1462311701278054603502233)
        ·
          refine ⟨1096733775958540952626675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462311701278054603502233 1096733775958540952626675)
          ·
            refine ⟨1645100663937811428940013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096733775958540952626675 1645100663937811428940013)
            ·
              refine ⟨616912748976679285852505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645100663937811428940013 616912748976679285852505)
              ·
                refine ⟨462684561732509464389379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616912748976679285852505 462684561732509464389379)
                ·
                  refine ⟨694026842598764196584069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462684561732509464389379 694026842598764196584069)
                  ·
                    refine ⟨130130032987268286859513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694026842598764196584069 130130032987268286859513)
                    ·
                      rfl

theorem cell22_380141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_380141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380141 prefixEnd_380141 := by exact prefixLift 380141
  have htrace : WordTrace (prefixWord ++ tailWord_380141) baseStart_380141 baseEnd_380141 := by
    simpa [prefixWord, tailWord_380141, baseEnd_380141] using wordTrace_append hprefix tailTrace_380141
  have hstable : (prefixWord ++ tailWord_380141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380141).length < 2 ^ (prefixWord ++ tailWord_380141).sum := by decide
  have hdescent : baseEnd_380141 < baseStart_380141 := by decide
  rcases family_descends (prefixWord ++ tailWord_380141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380158 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 1, 4]
def baseStart_380158 : Nat := 118140960795 + 380158 * 2 ^ 59
def prefixEnd_380158 : Nat := 4983230072969 + 3 ^ 40 * 380158 * 2
def baseEnd_380158 : Nat := 130135852434685909184461

theorem tailTrace_380158 : CollatzResearch.WordTrace tailWord_380158 prefixEnd_380158 130135852434685909184461 := by
  unfold tailWord_380158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733187669594995832812641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9243667571173311108334085 1733187669594995832812641)
  ·
    refine ⟨1299890752196246874609481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1733187669594995832812641 1299890752196246874609481)
    ·
      refine ⟨974918064147185155957111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1299890752196246874609481 974918064147185155957111)
      ·
        refine ⟨1462377096220777733935667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974918064147185155957111 1462377096220777733935667)
        ·
          refine ⟨2193565644331166600903501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462377096220777733935667 2193565644331166600903501)
          ·
            refine ⟨822587116624187475338813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2193565644331166600903501 822587116624187475338813)
            ·
              refine ⟨308470168734070303252055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822587116624187475338813 308470168734070303252055)
              ·
                refine ⟨462705253101105454878083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308470168734070303252055 462705253101105454878083)
                ·
                  refine ⟨694057879651658182317125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462705253101105454878083 694057879651658182317125)
                  ·
                    refine ⟨130135852434685909184461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694057879651658182317125 130135852434685909184461)
                    ·
                      rfl

theorem cell22_380158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_380158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380158 prefixEnd_380158 := by exact prefixLift 380158
  have htrace : WordTrace (prefixWord ++ tailWord_380158) baseStart_380158 baseEnd_380158 := by
    simpa [prefixWord, tailWord_380158, baseEnd_380158] using wordTrace_append hprefix tailTrace_380158
  have hstable : (prefixWord ++ tailWord_380158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380158).length < 2 ^ (prefixWord ++ tailWord_380158).sum := by decide
  have hdescent : baseEnd_380158 < baseStart_380158 := by decide
  rcases family_descends (prefixWord ++ tailWord_380158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380171 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 2, 3]
def baseStart_380171 : Nat := 118140960795 + 380171 * 2 ^ 59
def prefixEnd_380171 : Nat := 4983230072969 + 3 ^ 40 * 380171 * 2
def baseEnd_380171 : Nat := 130140302600358208609421

theorem tailTrace_380171 : CollatzResearch.WordTrace tailWord_380171 prefixEnd_380171 130140302600358208609421 := by
  unfold tailWord_380171
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865975505712869882724367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9243983670475246588482911 13865975505712869882724367)
  ·
    refine ⟨20798963258569304824086551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13865975505712869882724367 20798963258569304824086551)
    ·
      refine ⟨31198444887853957236129827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20798963258569304824086551 31198444887853957236129827)
      ·
        refine ⟨46797667331780935854194741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31198444887853957236129827 46797667331780935854194741)
        ·
          refine ⟨4387281312354462736330757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46797667331780935854194741 4387281312354462736330757)
          ·
            refine ⟨822615246066461763062017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4387281312354462736330757 822615246066461763062017)
            ·
              refine ⟨616961434549846322296513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822615246066461763062017 616961434549846322296513)
              ·
                refine ⟨462721075912384741722385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616961434549846322296513 462721075912384741722385)
                ·
                  refine ⟨347040806934288556291789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462721075912384741722385 347040806934288556291789)
                  ·
                    refine ⟨130140302600358208609421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347040806934288556291789 130140302600358208609421)
                    ·
                      rfl

theorem cell22_380171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3].length) (baseStart_380171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380171 prefixEnd_380171 := by exact prefixLift 380171
  have htrace : WordTrace (prefixWord ++ tailWord_380171) baseStart_380171 baseEnd_380171 := by
    simpa [prefixWord, tailWord_380171, baseEnd_380171] using wordTrace_append hprefix tailTrace_380171
  have hstable : (prefixWord ++ tailWord_380171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380171).length < 2 ^ (prefixWord ++ tailWord_380171).sum := by decide
  have hdescent : baseEnd_380171 < baseStart_380171 := by decide
  rcases family_descends (prefixWord ++ tailWord_380171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380184 : List Nat := [2, 1, 2, 3, 1, 5, 1, 7]
def baseStart_380184 : Nat := 118140960795 + 380184 * 2 ^ 59
def prefixEnd_380184 : Nat := 4983230072969 + 3 ^ 40 * 380184 * 2
def baseEnd_380184 : Nat := 14460528085114500892709

theorem tailTrace_380184 : CollatzResearch.WordTrace tailWord_380184 prefixEnd_380184 14460528085114500892709 := by
  unfold tailWord_380184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933224827332886551473803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9244299769777182068631737 6933224827332886551473803)
  ·
    refine ⟨10399837240999329827210705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6933224827332886551473803 10399837240999329827210705)
    ·
      refine ⟨7799877930749497370408029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10399837240999329827210705 7799877930749497370408029)
      ·
        refine ⟨2924954224031061513903011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7799877930749497370408029 2924954224031061513903011)
        ·
          refine ⟨4387431336046592270854517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924954224031061513903011 4387431336046592270854517)
          ·
            refine ⟨411321687754368025392611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4387431336046592270854517 411321687754368025392611)
            ·
              refine ⟨616982531631552038088917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411321687754368025392611 616982531631552038088917)
              ·
                refine ⟨14460528085114500892709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 616982531631552038088917 14460528085114500892709)
                ·
                  rfl

theorem cell22_380184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_380184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380184 prefixEnd_380184 := by exact prefixLift 380184
  have htrace : WordTrace (prefixWord ++ tailWord_380184) baseStart_380184 baseEnd_380184 := by
    simpa [prefixWord, tailWord_380184, baseEnd_380184] using wordTrace_append hprefix tailTrace_380184
  have hstable : (prefixWord ++ tailWord_380184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380184).length < 2 ^ (prefixWord ++ tailWord_380184).sum := by decide
  have hdescent : baseEnd_380184 < baseStart_380184 := by decide
  rcases family_descends (prefixWord ++ tailWord_380184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380244 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_380244 : Nat := 118140960795 + 380244 * 2 ^ 59
def prefixEnd_380244 : Nat := 4983230072969 + 3 ^ 40 * 380244 * 2
def baseEnd_380244 : Nat := 130165291992210351534197

theorem tailTrace_380244 : CollatzResearch.WordTrace tailWord_380244 prefixEnd_380244 130165291992210351534197 := by
  unfold tailWord_380244
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934319017224201675065893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9245758689632268900087857 6934319017224201675065893)
  ·
    refine ⟨1300184815729537814074855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6934319017224201675065893 1300184815729537814074855)
    ·
      refine ⟨1950277223594306721112283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300184815729537814074855 1950277223594306721112283)
      ·
        refine ⟨2925415835391460081668425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950277223594306721112283 2925415835391460081668425)
        ·
          refine ⟨2194061876543595061251319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925415835391460081668425 2194061876543595061251319)
          ·
            refine ⟨3291092814815392591876979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194061876543595061251319 3291092814815392591876979)
            ·
              refine ⟨4936639222223088887815469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3291092814815392591876979 4936639222223088887815469)
              ·
                refine ⟨1851239708333658332930801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4936639222223088887815469 1851239708333658332930801)
                ·
                  refine ⟨1388429781250243749698101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1851239708333658332930801 1388429781250243749698101)
                  ·
                    refine ⟨130165291992210351534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1388429781250243749698101 130165291992210351534197)
                    ·
                      rfl

theorem cell22_380244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_380244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380244 prefixEnd_380244 := by exact prefixLift 380244
  have htrace : WordTrace (prefixWord ++ tailWord_380244) baseStart_380244 baseEnd_380244 := by
    simpa [prefixWord, tailWord_380244, baseEnd_380244] using wordTrace_append hprefix tailTrace_380244
  have hstable : (prefixWord ++ tailWord_380244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380244).length < 2 ^ (prefixWord ++ tailWord_380244).sum := by decide
  have hdescent : baseEnd_380244 < baseStart_380244 := by decide
  rcases family_descends (prefixWord ++ tailWord_380244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380291 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 6]
def baseStart_380291 : Nat := 118140960795 + 380291 * 2 ^ 59
def prefixEnd_380291 : Nat := 4983230072969 + 3 ^ 40 * 380291 * 2
def baseEnd_380291 : Nat := 43393793684239298536351

theorem tailTrace_380291 : CollatzResearch.WordTrace tailWord_380291 prefixEnd_380291 43393793684239298536351 := by
  unfold tailWord_380291
  simp only [CollatzResearch.WordTrace]
  refine ⟨13870352265278130377092727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9246901510185420251395151 13870352265278130377092727)
  ·
    refine ⟨20805528397917195565639091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13870352265278130377092727 20805528397917195565639091)
    ·
      refine ⟨31208292596875793348458637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20805528397917195565639091 31208292596875793348458637)
      ·
        refine ⟨11703109723828422505671989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31208292596875793348458637 11703109723828422505671989)
        ·
          refine ⟨1097166536608914609906749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11703109723828422505671989 1097166536608914609906749)
          ·
            refine ⟨411437451228342978715031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1097166536608914609906749 411437451228342978715031)
            ·
              refine ⟨617156176842514468072547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411437451228342978715031 617156176842514468072547)
              ·
                refine ⟨925734265263771702108821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617156176842514468072547 925734265263771702108821)
                ·
                  refine ⟨43393793684239298536351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 925734265263771702108821 43393793684239298536351)
                  ·
                    rfl

theorem cell22_380291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 6].length) (baseStart_380291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380291 prefixEnd_380291 := by exact prefixLift 380291
  have htrace : WordTrace (prefixWord ++ tailWord_380291) baseStart_380291 baseEnd_380291 := by
    simpa [prefixWord, tailWord_380291, baseEnd_380291] using wordTrace_append hprefix tailTrace_380291
  have hstable : (prefixWord ++ tailWord_380291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380291).length < 2 ^ (prefixWord ++ tailWord_380291).sum := by decide
  have hdescent : baseEnd_380291 < baseStart_380291 := by decide
  rcases family_descends (prefixWord ++ tailWord_380291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380319 : List Nat := [1, 1, 2, 5, 1, 2, 2, 8]
def baseStart_380319 : Nat := 118140960795 + 380319 * 2 ^ 59
def prefixEnd_380319 : Nat := 4983230072969 + 3 ^ 40 * 380319 * 2
def baseEnd_380319 : Nat := 14465662891659461767663

theorem tailTrace_380319 : CollatzResearch.WordTrace tailWord_380319 prefixEnd_380319 14465662891659461767663 := by
  unfold tailWord_380319
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871373509176691159112011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9247582339451127439408007 13871373509176691159112011)
  ·
    refine ⟨20807060263765036738668017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13871373509176691159112011 20807060263765036738668017)
    ·
      refine ⟨15605295197823777554001013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20807060263765036738668017 15605295197823777554001013)
      ·
        refine ⟨1462996424795979145687595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15605295197823777554001013 1462996424795979145687595)
        ·
          refine ⟨2194494637193968718531393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462996424795979145687595 2194494637193968718531393)
          ·
            refine ⟨1645870977895476538898545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194494637193968718531393 1645870977895476538898545)
            ·
              refine ⟨1234403233421607404173909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1645870977895476538898545 1234403233421607404173909)
              ·
                refine ⟨14465662891659461767663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1234403233421607404173909 14465662891659461767663)
                ·
                  rfl

theorem cell22_380319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 8].length) (baseStart_380319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380319 prefixEnd_380319 := by exact prefixLift 380319
  have htrace : WordTrace (prefixWord ++ tailWord_380319) baseStart_380319 baseEnd_380319 := by
    simpa [prefixWord, tailWord_380319, baseEnd_380319] using wordTrace_append hprefix tailTrace_380319
  have hstable : (prefixWord ++ tailWord_380319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380319).length < 2 ^ (prefixWord ++ tailWord_380319).sum := by decide
  have hdescent : baseEnd_380319 < baseStart_380319 := by decide
  rcases family_descends (prefixWord ++ tailWord_380319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380349 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_380349 : Nat := 118140960795 + 380349 * 2 ^ 59
def prefixEnd_380349 : Nat := 4983230072969 + 3 ^ 40 * 380349 * 2
def baseEnd_380349 : Nat := 130201235638025077658875

theorem tailTrace_380349 : CollatzResearch.WordTrace tailWord_380349 prefixEnd_380349 130201235638025077658875 := by
  unfold tailWord_380349
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872467699068006282704101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9248311799378670855136067 13872467699068006282704101)
  ·
    refine ⟨2601087693575251178007019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13872467699068006282704101 2601087693575251178007019)
    ·
      refine ⟨3901631540362876767010529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601087693575251178007019 3901631540362876767010529)
      ·
        refine ⟨2926223655272157575257897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3901631540362876767010529 2926223655272157575257897)
        ·
          refine ⟨2194667741454118181443423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926223655272157575257897 2194667741454118181443423)
          ·
            refine ⟨3292001612181177272165135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2194667741454118181443423 3292001612181177272165135)
            ·
              refine ⟨4938002418271765908247703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292001612181177272165135 4938002418271765908247703)
              ·
                refine ⟨7407003627407648862371555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938002418271765908247703 7407003627407648862371555)
                ·
                  refine ⟨11110505441111473293557333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407003627407648862371555 11110505441111473293557333)
                  ·
                    refine ⟨130201235638025077658875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11110505441111473293557333 130201235638025077658875)
                    ·
                      rfl

theorem cell22_380349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_380349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380349 prefixEnd_380349 := by exact prefixLift 380349
  have htrace : WordTrace (prefixWord ++ tailWord_380349) baseStart_380349 baseEnd_380349 := by
    simpa [prefixWord, tailWord_380349, baseEnd_380349] using wordTrace_append hprefix tailTrace_380349
  have hstable : (prefixWord ++ tailWord_380349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380349).length < 2 ^ (prefixWord ++ tailWord_380349).sum := by decide
  have hdescent : baseEnd_380349 < baseStart_380349 := by decide
  rcases family_descends (prefixWord ++ tailWord_380349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380385 : List Nat := [1, 2, 3, 1, 2, 4, 2, 3, 1, 3]
def baseStart_380385 : Nat := 118140960795 + 380385 * 2 ^ 59
def prefixEnd_380385 : Nat := 4983230072969 + 3 ^ 40 * 380385 * 2
def baseEnd_380385 : Nat := 130213559173732983758765

theorem tailTrace_380385 : CollatzResearch.WordTrace tailWord_380385 prefixEnd_380385 130213559173732983758765 := by
  unfold tailWord_380385
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873780726937584431014609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9249187151291722954009739 13873780726937584431014609)
  ·
    refine ⟨10405335545203188323260957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13873780726937584431014609 10405335545203188323260957)
    ·
      refine ⟨3902000829451195621222859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10405335545203188323260957 3902000829451195621222859)
      ·
        refine ⟨5853001244176793431834289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902000829451195621222859 5853001244176793431834289)
        ·
          refine ⟨4389750933132595073875717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5853001244176793431834289 4389750933132595073875717)
          ·
            refine ⟨823078299962361576351697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4389750933132595073875717 823078299962361576351697)
            ·
              refine ⟨617308724971771182263773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823078299962361576351697 617308724971771182263773)
              ·
                refine ⟨231490771864414193348915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617308724971771182263773 231490771864414193348915)
                ·
                  refine ⟨347236157796621290023373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231490771864414193348915 347236157796621290023373)
                  ·
                    refine ⟨130213559173732983758765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347236157796621290023373 130213559173732983758765)
                    ·
                      rfl

theorem cell22_380385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_380385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380385 prefixEnd_380385 := by exact prefixLift 380385
  have htrace : WordTrace (prefixWord ++ tailWord_380385) baseStart_380385 baseEnd_380385 := by
    simpa [prefixWord, tailWord_380385, baseEnd_380385] using wordTrace_append hprefix tailTrace_380385
  have hstable : (prefixWord ++ tailWord_380385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380385).length < 2 ^ (prefixWord ++ tailWord_380385).sum := by decide
  have hdescent : baseEnd_380385 < baseStart_380385 := by decide
  rcases family_descends (prefixWord ++ tailWord_380385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380426 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_380426 : Nat := 118140960795 + 380426 * 2 ^ 59
def prefixEnd_380426 : Nat := 4983230072969 + 3 ^ 40 * 380426 * 2
def baseEnd_380426 : Nat := 43409198103874181161213

theorem tailTrace_380426 : CollatzResearch.WordTrace tailWord_380426 prefixEnd_380426 43409198103874181161213 := by
  unfold tailWord_380426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468819029947262108314283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9250184079859365622171421 3468819029947262108314283)
  ·
    refine ⟨5203228544920893162471425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3468819029947262108314283 5203228544920893162471425)
    ·
      refine ⟨3902421408690669871853569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5203228544920893162471425 3902421408690669871853569)
      ·
        refine ⟨2926816056518002403890177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3902421408690669871853569 2926816056518002403890177)
        ·
          refine ⟨2195112042388501802917633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926816056518002403890177 2195112042388501802917633)
          ·
            refine ⟨1646334031791376352188225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2195112042388501802917633 1646334031791376352188225)
            ·
              refine ⟨1234750523843532264141169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1646334031791376352188225 1234750523843532264141169)
              ·
                refine ⟨926062892882649198105877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1234750523843532264141169 926062892882649198105877)
                ·
                  refine ⟨43409198103874181161213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 926062892882649198105877 43409198103874181161213)
                  ·
                    rfl

theorem cell22_380426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_380426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380426 prefixEnd_380426 := by exact prefixLift 380426
  have htrace : WordTrace (prefixWord ++ tailWord_380426) baseStart_380426 baseEnd_380426 := by
    simpa [prefixWord, tailWord_380426, baseEnd_380426] using wordTrace_append hprefix tailTrace_380426
  have hstable : (prefixWord ++ tailWord_380426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380426).length < 2 ^ (prefixWord ++ tailWord_380426).sum := by decide
  have hdescent : baseEnd_380426 < baseStart_380426 := by decide
  rcases family_descends (prefixWord ++ tailWord_380426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380436 : List Nat := [2, 4, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_380436 : Nat := 118140960795 + 380436 * 2 ^ 59
def prefixEnd_380436 : Nat := 4983230072969 + 3 ^ 40 * 380436 * 2
def baseEnd_380436 : Nat := 130231017515985850733609

theorem tailTrace_380436 : CollatzResearch.WordTrace tailWord_380436 prefixEnd_380436 130231017515985850733609 := by
  unfold tailWord_380436
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937820424876410070560581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9250427233168546760747441 6937820424876410070560581)
  ·
    refine ⟨1300841329664326888230109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6937820424876410070560581 1300841329664326888230109)
    ·
      refine ⟨487815498624122583086291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1300841329664326888230109 487815498624122583086291)
      ·
        refine ⟨731723247936183874629437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487815498624122583086291 731723247936183874629437)
        ·
          refine ⟨274396217976068952986039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731723247936183874629437 274396217976068952986039)
          ·
            refine ⟨411594326964103429479059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274396217976068952986039 411594326964103429479059)
            ·
              refine ⟨617391490446155144218589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411594326964103429479059 617391490446155144218589)
              ·
                refine ⟨231521808917308179081971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617391490446155144218589 231521808917308179081971)
                ·
                  refine ⟨347282713375962268622957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231521808917308179081971 347282713375962268622957)
                  ·
                    refine ⟨130231017515985850733609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347282713375962268622957 130231017515985850733609)
                    ·
                      rfl

theorem cell22_380436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_380436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380436 prefixEnd_380436 := by exact prefixLift 380436
  have htrace : WordTrace (prefixWord ++ tailWord_380436) baseStart_380436 baseEnd_380436 := by
    simpa [prefixWord, tailWord_380436, baseEnd_380436] using wordTrace_append hprefix tailTrace_380436
  have hstable : (prefixWord ++ tailWord_380436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380436).length < 2 ^ (prefixWord ++ tailWord_380436).sum := by decide
  have hdescent : baseEnd_380436 < baseStart_380436 := by decide
  rcases family_descends (prefixWord ++ tailWord_380436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380458 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_380458 : Nat := 118140960795 + 380458 * 2 ^ 59
def prefixEnd_380458 : Nat := 4983230072969 + 3 ^ 40 * 380458 * 2
def baseEnd_380458 : Nat := 130238548565585126683541

theorem tailTrace_380458 : CollatzResearch.WordTrace tailWord_380458 prefixEnd_380458 130238548565585126683541 := by
  unfold tailWord_380458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3469110813918279474605507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9250962170448745265614685 3469110813918279474605507)
  ·
    refine ⟨5203666220877419211908261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3469110813918279474605507 5203666220877419211908261)
    ·
      refine ⟨975687416414516102232799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5203666220877419211908261 975687416414516102232799)
      ·
        refine ⟨1463531124621774153349199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975687416414516102232799 1463531124621774153349199)
        ·
          refine ⟨2195296686932661230023799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463531124621774153349199 2195296686932661230023799)
          ·
            refine ⟨3292945030398991845035699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2195296686932661230023799 3292945030398991845035699)
            ·
              refine ⟨4939417545598487767553549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3292945030398991845035699 4939417545598487767553549)
              ·
                refine ⟨1852281579599432912832581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4939417545598487767553549 1852281579599432912832581)
                ·
                  refine ⟨347302796174893671156109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1852281579599432912832581 347302796174893671156109)
                  ·
                    refine ⟨130238548565585126683541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347302796174893671156109 130238548565585126683541)
                    ·
                      rfl

theorem cell22_380458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_380458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380458 prefixEnd_380458 := by exact prefixLift 380458
  have htrace : WordTrace (prefixWord ++ tailWord_380458) baseStart_380458 baseEnd_380458 := by
    simpa [prefixWord, tailWord_380458, baseEnd_380458] using wordTrace_append hprefix tailTrace_380458
  have hstable : (prefixWord ++ tailWord_380458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380458).length < 2 ^ (prefixWord ++ tailWord_380458).sum := by decide
  have hdescent : baseEnd_380458 < baseStart_380458 := by decide
  rcases family_descends (prefixWord ++ tailWord_380458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380471 : List Nat := [1, 1, 3, 1, 2, 5, 2, 7]
def baseStart_380471 : Nat := 118140960795 + 380471 * 2 ^ 59
def prefixEnd_380471 : Nat := 4983230072969 + 3 ^ 40 * 380471 * 2
def baseEnd_380471 : Nat := 14471444303473047345389

theorem tailTrace_380471 : CollatzResearch.WordTrace tailWord_380471 prefixEnd_380471 14471444303473047345389 := by
  unfold tailWord_380471
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876917404626021118645267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9251278269750680745763511 13876917404626021118645267)
  ·
    refine ⟨20815376106939031677967901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13876917404626021118645267 20815376106939031677967901)
    ·
      refine ⟨7805766040102136879237963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20815376106939031677967901 7805766040102136879237963)
      ·
        refine ⟨11708649060153205318856945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805766040102136879237963 11708649060153205318856945)
        ·
          refine ⟨8781486795114903989142709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11708649060153205318856945 8781486795114903989142709)
          ·
            refine ⟨823264387042022248982129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8781486795114903989142709 823264387042022248982129)
            ·
              refine ⟨617448290281516686736597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823264387042022248982129 617448290281516686736597)
              ·
                refine ⟨14471444303473047345389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 617448290281516686736597 14471444303473047345389)
                ·
                  rfl

theorem cell22_380471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 7].length) (baseStart_380471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380471 prefixEnd_380471 := by exact prefixLift 380471
  have htrace : WordTrace (prefixWord ++ tailWord_380471) baseStart_380471 baseEnd_380471 := by
    simpa [prefixWord, tailWord_380471, baseEnd_380471] using wordTrace_append hprefix tailTrace_380471
  have hstable : (prefixWord ++ tailWord_380471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380471).length < 2 ^ (prefixWord ++ tailWord_380471).sum := by decide
  have hdescent : baseEnd_380471 < baseStart_380471 := by decide
  rcases family_descends (prefixWord ++ tailWord_380471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380509 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_380509 : Nat := 118140960795 + 380509 * 2 ^ 59
def prefixEnd_380509 : Nat := 4983230072969 + 3 ^ 40 * 380509 * 2
def baseEnd_380509 : Nat := 130256006907837993658385

theorem tailTrace_380509 : CollatzResearch.WordTrace tailWord_380509 prefixEnd_380509 130256006907837993658385 := by
  unfold tailWord_380509
  simp only [CollatzResearch.WordTrace]
  refine ⟨13878303378488353608528581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9252202252325569072352387 13878303378488353608528581)
  ·
    refine ⟨2602181883466566301599109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13878303378488353608528581 2602181883466566301599109)
    ·
      refine ⟨487909103149981181549833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2602181883466566301599109 487909103149981181549833)
      ·
        refine ⟨365931827362485886162375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 487909103149981181549833 365931827362485886162375)
        ·
          refine ⟨548897741043728829243563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365931827362485886162375 548897741043728829243563)
          ·
            refine ⟨823346611565593243865345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548897741043728829243563 823346611565593243865345)
            ·
              refine ⟨617509958674194932899009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823346611565593243865345 617509958674194932899009)
              ·
                refine ⟨463132469005646199674257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617509958674194932899009 463132469005646199674257)
                ·
                  refine ⟨347349351754234649755693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463132469005646199674257 347349351754234649755693)
                  ·
                    refine ⟨130256006907837993658385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347349351754234649755693 130256006907837993658385)
                    ·
                      rfl

theorem cell22_380509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_380509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380509 prefixEnd_380509 := by exact prefixLift 380509
  have htrace : WordTrace (prefixWord ++ tailWord_380509) baseStart_380509 baseEnd_380509 := by
    simpa [prefixWord, tailWord_380509, baseEnd_380509] using wordTrace_append hprefix tailTrace_380509
  have hstable : (prefixWord ++ tailWord_380509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380509).length < 2 ^ (prefixWord ++ tailWord_380509).sum := by decide
  have hdescent : baseEnd_380509 < baseStart_380509 := by decide
  rcases family_descends (prefixWord ++ tailWord_380509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380591 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_380591 : Nat := 118140960795 + 380591 * 2 ^ 59
def prefixEnd_380591 : Nat := 4983230072969 + 3 ^ 40 * 380591 * 2
def baseEnd_380591 : Nat := 130284077183617113108133

theorem tailTrace_380591 : CollatzResearch.WordTrace tailWord_380591 prefixEnd_380591 130284077183617113108133 := by
  unfold tailWord_380591
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881294164191281613013627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9254196109460854408675751 13881294164191281613013627)
  ·
    refine ⟨20821941246286922419520441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13881294164191281613013627 20821941246286922419520441)
    ·
      refine ⟨15616455934715191814640331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20821941246286922419520441 15616455934715191814640331)
      ·
        refine ⟨23424683902072787721960497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15616455934715191814640331 23424683902072787721960497)
        ·
          refine ⟨17568512926554590791470373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23424683902072787721960497 17568512926554590791470373)
          ·
            refine ⟨3294096173728985773400695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17568512926554590791470373 3294096173728985773400695)
            ·
              refine ⟨4941144260593478660101043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294096173728985773400695 4941144260593478660101043)
              ·
                refine ⟨7411716390890217990151565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941144260593478660101043 7411716390890217990151565)
                ·
                  refine ⟨2779393646583831746306837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7411716390890217990151565 2779393646583831746306837)
                  ·
                    refine ⟨130284077183617113108133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2779393646583831746306837 130284077183617113108133)
                    ·
                      rfl

theorem cell22_380591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_380591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380591 prefixEnd_380591 := by exact prefixLift 380591
  have htrace : WordTrace (prefixWord ++ tailWord_380591) baseStart_380591 baseEnd_380591 := by
    simpa [prefixWord, tailWord_380591, baseEnd_380591] using wordTrace_append hprefix tailTrace_380591
  have hstable : (prefixWord ++ tailWord_380591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380591).length < 2 ^ (prefixWord ++ tailWord_380591).sum := by decide
  have hdescent : baseEnd_380591 < baseStart_380591 := by decide
  rcases family_descends (prefixWord ++ tailWord_380591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380597 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_380597 : Nat := 118140960795 + 380597 * 2 ^ 59
def prefixEnd_380597 : Nat := 4983230072969 + 3 ^ 40 * 380597 * 2
def baseEnd_380597 : Nat := 130286131106235097458115

theorem tailTrace_380597 : CollatzResearch.WordTrace tailWord_380597 prefixEnd_380597 130286131106235097458115 := by
  unfold tailWord_380597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881513002169544637732045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9254342001446363091821363 13881513002169544637732045)
  ·
    refine ⟨5205567375813579239149517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13881513002169544637732045 5205567375813579239149517)
    ·
      refine ⟨1952087765930092214681069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5205567375813579239149517 1952087765930092214681069)
      ·
        refine ⟨732032912223784580505401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1952087765930092214681069 732032912223784580505401)
        ·
          refine ⟨549024684167838435379051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732032912223784580505401 549024684167838435379051)
          ·
            refine ⟨823537026251757653068577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549024684167838435379051 823537026251757653068577)
            ·
              refine ⟨617652769688818239801433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 823537026251757653068577 617652769688818239801433)
              ·
                refine ⟨463239577266613679851075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617652769688818239801433 463239577266613679851075)
                ·
                  refine ⟨694859365899920519776613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463239577266613679851075 694859365899920519776613)
                  ·
                    refine ⟨130286131106235097458115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694859365899920519776613 130286131106235097458115)
                    ·
                      rfl

theorem cell22_380597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_380597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380597 prefixEnd_380597 := by exact prefixLift 380597
  have htrace : WordTrace (prefixWord ++ tailWord_380597) baseStart_380597 baseEnd_380597 := by
    simpa [prefixWord, tailWord_380597, baseEnd_380597] using wordTrace_append hprefix tailTrace_380597
  have hstable : (prefixWord ++ tailWord_380597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380597).length < 2 ^ (prefixWord ++ tailWord_380597).sum := by decide
  have hdescent : baseEnd_380597 < baseStart_380597 := by decide
  rcases family_descends (prefixWord ++ tailWord_380597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380608 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_380608 : Nat := 118140960795 + 380608 * 2 ^ 59
def prefixEnd_380608 : Nat := 4983230072969 + 3 ^ 40 * 380608 * 2
def baseEnd_380608 : Nat := 130289896631034735433081

theorem tailTrace_380608 : CollatzResearch.WordTrace tailWord_380608 prefixEnd_380608 130289896631034735433081 := by
  unfold tailWord_380608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940957102564846758191239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9254609470086462344254985 6940957102564846758191239)
  ·
    refine ⟨10411435653847270137286859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6940957102564846758191239 10411435653847270137286859)
    ·
      refine ⟨15617153480770905205930289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411435653847270137286859 15617153480770905205930289)
      ·
        refine ⟨11712865110578178904447717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15617153480770905205930289 11712865110578178904447717)
        ·
          refine ⟨2196162208233408544583947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11712865110578178904447717 2196162208233408544583947)
          ·
            refine ⟨3294243312350112816875921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196162208233408544583947 3294243312350112816875921)
            ·
              refine ⟨2470682484262584612656941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3294243312350112816875921 2470682484262584612656941)
              ·
                refine ⟨926505931598469229746353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2470682484262584612656941 926505931598469229746353)
                ·
                  refine ⟨694879448698851922309765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 926505931598469229746353 694879448698851922309765)
                  ·
                    refine ⟨130289896631034735433081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694879448698851922309765 130289896631034735433081)
                    ·
                      rfl

theorem cell22_380608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_380608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380608 prefixEnd_380608 := by exact prefixLift 380608
  have htrace : WordTrace (prefixWord ++ tailWord_380608) baseStart_380608 baseEnd_380608 := by
    simpa [prefixWord, tailWord_380608, baseEnd_380608] using wordTrace_append hprefix tailTrace_380608
  have hstable : (prefixWord ++ tailWord_380608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380608).length < 2 ^ (prefixWord ++ tailWord_380608).sum := by decide
  have hdescent : baseEnd_380608 < baseStart_380608 := by decide
  rcases family_descends (prefixWord ++ tailWord_380608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380614 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_380614 : Nat := 118140960795 + 380614 * 2 ^ 59
def prefixEnd_380614 : Nat := 4983230072969 + 3 ^ 40 * 380614 * 2
def baseEnd_380614 : Nat := 130291950553652719783063

theorem tailTrace_380614 : CollatzResearch.WordTrace tailWord_380614 prefixEnd_380614 130291950553652719783063 := by
  unfold tailWord_380614
  simp only [CollatzResearch.WordTrace]
  refine ⟨433816657597123641909403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9254755362071971027400597 433816657597123641909403)
  ·
    refine ⟨650724986395685462864105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 433816657597123641909403 650724986395685462864105)
    ·
      refine ⟨488043739796764097148079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 650724986395685462864105 488043739796764097148079)
      ·
        refine ⟨732065609695146145722119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488043739796764097148079 732065609695146145722119)
        ·
          refine ⟨1098098414542719218583179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732065609695146145722119 1098098414542719218583179)
          ·
            refine ⟨1647147621814078827874769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098098414542719218583179 1647147621814078827874769)
            ·
              refine ⟨1235360716360559120906077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1647147621814078827874769 1235360716360559120906077)
              ·
                refine ⟨463260268635209670339779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1235360716360559120906077 463260268635209670339779)
                ·
                  refine ⟨694890402952814505509669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463260268635209670339779 694890402952814505509669)
                  ·
                    refine ⟨130291950553652719783063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 694890402952814505509669 130291950553652719783063)
                    ·
                      rfl

theorem cell22_380614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_380614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380614 prefixEnd_380614 := by exact prefixLift 380614
  have htrace : WordTrace (prefixWord ++ tailWord_380614) baseStart_380614 baseEnd_380614 := by
    simpa [prefixWord, tailWord_380614, baseEnd_380614] using wordTrace_append hprefix tailTrace_380614
  have hstable : (prefixWord ++ tailWord_380614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380614).length < 2 ^ (prefixWord ++ tailWord_380614).sum := by decide
  have hdescent : baseEnd_380614 < baseStart_380614 := by decide
  rcases family_descends (prefixWord ++ tailWord_380614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380732 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_380732 : Nat := 118140960795 + 380732 * 2 ^ 59
def prefixEnd_380732 : Nat := 4983230072969 + 3 ^ 40 * 380732 * 2
def baseEnd_380732 : Nat := 130332344365139745332701

theorem tailTrace_380732 : CollatzResearch.WordTrace tailWord_380732 prefixEnd_380732 130332344365139745332701 := by
  unfold tailWord_380732
  simp only [CollatzResearch.WordTrace]
  refine ⟨6943218428340231346948225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9257624571120308462597633 6943218428340231346948225)
  ·
    refine ⟨5207413821255173510211169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6943218428340231346948225 5207413821255173510211169)
    ·
      refine ⟨3905560365941380132658377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5207413821255173510211169 3905560365941380132658377)
      ·
        refine ⟨2929170274456035099493783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905560365941380132658377 2929170274456035099493783)
        ·
          refine ⟨4393755411684052649240675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929170274456035099493783 4393755411684052649240675)
          ·
            refine ⟨6590633117526078973861013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393755411684052649240675 6590633117526078973861013)
            ·
              refine ⟨308935927384034951899735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6590633117526078973861013 308935927384034951899735)
              ·
                refine ⟨463403891076052427849603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308935927384034951899735 463403891076052427849603)
                ·
                  refine ⟨695105836614078641774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463403891076052427849603 695105836614078641774405)
                  ·
                    refine ⟨130332344365139745332701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695105836614078641774405 130332344365139745332701)
                    ·
                      rfl

theorem cell22_380732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_380732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380732 prefixEnd_380732 := by exact prefixLift 380732
  have htrace : WordTrace (prefixWord ++ tailWord_380732) baseStart_380732 baseEnd_380732 := by
    simpa [prefixWord, tailWord_380732, baseEnd_380732] using wordTrace_append hprefix tailTrace_380732
  have hstable : (prefixWord ++ tailWord_380732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380732).length < 2 ^ (prefixWord ++ tailWord_380732).sum := by decide
  have hdescent : baseEnd_380732 < baseStart_380732 := by decide
  rcases family_descends (prefixWord ++ tailWord_380732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380745 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_380745 : Nat := 118140960795 + 380745 * 2 ^ 59
def prefixEnd_380745 : Nat := 4983230072969 + 3 ^ 40 * 380745 * 2
def baseEnd_380745 : Nat := 130336794530812044757661

theorem tailTrace_380745 : CollatzResearch.WordTrace tailWord_380745 prefixEnd_380745 130336794530812044757661 := by
  unfold tailWord_380745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886911005633365914119689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9257940670422243942746459 13886911005633365914119689)
  ·
    refine ⟨10415183254225024435589767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13886911005633365914119689 10415183254225024435589767)
    ·
      refine ⟨15622774881337536653384651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10415183254225024435589767 15622774881337536653384651)
      ·
        refine ⟨23434162322006304980076977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15622774881337536653384651 23434162322006304980076977)
        ·
          refine ⟨17575621741504728735057733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23434162322006304980076977 17575621741504728735057733)
          ·
            refine ⟨3295429076532136637823325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17575621741504728735057733 3295429076532136637823325)
            ·
              refine ⟨1235785903699551239183747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3295429076532136637823325 1235785903699551239183747)
              ·
                refine ⟨1853678855549326858775621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235785903699551239183747 1853678855549326858775621)
                ·
                  refine ⟨347564785415498786020429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853678855549326858775621 347564785415498786020429)
                  ·
                    refine ⟨130336794530812044757661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347564785415498786020429 130336794530812044757661)
                    ·
                      rfl

theorem cell22_380745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_380745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380745 prefixEnd_380745 := by exact prefixLift 380745
  have htrace : WordTrace (prefixWord ++ tailWord_380745) baseStart_380745 baseEnd_380745 := by
    simpa [prefixWord, tailWord_380745, baseEnd_380745] using wordTrace_append hprefix tailTrace_380745
  have hstable : (prefixWord ++ tailWord_380745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380745).length < 2 ^ (prefixWord ++ tailWord_380745).sum := by decide
  have hdescent : baseEnd_380745 < baseStart_380745 := by decide
  rcases family_descends (prefixWord ++ tailWord_380745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380773 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_380773 : Nat := 118140960795 + 380773 * 2 ^ 59
def prefixEnd_380773 : Nat := 4983230072969 + 3 ^ 40 * 380773 * 2
def baseEnd_380773 : Nat := 130346379503029305057575

theorem tailTrace_380773 : CollatzResearch.WordTrace tailWord_380773 prefixEnd_380773 130346379503029305057575 := by
  unfold tailWord_380773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887932249531926696138973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9258621499687951130759315 13887932249531926696138973)
  ·
    refine ⟨5207974593574472511052115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13887932249531926696138973 5207974593574472511052115)
    ·
      refine ⟨7811961890361708766578173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5207974593574472511052115 7811961890361708766578173)
      ·
        refine ⟨2929485708885640787466815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7811961890361708766578173 2929485708885640787466815)
        ·
          refine ⟨4394228563328461181200223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929485708885640787466815 4394228563328461181200223)
          ·
            refine ⟨6591342844992691771800335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394228563328461181200223 6591342844992691771800335)
            ·
              refine ⟨9887014267489037657700503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6591342844992691771800335 9887014267489037657700503)
              ·
                refine ⟨14830521401233556486550755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9887014267489037657700503 14830521401233556486550755)
                ·
                  refine ⟨22245782101850334729826133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14830521401233556486550755 22245782101850334729826133)
                  ·
                    refine ⟨130346379503029305057575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22245782101850334729826133 130346379503029305057575)
                    ·
                      rfl

theorem cell22_380773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_380773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380773 prefixEnd_380773 := by exact prefixLift 380773
  have htrace : WordTrace (prefixWord ++ tailWord_380773) baseStart_380773 baseEnd_380773 := by
    simpa [prefixWord, tailWord_380773, baseEnd_380773] using wordTrace_append hprefix tailTrace_380773
  have hstable : (prefixWord ++ tailWord_380773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380773).length < 2 ^ (prefixWord ++ tailWord_380773).sum := by decide
  have hdescent : baseEnd_380773 < baseStart_380773 := by decide
  rcases family_descends (prefixWord ++ tailWord_380773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380880 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_380880 : Nat := 118140960795 + 380880 * 2 ^ 59
def prefixEnd_380880 : Nat := 4983230072969 + 3 ^ 40 * 380880 * 2
def baseEnd_380880 : Nat := 130383007789716692632247

theorem tailTrace_380880 : CollatzResearch.WordTrace tailWord_380880 prefixEnd_380880 130383007789716692632247 := by
  unfold tailWord_380880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945917430072141985142047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9261223240096189313522729 6945917430072141985142047)
  ·
    refine ⟨10418876145108212977713071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945917430072141985142047 10418876145108212977713071)
    ·
      refine ⟨15628314217662319466569607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10418876145108212977713071 15628314217662319466569607)
      ·
        refine ⟨23442471326493479199854411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15628314217662319466569607 23442471326493479199854411)
        ·
          refine ⟨35163706989740218799781617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23442471326493479199854411 35163706989740218799781617)
          ·
            refine ⟨26372780242305164099836213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35163706989740218799781617 26372780242305164099836213)
            ·
              refine ⟨2472448147716109134359645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26372780242305164099836213 2472448147716109134359645)
              ·
                refine ⟨927168055393540925384867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472448147716109134359645 927168055393540925384867)
                ·
                  refine ⟨1390752083090311388077301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927168055393540925384867 1390752083090311388077301)
                  ·
                    refine ⟨130383007789716692632247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1390752083090311388077301 130383007789716692632247)
                    ·
                      rfl

theorem cell22_380880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_380880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380880 prefixEnd_380880 := by exact prefixLift 380880
  have htrace : WordTrace (prefixWord ++ tailWord_380880) baseStart_380880 baseEnd_380880 := by
    simpa [prefixWord, tailWord_380880, baseEnd_380880] using wordTrace_append hprefix tailTrace_380880
  have hstable : (prefixWord ++ tailWord_380880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380880).length < 2 ^ (prefixWord ++ tailWord_380880).sum := by decide
  have hdescent : baseEnd_380880 < baseStart_380880 := by decide
  rcases family_descends (prefixWord ++ tailWord_380880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380899 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 4]
def baseStart_380899 : Nat := 118140960795 + 380899 * 2 ^ 59
def prefixEnd_380899 : Nat := 4983230072969 + 3 ^ 40 * 380899 * 2
def baseEnd_380899 : Nat := 43463170626002325469063

theorem tailTrace_380899 : CollatzResearch.WordTrace tailWord_380899 prefixEnd_380899 43463170626002325469063 := by
  unfold tailWord_380899
  simp only [CollatzResearch.WordTrace]
  refine ⟨13892527847075450215225751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9261685231383633476817167 13892527847075450215225751)
  ·
    refine ⟨20838791770613175322838627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13892527847075450215225751 20838791770613175322838627)
    ·
      refine ⟨31258187655919762984257941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20838791770613175322838627 31258187655919762984257941)
      ·
        refine ⟨1465227546371238889887091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31258187655919762984257941 1465227546371238889887091)
        ·
          refine ⟨2197841319556858334830637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1465227546371238889887091 2197841319556858334830637)
          ·
            refine ⟨824190494833821875561489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2197841319556858334830637 824190494833821875561489)
            ·
              refine ⟨618142871125366406671117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824190494833821875561489 618142871125366406671117)
              ·
                refine ⟨231803576672012402501669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618142871125366406671117 231803576672012402501669)
                ·
                  refine ⟨43463170626002325469063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231803576672012402501669 43463170626002325469063)
                  ·
                    rfl

theorem cell22_380899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 4].length) (baseStart_380899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_380899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_380899 prefixEnd_380899 := by exact prefixLift 380899
  have htrace : WordTrace (prefixWord ++ tailWord_380899) baseStart_380899 baseEnd_380899 := by
    simpa [prefixWord, tailWord_380899, baseEnd_380899] using wordTrace_append hprefix tailTrace_380899
  have hstable : (prefixWord ++ tailWord_380899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380899).length < 2 ^ (prefixWord ++ tailWord_380899).sum := by decide
  have hdescent : baseEnd_380899 < baseStart_380899 := by decide
  rcases family_descends (prefixWord ++ tailWord_380899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381049 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_381049 : Nat := 118140960795 + 381049 * 2 ^ 59
def prefixEnd_381049 : Nat := 4983230072969 + 3 ^ 40 * 381049 * 2
def baseEnd_381049 : Nat := 130440859943456585156729

theorem tailTrace_381049 : CollatzResearch.WordTrace tailWord_381049 prefixEnd_381049 130440859943456585156729 := by
  unfold tailWord_381049
  simp only [CollatzResearch.WordTrace]
  refine ⟨13897998796532025833186201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9265332531021350555457467 13897998796532025833186201)
  ·
    refine ⟨10423499097399019374889651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13897998796532025833186201 10423499097399019374889651)
    ·
      refine ⟨15635248646098529062334477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10423499097399019374889651 15635248646098529062334477)
      ·
        refine ⟨5863218242286948398375429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15635248646098529062334477 5863218242286948398375429)
        ·
          refine ⟨1099353420428802824695393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5863218242286948398375429 1099353420428802824695393)
          ·
            refine ⟨824515065321602118521545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099353420428802824695393 824515065321602118521545)
            ·
              refine ⟨618386298991201588891159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 824515065321602118521545 618386298991201588891159)
              ·
                refine ⟨927579448486802383336739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618386298991201588891159 927579448486802383336739)
                ·
                  refine ⟨1391369172730203575005109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927579448486802383336739 1391369172730203575005109)
                  ·
                    refine ⟨130440859943456585156729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1391369172730203575005109 130440859943456585156729)
                    ·
                      rfl

theorem cell22_381049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_381049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381049 prefixEnd_381049 := by exact prefixLift 381049
  have htrace : WordTrace (prefixWord ++ tailWord_381049) baseStart_381049 baseEnd_381049 := by
    simpa [prefixWord, tailWord_381049, baseEnd_381049] using wordTrace_append hprefix tailTrace_381049
  have hstable : (prefixWord ++ tailWord_381049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381049).length < 2 ^ (prefixWord ++ tailWord_381049).sum := by decide
  have hdescent : baseEnd_381049 < baseStart_381049 := by decide
  rcases family_descends (prefixWord ++ tailWord_381049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381064 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 6]
def baseStart_381064 : Nat := 118140960795 + 381064 * 2 ^ 59
def prefixEnd_381064 : Nat := 4983230072969 + 3 ^ 40 * 381064 * 2
def baseEnd_381064 : Nat := 130445994750001546031683

theorem tailTrace_381064 : CollatzResearch.WordTrace tailWord_381064 prefixEnd_381064 130445994750001546031683 := by
  unfold tailWord_381064
  simp only [CollatzResearch.WordTrace]
  refine ⟨6949272945738841697491123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9265697260985122263321497 6949272945738841697491123)
  ·
    refine ⟨10423909418608262546236685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6949272945738841697491123 10423909418608262546236685)
    ·
      refine ⟨3908966031978098454838757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10423909418608262546236685 3908966031978098454838757)
      ·
        refine ⟨732931130995893460282267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3908966031978098454838757 732931130995893460282267)
        ·
          refine ⟨1099396696493840190423401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732931130995893460282267 1099396696493840190423401)
          ·
            refine ⟨824547522370380142817551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1099396696493840190423401 824547522370380142817551)
            ·
              refine ⟨1236821283555570214226327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824547522370380142817551 1236821283555570214226327)
              ·
                refine ⟨1855231925333355321339491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236821283555570214226327 1855231925333355321339491)
                ·
                  refine ⟨2782847888000032982009237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1855231925333355321339491 2782847888000032982009237)
                  ·
                    refine ⟨130445994750001546031683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2782847888000032982009237 130445994750001546031683)
                    ·
                      rfl

theorem cell22_381064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_381064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381064 prefixEnd_381064 := by exact prefixLift 381064
  have htrace : WordTrace (prefixWord ++ tailWord_381064) baseStart_381064 baseEnd_381064 := by
    simpa [prefixWord, tailWord_381064, baseEnd_381064] using wordTrace_append hprefix tailTrace_381064
  have hstable : (prefixWord ++ tailWord_381064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381064).length < 2 ^ (prefixWord ++ tailWord_381064).sum := by decide
  have hdescent : baseEnd_381064 < baseStart_381064 := by decide
  rcases family_descends (prefixWord ++ tailWord_381064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381070 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 1, 4]
def baseStart_381070 : Nat := 118140960795 + 381070 * 2 ^ 59
def prefixEnd_381070 : Nat := 4983230072969 + 3 ^ 40 * 381070 * 2
def baseEnd_381070 : Nat := 130448048672619530381665

theorem tailTrace_381070 : CollatzResearch.WordTrace tailWord_381070 prefixEnd_381070 130448048672619530381665 := by
  unfold tailWord_381070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1737345591181993302462583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9265843152970630946467109 1737345591181993302462583)
  ·
    refine ⟨2606018386772989953693875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1737345591181993302462583 2606018386772989953693875)
    ·
      refine ⟨3909027580159484930540813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2606018386772989953693875 3909027580159484930540813)
      ·
        refine ⟨1465885342559806848952805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3909027580159484930540813 1465885342559806848952805)
        ·
          refine ⟨274853501729963784178651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1465885342559806848952805 274853501729963784178651)
          ·
            refine ⟨412280252594945676267977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274853501729963784178651 412280252594945676267977)
            ·
              refine ⟨309210189446209257200983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412280252594945676267977 309210189446209257200983)
              ·
                refine ⟨463815284169313885801475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309210189446209257200983 463815284169313885801475)
                ·
                  refine ⟨695722926253970828702213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463815284169313885801475 695722926253970828702213)
                  ·
                    refine ⟨130448048672619530381665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 695722926253970828702213 130448048672619530381665)
                    ·
                      rfl

theorem cell22_381070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_381070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381070 prefixEnd_381070 := by exact prefixLift 381070
  have htrace : WordTrace (prefixWord ++ tailWord_381070) baseStart_381070 baseEnd_381070 := by
    simpa [prefixWord, tailWord_381070, baseEnd_381070] using wordTrace_append hprefix tailTrace_381070
  have hstable : (prefixWord ++ tailWord_381070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381070).length < 2 ^ (prefixWord ++ tailWord_381070).sum := by decide
  have hdescent : baseEnd_381070 < baseStart_381070 := by decide
  rcases family_descends (prefixWord ++ tailWord_381070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381124 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 7]
def baseStart_381124 : Nat := 118140960795 + 381124 * 2 ^ 59
def prefixEnd_381124 : Nat := 4983230072969 + 3 ^ 40 * 381124 * 2
def baseEnd_381124 : Nat := 43488844658727129843833

theorem tailTrace_381124 : CollatzResearch.WordTrace tailWord_381124 prefixEnd_381124 43488844658727129843833 := by
  unfold tailWord_381124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6950367135630156821083213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9267156180840209094777617 6950367135630156821083213)
  ·
    refine ⟨2606387675861308807906205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6950367135630156821083213 2606387675861308807906205)
    ·
      refine ⟨977395378447990802964827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2606387675861308807906205 977395378447990802964827)
      ·
        refine ⟨1466093067671986204447241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977395378447990802964827 1466093067671986204447241)
        ·
          refine ⟨1099569800753989653335431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466093067671986204447241 1099569800753989653335431)
          ·
            refine ⟨1649354701130984480003147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099569800753989653335431 1649354701130984480003147)
            ·
              refine ⟨2474032051696476720004721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649354701130984480003147 2474032051696476720004721)
              ·
                refine ⟨1855524038772357540003541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474032051696476720004721 1855524038772357540003541)
                ·
                  refine ⟨43488844658727129843833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1855524038772357540003541 43488844658727129843833)
                  ·
                    rfl

theorem cell22_381124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_381124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381124 prefixEnd_381124 := by exact prefixLift 381124
  have htrace : WordTrace (prefixWord ++ tailWord_381124) baseStart_381124 baseEnd_381124 := by
    simpa [prefixWord, tailWord_381124, baseEnd_381124] using wordTrace_append hprefix tailTrace_381124
  have hstable : (prefixWord ++ tailWord_381124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381124).length < 2 ^ (prefixWord ++ tailWord_381124).sum := by decide
  have hdescent : baseEnd_381124 < baseStart_381124 := by decide
  rcases family_descends (prefixWord ++ tailWord_381124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381184 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 6, 3]
def baseStart_381184 : Nat := 118140960795 + 381184 * 2 ^ 59
def prefixEnd_381184 : Nat := 4983230072969 + 3 ^ 40 * 381184 * 2
def baseEnd_381184 : Nat := 130487073202361233031315

theorem tailTrace_381184 : CollatzResearch.WordTrace tailWord_381184 prefixEnd_381184 130487073202361233031315 := by
  unfold tailWord_381184
  simp only [CollatzResearch.WordTrace]
  refine ⟨6951461325521471944675303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9268615100695295926233737 6951461325521471944675303)
  ·
    refine ⟨10427191988282207917012955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6951461325521471944675303 10427191988282207917012955)
    ·
      refine ⟨15640787982423311875519433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10427191988282207917012955 15640787982423311875519433)
      ·
        refine ⟨11730590986817483906639575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15640787982423311875519433 11730590986817483906639575)
        ·
          refine ⟨17595886480226225859959363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11730590986817483906639575 17595886480226225859959363)
          ·
            refine ⟨26393829720339338789939045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17595886480226225859959363 26393829720339338789939045)
            ·
              refine ⟨4948843072563626023113571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26393829720339338789939045 4948843072563626023113571)
              ·
                refine ⟨7423264608845439034670357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948843072563626023113571 7423264608845439034670357)
                ·
                  refine ⟨347965528539629954750173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7423264608845439034670357 347965528539629954750173)
                  ·
                    refine ⟨130487073202361233031315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347965528539629954750173 130487073202361233031315)
                    ·
                      rfl

theorem cell22_381184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_381184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381184 prefixEnd_381184 := by exact prefixLift 381184
  have htrace : WordTrace (prefixWord ++ tailWord_381184) baseStart_381184 baseEnd_381184 := by
    simpa [prefixWord, tailWord_381184, baseEnd_381184] using wordTrace_append hprefix tailTrace_381184
  have hstable : (prefixWord ++ tailWord_381184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381184).length < 2 ^ (prefixWord ++ tailWord_381184).sum := by decide
  have hdescent : baseEnd_381184 < baseStart_381184 := by decide
  rcases family_descends (prefixWord ++ tailWord_381184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381201 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_381201 : Nat := 118140960795 + 381201 * 2 ^ 59
def prefixEnd_381201 : Nat := 4983230072969 + 3 ^ 40 * 381201 * 2
def baseEnd_381201 : Nat := 130492892649778855356263

theorem tailTrace_381201 : CollatzResearch.WordTrace tailWord_381201 prefixEnd_381201 130492892649778855356263 := by
  unfold tailWord_381201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903542691981355792719457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9269028461320903861812971 13903542691981355792719457)
  ·
    refine ⟨10427657018986016844539593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13903542691981355792719457 10427657018986016844539593)
    ·
      refine ⟨7820742764239512633404695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10427657018986016844539593 7820742764239512633404695)
      ·
        refine ⟨11731114146359268950107043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7820742764239512633404695 11731114146359268950107043)
        ·
          refine ⟨17596671219538903425160565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11731114146359268950107043 17596671219538903425160565)
          ·
            refine ⟨1649687926831772196108803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17596671219538903425160565 1649687926831772196108803)
            ·
              refine ⟨2474531890247658294163205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649687926831772196108803 2474531890247658294163205)
              ·
                refine ⟨463974729421435930155601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2474531890247658294163205 463974729421435930155601)
                ·
                  refine ⟨347981047066076947616701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463974729421435930155601 347981047066076947616701)
                  ·
                    refine ⟨130492892649778855356263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347981047066076947616701 130492892649778855356263)
                    ·
                      rfl

theorem cell22_381201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_381201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381201 prefixEnd_381201 := by exact prefixLift 381201
  have htrace : WordTrace (prefixWord ++ tailWord_381201) baseStart_381201 baseEnd_381201 := by
    simpa [prefixWord, tailWord_381201, baseEnd_381201] using wordTrace_append hprefix tailTrace_381201
  have hstable : (prefixWord ++ tailWord_381201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381201).length < 2 ^ (prefixWord ++ tailWord_381201).sum := by decide
  have hdescent : baseEnd_381201 < baseStart_381201 := by decide
  rcases family_descends (prefixWord ++ tailWord_381201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381218 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_381218 : Nat := 118140960795 + 381218 * 2 ^ 59
def prefixEnd_381218 : Nat := 4983230072969 + 3 ^ 40 * 381218 * 2
def baseEnd_381218 : Nat := 130498712097196477681211

theorem tailTrace_381218 : CollatzResearch.WordTrace tailWord_381218 prefixEnd_381218 130498712097196477681211 := by
  unfold tailWord_381218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476040683229941924022077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9269441821946511797392205 3476040683229941924022077)
  ·
    refine ⟨1303515256211228221508279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3476040683229941924022077 1303515256211228221508279)
    ·
      refine ⟨1955272884316842332262419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303515256211228221508279 1955272884316842332262419)
      ·
        refine ⟨2932909326475263498393629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955272884316842332262419 2932909326475263498393629)
        ·
          refine ⟨1099840997428223811897611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2932909326475263498393629 1099840997428223811897611)
          ·
            refine ⟨1649761496142335717846417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099840997428223811897611 1649761496142335717846417)
            ·
              refine ⟨1237321122106751788384813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1649761496142335717846417 1237321122106751788384813)
              ·
                refine ⟨463995420790031920644305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1237321122106751788384813 463995420790031920644305)
                ·
                  refine ⟨347996565592523940483229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463995420790031920644305 347996565592523940483229)
                  ·
                    refine ⟨130498712097196477681211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347996565592523940483229 130498712097196477681211)
                    ·
                      rfl

theorem cell22_381218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_381218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381218 prefixEnd_381218 := by exact prefixLift 381218
  have htrace : WordTrace (prefixWord ++ tailWord_381218) baseStart_381218 baseEnd_381218 := by
    simpa [prefixWord, tailWord_381218, baseEnd_381218] using wordTrace_append hprefix tailTrace_381218
  have hstable : (prefixWord ++ tailWord_381218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381218).length < 2 ^ (prefixWord ++ tailWord_381218).sum := by decide
  have hdescent : baseEnd_381218 < baseStart_381218 := by decide
  rcases family_descends (prefixWord ++ tailWord_381218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381233 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_381233 : Nat := 118140960795 + 381233 * 2 ^ 59
def prefixEnd_381233 : Nat := 4983230072969 + 3 ^ 40 * 381233 * 2
def baseEnd_381233 : Nat := 130503846903741438556165

theorem tailTrace_381233 : CollatzResearch.WordTrace tailWord_381233 prefixEnd_381233 130503846903741438556165 := by
  unfold tailWord_381233
  simp only [CollatzResearch.WordTrace]
  refine ⟨13904709827865425257884353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9269806551910283505256235 13904709827865425257884353)
  ·
    refine ⟨10428532370899068943413265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13904709827865425257884353 10428532370899068943413265)
    ·
      refine ⟨7821399278174301707559949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10428532370899068943413265 7821399278174301707559949)
      ·
        refine ⟨2933024729315363140334981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7821399278174301707559949 2933024729315363140334981)
        ·
          refine ⟨549942136746630588812809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2933024729315363140334981 549942136746630588812809)
          ·
            refine ⟨412456602559972941609607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549942136746630588812809 412456602559972941609607)
            ·
              refine ⟨618684903839959412414411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412456602559972941609607 618684903839959412414411)
              ·
                refine ⟨928027355759939118621617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618684903839959412414411 928027355759939118621617)
                ·
                  refine ⟨696020516819954338966213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928027355759939118621617 696020516819954338966213)
                  ·
                    refine ⟨130503846903741438556165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696020516819954338966213 130503846903741438556165)
                    ·
                      rfl

theorem cell22_381233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_381233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381233 prefixEnd_381233 := by exact prefixLift 381233
  have htrace : WordTrace (prefixWord ++ tailWord_381233) baseStart_381233 baseEnd_381233 := by
    simpa [prefixWord, tailWord_381233, baseEnd_381233] using wordTrace_append hprefix tailTrace_381233
  have hstable : (prefixWord ++ tailWord_381233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381233).length < 2 ^ (prefixWord ++ tailWord_381233).sum := by decide
  have hdescent : baseEnd_381233 < baseStart_381233 := by decide
  rcases family_descends (prefixWord ++ tailWord_381233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381252 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_381252 : Nat := 118140960795 + 381252 * 2 ^ 59
def prefixEnd_381252 : Nat := 4983230072969 + 3 ^ 40 * 381252 * 2
def baseEnd_381252 : Nat := 130510350992031722331107

theorem tailTrace_381252 : CollatzResearch.WordTrace tailWord_381252 prefixEnd_381252 130510350992031722331107 := by
  unfold tailWord_381252
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952701407398295751413005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9270268543197727668550673 6952701407398295751413005)
  ·
    refine ⟨2607263027774360906779877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6952701407398295751413005 2607263027774360906779877)
    ·
      refine ⟨488861817707692670021227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2607263027774360906779877 488861817707692670021227)
      ·
        refine ⟨733292726561539005031841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488861817707692670021227 733292726561539005031841)
        ·
          refine ⟨549969544921154253773881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733292726561539005031841 549969544921154253773881)
          ·
            refine ⟨412477158690865690330411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549969544921154253773881 412477158690865690330411)
            ·
              refine ⟨618715738036298535495617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412477158690865690330411 618715738036298535495617)
              ·
                refine ⟨464036803527223901621713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 618715738036298535495617 464036803527223901621713)
                ·
                  refine ⟨348027602645417926216285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464036803527223901621713 348027602645417926216285)
                  ·
                    refine ⟨130510350992031722331107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348027602645417926216285 130510350992031722331107)
                    ·
                      rfl

theorem cell22_381252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_381252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381252 prefixEnd_381252 := by exact prefixLift 381252
  have htrace : WordTrace (prefixWord ++ tailWord_381252) baseStart_381252 baseEnd_381252 := by
    simpa [prefixWord, tailWord_381252, baseEnd_381252] using wordTrace_append hprefix tailTrace_381252
  have hstable : (prefixWord ++ tailWord_381252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381252).length < 2 ^ (prefixWord ++ tailWord_381252).sum := by decide
  have hdescent : baseEnd_381252 < baseStart_381252 := by decide
  rcases family_descends (prefixWord ++ tailWord_381252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381259 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 5]
def baseStart_381259 : Nat := 118140960795 + 381259 * 2 ^ 59
def prefixEnd_381259 : Nat := 4983230072969 + 3 ^ 40 * 381259 * 2
def baseEnd_381259 : Nat := 43504249078362012468695

theorem tailTrace_381259 : CollatzResearch.WordTrace tailWord_381259 prefixEnd_381259 43504249078362012468695 := by
  unfold tailWord_381259
  simp only [CollatzResearch.WordTrace]
  refine ⟨13905658125771231698330831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9270438750514154465553887 13905658125771231698330831)
  ·
    refine ⟨20858487188656847547496247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13905658125771231698330831 20858487188656847547496247)
    ·
      refine ⟨31287730782985271321244371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20858487188656847547496247 31287730782985271321244371)
      ·
        refine ⟨46931596174477906981866557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31287730782985271321244371 46931596174477906981866557)
        ·
          refine ⟨17599348565429215118199959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46931596174477906981866557 17599348565429215118199959)
          ·
            refine ⟨26399022848143822677299939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17599348565429215118199959 26399022848143822677299939)
            ·
              refine ⟨39598534272215734015949909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26399022848143822677299939 39598534272215734015949909)
              ·
                refine ⟨464045323502528132999413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 39598534272215734015949909 464045323502528132999413)
                ·
                  refine ⟨43504249078362012468695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464045323502528132999413 43504249078362012468695)
                  ·
                    rfl

theorem cell22_381259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 5].length) (baseStart_381259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381259 prefixEnd_381259 := by exact prefixLift 381259
  have htrace : WordTrace (prefixWord ++ tailWord_381259) baseStart_381259 baseEnd_381259 := by
    simpa [prefixWord, tailWord_381259, baseEnd_381259] using wordTrace_append hprefix tailTrace_381259
  have hstable : (prefixWord ++ tailWord_381259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381259).length < 2 ^ (prefixWord ++ tailWord_381259).sum := by decide
  have hdescent : baseEnd_381259 < baseStart_381259 := by decide
  rcases family_descends (prefixWord ++ tailWord_381259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381314 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_381314 : Nat := 118140960795 + 381314 * 2 ^ 59
def prefixEnd_381314 : Nat := 4983230072969 + 3 ^ 40 * 381314 * 2
def baseEnd_381314 : Nat := 130531574859084227280917

theorem tailTrace_381314 : CollatzResearch.WordTrace tailWord_381314 prefixEnd_381314 130531574859084227280917 := by
  unfold tailWord_381314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476916035142994022895749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9271776093714650727721997 3476916035142994022895749)
  ·
    refine ⟨651921756589311379292953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3476916035142994022895749 651921756589311379292953)
    ·
      refine ⟨488941317441983534469715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651921756589311379292953 488941317441983534469715)
      ·
        refine ⟨733411976162975301704573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488941317441983534469715 733411976162975301704573)
        ·
          refine ⟨275029491061115738139215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 733411976162975301704573 275029491061115738139215)
          ·
            refine ⟨412544236591673607208823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275029491061115738139215 412544236591673607208823)
            ·
              refine ⟨618816354887510410813235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412544236591673607208823 618816354887510410813235)
              ·
                refine ⟨928224532331265616219853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618816354887510410813235 928224532331265616219853)
                ·
                  refine ⟨348084199624224606082445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928224532331265616219853 348084199624224606082445)
                  ·
                    refine ⟨130531574859084227280917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348084199624224606082445 130531574859084227280917)
                    ·
                      rfl

theorem cell22_381314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_381314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381314 prefixEnd_381314 := by exact prefixLift 381314
  have htrace : WordTrace (prefixWord ++ tailWord_381314) baseStart_381314 baseEnd_381314 := by
    simpa [prefixWord, tailWord_381314, baseEnd_381314] using wordTrace_append hprefix tailTrace_381314
  have hstable : (prefixWord ++ tailWord_381314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381314).length < 2 ^ (prefixWord ++ tailWord_381314).sum := by decide
  have hdescent : baseEnd_381314 < baseStart_381314 := by decide
  rcases family_descends (prefixWord ++ tailWord_381314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381321 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 6]
def baseStart_381321 : Nat := 118140960795 + 381321 * 2 ^ 59
def prefixEnd_381321 : Nat := 4983230072969 + 3 ^ 40 * 381321 * 2
def baseEnd_381321 : Nat := 43511323700712847451965

theorem tailTrace_381321 : CollatzResearch.WordTrace tailWord_381321 prefixEnd_381321 43511323700712847451965 := by
  unfold tailWord_381321
  simp only [CollatzResearch.WordTrace]
  refine ⟨13907919451546616287087817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9271946301031077524725211 13907919451546616287087817)
  ·
    refine ⟨10430939588659962215315863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13907919451546616287087817 10430939588659962215315863)
    ·
      refine ⟨15646409382989943322973795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10430939588659962215315863 15646409382989943322973795)
      ·
        refine ⟨23469614074484914984460693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15646409382989943322973795 23469614074484914984460693)
        ·
          refine ⟨1100138159741480389896595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23469614074484914984460693 1100138159741480389896595)
          ·
            refine ⟨1650207239612220584844893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100138159741480389896595 1650207239612220584844893)
            ·
              refine ⟨618827714854582719316835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1650207239612220584844893 618827714854582719316835)
              ·
                refine ⟨928241572281874078975253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618827714854582719316835 928241572281874078975253)
                ·
                  refine ⟨43511323700712847451965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 928241572281874078975253 43511323700712847451965)
                  ·
                    rfl

theorem cell22_381321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_381321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381321 prefixEnd_381321 := by exact prefixLift 381321
  have htrace : WordTrace (prefixWord ++ tailWord_381321) baseStart_381321 baseEnd_381321 := by
    simpa [prefixWord, tailWord_381321, baseEnd_381321] using wordTrace_append hprefix tailTrace_381321
  have hstable : (prefixWord ++ tailWord_381321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381321).length < 2 ^ (prefixWord ++ tailWord_381321).sum := by decide
  have hdescent : baseEnd_381321 < baseStart_381321 := by decide
  rcases family_descends (prefixWord ++ tailWord_381321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381349 : List Nat := [1, 3, 1, 2, 1, 1, 3, 10]
def baseStart_381349 : Nat := 118140960795 + 381349 * 2 ^ 59
def prefixEnd_381349 : Nat := 4983230072969 + 3 ^ 40 * 381349 * 2
def baseEnd_381349 : Nat := 14504839563817311406201

theorem tailTrace_381349 : CollatzResearch.WordTrace tailWord_381349 prefixEnd_381349 14504839563817311406201 := by
  unfold tailWord_381349
  simp only [CollatzResearch.WordTrace]
  refine ⟨13908940695445177069107101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9272627130296784712738067 13908940695445177069107101)
  ·
    refine ⟨5215852760791941400915163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13908940695445177069107101 5215852760791941400915163)
    ·
      refine ⟨7823779141187912101372745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5215852760791941400915163 7823779141187912101372745)
      ·
        refine ⟨5867834355890934076029559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823779141187912101372745 5867834355890934076029559)
        ·
          refine ⟨8801751533836401114044339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5867834355890934076029559 8801751533836401114044339)
          ·
            refine ⟨13202627300754601671066509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8801751533836401114044339 13202627300754601671066509)
            ·
              refine ⟨4950985237782975626649941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13202627300754601671066509 4950985237782975626649941)
              ·
                refine ⟨14504839563817311406201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4950985237782975626649941 14504839563817311406201)
                ·
                  rfl

theorem cell22_381349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 10].length) (baseStart_381349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381349 prefixEnd_381349 := by exact prefixLift 381349
  have htrace : WordTrace (prefixWord ++ tailWord_381349) baseStart_381349 baseEnd_381349 := by
    simpa [prefixWord, tailWord_381349, baseEnd_381349] using wordTrace_append hprefix tailTrace_381349
  have hstable : (prefixWord ++ tailWord_381349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381349).length < 2 ^ (prefixWord ++ tailWord_381349).sum := by decide
  have hdescent : baseEnd_381349 < baseStart_381349 := by decide
  rcases family_descends (prefixWord ++ tailWord_381349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381357 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_381357 : Nat := 118140960795 + 381357 * 2 ^ 59
def prefixEnd_381357 : Nat := 4983230072969 + 3 ^ 40 * 381357 * 2
def baseEnd_381357 : Nat := 130546294637846448455785

theorem tailTrace_381357 : CollatzResearch.WordTrace tailWord_381357 prefixEnd_381357 130546294637846448455785 := by
  unfold tailWord_381357
  simp only [CollatzResearch.WordTrace]
  refine ⟨13909232479416194435398325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9272821652944129623598883 13909232479416194435398325)
  ·
    refine ⟨1303990544945268228318593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13909232479416194435398325 1303990544945268228318593)
    ·
      refine ⟨977992908708951171238945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1303990544945268228318593 977992908708951171238945)
      ·
        refine ⟨733494681531713378429209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 977992908708951171238945 733494681531713378429209)
        ·
          refine ⟨550121011148785033821907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733494681531713378429209 550121011148785033821907)
          ·
            refine ⟨825181516723177550732861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550121011148785033821907 825181516723177550732861)
            ·
              refine ⟨309443068771191581524823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825181516723177550732861 309443068771191581524823)
              ·
                refine ⟨464164603156787372287235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309443068771191581524823 464164603156787372287235)
                ·
                  refine ⟨696246904735181058430853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464164603156787372287235 696246904735181058430853)
                  ·
                    refine ⟨130546294637846448455785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696246904735181058430853 130546294637846448455785)
                    ·
                      rfl

theorem cell22_381357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_381357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381357 prefixEnd_381357 := by exact prefixLift 381357
  have htrace : WordTrace (prefixWord ++ tailWord_381357) baseStart_381357 baseEnd_381357 := by
    simpa [prefixWord, tailWord_381357, baseEnd_381357] using wordTrace_append hprefix tailTrace_381357
  have hstable : (prefixWord ++ tailWord_381357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381357).length < 2 ^ (prefixWord ++ tailWord_381357).sum := by decide
  have hdescent : baseEnd_381357 < baseStart_381357 := by decide
  rcases family_descends (prefixWord ++ tailWord_381357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381372 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_381372 : Nat := 118140960795 + 381372 * 2 ^ 59
def prefixEnd_381372 : Nat := 4983230072969 + 3 ^ 40 * 381372 * 2
def baseEnd_381372 : Nat := 43517143148130469776913

theorem tailTrace_381372 : CollatzResearch.WordTrace tailWord_381372 prefixEnd_381372 43517143148130469776913 := by
  unfold tailWord_381372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954889787180925998597185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9273186382907901331462913 6954889787180925998597185)
  ·
    refine ⟨5216167340385694498947889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6954889787180925998597185 5216167340385694498947889)
    ·
      refine ⟨3912125505289270874210917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5216167340385694498947889 3912125505289270874210917)
      ·
        refine ⟨733523532241738288914547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3912125505289270874210917 733523532241738288914547)
        ·
          refine ⟨1100285298362607433371821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733523532241738288914547 1100285298362607433371821)
          ·
            refine ⟨412606986885977787514433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1100285298362607433371821 412606986885977787514433)
            ·
              refine ⟨309455240164483340635825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412606986885977787514433 309455240164483340635825)
              ·
                refine ⟨232091430123362505476869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309455240164483340635825 232091430123362505476869)
                ·
                  refine ⟨43517143148130469776913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232091430123362505476869 43517143148130469776913)
                  ·
                    rfl

theorem cell22_381372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_381372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381372 prefixEnd_381372 := by exact prefixLift 381372
  have htrace : WordTrace (prefixWord ++ tailWord_381372) baseStart_381372 baseEnd_381372 := by
    simpa [prefixWord, tailWord_381372, baseEnd_381372] using wordTrace_append hprefix tailTrace_381372
  have hstable : (prefixWord ++ tailWord_381372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381372).length < 2 ^ (prefixWord ++ tailWord_381372).sum := by decide
  have hdescent : baseEnd_381372 < baseStart_381372 := by decide
  rcases family_descends (prefixWord ++ tailWord_381372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381381 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_381381 : Nat := 118140960795 + 381381 * 2 ^ 59
def prefixEnd_381381 : Nat := 4983230072969 + 3 ^ 40 * 381381 * 2
def baseEnd_381381 : Nat := 130554510328318385855711

theorem tailTrace_381381 : CollatzResearch.WordTrace tailWord_381381 prefixEnd_381381 130554510328318385855711 := by
  unfold tailWord_381381
  simp only [CollatzResearch.WordTrace]
  refine ⟨13910107831329246534271997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9273405220886164356181331 13910107831329246534271997)
  ·
    refine ⟨5216290436748467450351999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13910107831329246534271997 5216290436748467450351999)
    ·
      refine ⟨7824435655122701175527999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5216290436748467450351999 7824435655122701175527999)
      ·
        refine ⟨11736653482684051763291999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824435655122701175527999 11736653482684051763291999)
        ·
          refine ⟨17604980224026077644937999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11736653482684051763291999 17604980224026077644937999)
          ·
            refine ⟨26407470336039116467406999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17604980224026077644937999 26407470336039116467406999)
            ·
              refine ⟨39611205504058674701110499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26407470336039116467406999 39611205504058674701110499)
              ·
                refine ⟨59416808256088012051665749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39611205504058674701110499 59416808256088012051665749)
                ·
                  refine ⟨348145360875515695615229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59416808256088012051665749 348145360875515695615229)
                  ·
                    refine ⟨130554510328318385855711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348145360875515695615229 130554510328318385855711)
                    ·
                      rfl

theorem cell22_381381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_381381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381381 prefixEnd_381381 := by exact prefixLift 381381
  have htrace : WordTrace (prefixWord ++ tailWord_381381) baseStart_381381 baseEnd_381381 := by
    simpa [prefixWord, tailWord_381381, baseEnd_381381] using wordTrace_append hprefix tailTrace_381381
  have hstable : (prefixWord ++ tailWord_381381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381381).length < 2 ^ (prefixWord ++ tailWord_381381).sum := by decide
  have hdescent : baseEnd_381381 < baseStart_381381 := by decide
  rcases family_descends (prefixWord ++ tailWord_381381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381471 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_381471 : Nat := 118140960795 + 381471 * 2 ^ 59
def prefixEnd_381471 : Nat := 4983230072969 + 3 ^ 40 * 381471 * 2
def baseEnd_381471 : Nat := 130585319167588151105435

theorem tailTrace_381471 : CollatzResearch.WordTrace tailWord_381471 prefixEnd_381471 130585319167588151105435 := by
  unfold tailWord_381471
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913390401003191905048267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9275593600668794603365511 13913390401003191905048267)
  ·
    refine ⟨20870085601504787857572401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13913390401003191905048267 20870085601504787857572401)
    ·
      refine ⟨15652564201128590893179301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20870085601504787857572401 15652564201128590893179301)
      ·
        refine ⟨2934855787711610792471119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15652564201128590893179301 2934855787711610792471119)
        ·
          refine ⟨4402283681567416188706679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2934855787711610792471119 4402283681567416188706679)
          ·
            refine ⟨6603425522351124283060019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402283681567416188706679 6603425522351124283060019)
            ·
              refine ⟨9905138283526686424590029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603425522351124283060019 9905138283526686424590029)
              ·
                refine ⟨3714426856322507409221261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9905138283526686424590029 3714426856322507409221261)
                ·
                  refine ⟨1392910071120940278457973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3714426856322507409221261 1392910071120940278457973)
                  ·
                    refine ⟨130585319167588151105435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1392910071120940278457973 130585319167588151105435)
                    ·
                      rfl

theorem cell22_381471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_381471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381471 prefixEnd_381471 := by exact prefixLift 381471
  have htrace : WordTrace (prefixWord ++ tailWord_381471) baseStart_381471 baseEnd_381471 := by
    simpa [prefixWord, tailWord_381471, baseEnd_381471] using wordTrace_append hprefix tailTrace_381471
  have hstable : (prefixWord ++ tailWord_381471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381471).length < 2 ^ (prefixWord ++ tailWord_381471).sum := by decide
  have hdescent : baseEnd_381471 < baseStart_381471 := by decide
  rcases family_descends (prefixWord ++ tailWord_381471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381488 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 4, 3]
def baseStart_381488 : Nat := 118140960795 + 381488 * 2 ^ 59
def prefixEnd_381488 : Nat := 4983230072969 + 3 ^ 40 * 381488 * 2
def baseEnd_381488 : Nat := 130591138615005773430383

theorem tailTrace_381488 : CollatzResearch.WordTrace tailWord_381488 prefixEnd_381488 130591138615005773430383 := by
  unfold tailWord_381488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957005220970801904208559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9276006961294402538944745 6957005220970801904208559)
  ·
    refine ⟨10435507831456202856312839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6957005220970801904208559 10435507831456202856312839)
    ·
      refine ⟨15653261747184304284469259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10435507831456202856312839 15653261747184304284469259)
      ·
        refine ⟨23479892620776456426703889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15653261747184304284469259 23479892620776456426703889)
        ·
          refine ⟨17609919465582342320027917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23479892620776456426703889 17609919465582342320027917)
          ·
            refine ⟨6603719799593378370010469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17609919465582342320027917 6603719799593378370010469)
            ·
              refine ⟨1238197462423758444376963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6603719799593378370010469 1238197462423758444376963)
              ·
                refine ⟨1857296193635637666565445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238197462423758444376963 1857296193635637666565445)
                ·
                  refine ⟨348243036306682062481021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1857296193635637666565445 348243036306682062481021)
                  ·
                    refine ⟨130591138615005773430383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348243036306682062481021 130591138615005773430383)
                    ·
                      rfl

theorem cell22_381488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_381488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381488 prefixEnd_381488 := by exact prefixLift 381488
  have htrace : WordTrace (prefixWord ++ tailWord_381488) baseStart_381488 baseEnd_381488 := by
    simpa [prefixWord, tailWord_381488, baseEnd_381488] using wordTrace_append hprefix tailTrace_381488
  have hstable : (prefixWord ++ tailWord_381488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381488).length < 2 ^ (prefixWord ++ tailWord_381488).sum := by decide
  have hdescent : baseEnd_381488 < baseStart_381488 := by decide
  rcases family_descends (prefixWord ++ tailWord_381488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381614 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_381614 : Nat := 118140960795 + 381614 * 2 ^ 59
def prefixEnd_381614 : Nat := 4983230072969 + 3 ^ 40 * 381614 * 2
def baseEnd_381614 : Nat := 43544756996661148259999

theorem tailTrace_381614 : CollatzResearch.WordTrace tailWord_381614 prefixEnd_381614 43544756996661148259999 := by
  unfold tailWord_381614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739825754935640915937987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9279070692990084885002597 1739825754935640915937987)
  ·
    refine ⟨2609738632403461373906981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739825754935640915937987 2609738632403461373906981)
    ·
      refine ⟨489325993575649007607559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2609738632403461373906981 489325993575649007607559)
      ·
        refine ⟨733988990363473511411339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489325993575649007607559 733988990363473511411339)
        ·
          refine ⟨1100983485545210267117009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733988990363473511411339 1100983485545210267117009)
          ·
            refine ⟨825737614158907700337757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100983485545210267117009 825737614158907700337757)
            ·
              refine ⟨309651605309590387626659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825737614158907700337757 309651605309590387626659)
              ·
                refine ⟨464477407964385581439989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309651605309590387626659 464477407964385581439989)
                ·
                  refine ⟨43544756996661148259999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464477407964385581439989 43544756996661148259999)
                  ·
                    rfl

theorem cell22_381614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_381614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381614 prefixEnd_381614 := by exact prefixLift 381614
  have htrace : WordTrace (prefixWord ++ tailWord_381614) baseStart_381614 baseEnd_381614 := by
    simpa [prefixWord, tailWord_381614, baseEnd_381614] using wordTrace_append hprefix tailTrace_381614
  have hstable : (prefixWord ++ tailWord_381614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381614).length < 2 ^ (prefixWord ++ tailWord_381614).sum := by decide
  have hdescent : baseEnd_381614 < baseStart_381614 := by decide
  rcases family_descends (prefixWord ++ tailWord_381614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381640 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 4, 3]
def baseStart_381640 : Nat := 118140960795 + 381640 * 2 ^ 59
def prefixEnd_381640 : Nat := 4983230072969 + 3 ^ 40 * 381640 * 2
def baseEnd_381640 : Nat := 130643171321328043629917

theorem tailTrace_381640 : CollatzResearch.WordTrace tailWord_381640 prefixEnd_381640 130643171321328043629917 := by
  unfold tailWord_381640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959777168695466883975187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9279702891593955845300249 6959777168695466883975187)
  ·
    refine ⟨10439665753043200325962781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6959777168695466883975187 10439665753043200325962781)
    ·
      refine ⟨3914874657391200122236043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10439665753043200325962781 3914874657391200122236043)
      ·
        refine ⟨5872311986086800183354065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914874657391200122236043 5872311986086800183354065)
        ·
          refine ⟨4404233989565100137515549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5872311986086800183354065 4404233989565100137515549)
          ·
            refine ⟨1651587746086912551568331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4404233989565100137515549 1651587746086912551568331)
            ·
              refine ⟨2477381619130368827352497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651587746086912551568331 2477381619130368827352497)
              ·
                refine ⟨1858036214347776620514373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477381619130368827352497 1858036214347776620514373)
                ·
                  refine ⟨348381790190208116346445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858036214347776620514373 348381790190208116346445)
                  ·
                    refine ⟨130643171321328043629917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348381790190208116346445 130643171321328043629917)
                    ·
                      rfl

theorem cell22_381640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_381640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381640 prefixEnd_381640 := by exact prefixLift 381640
  have htrace : WordTrace (prefixWord ++ tailWord_381640) baseStart_381640 baseEnd_381640 := by
    simpa [prefixWord, tailWord_381640, baseEnd_381640] using wordTrace_append hprefix tailTrace_381640
  have hstable : (prefixWord ++ tailWord_381640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381640).length < 2 ^ (prefixWord ++ tailWord_381640).sum := by decide
  have hdescent : baseEnd_381640 < baseStart_381640 := by decide
  rcases family_descends (prefixWord ++ tailWord_381640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381642 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_381642 : Nat := 118140960795 + 381642 * 2 ^ 59
def prefixEnd_381642 : Nat := 4983230072969 + 3 ^ 40 * 381642 * 2
def baseEnd_381642 : Nat := 43547951987400235026637

theorem tailTrace_381642 : CollatzResearch.WordTrace tailWord_381642 prefixEnd_381642 43547951987400235026637 := by
  unfold tailWord_381642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479906820845922027380795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9279751522255792073015453 3479906820845922027380795)
  ·
    refine ⟨5219860231268883041071193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479906820845922027380795 5219860231268883041071193)
    ·
      refine ⟨3914895173451662280803395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5219860231268883041071193 3914895173451662280803395)
      ·
        refine ⟨5872342760177493421205093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914895173451662280803395 5872342760177493421205093)
        ·
          refine ⟨1101064267533280016475955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5872342760177493421205093 1101064267533280016475955)
          ·
            refine ⟨1651596401299920024713933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101064267533280016475955 1651596401299920024713933)
            ·
              refine ⟨619348650487470009267725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1651596401299920024713933 619348650487470009267725)
              ·
                refine ⟨232255743932801253475397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 619348650487470009267725 232255743932801253475397)
                ·
                  refine ⟨43547951987400235026637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232255743932801253475397 43547951987400235026637)
                  ·
                    rfl

theorem cell22_381642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_381642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381642 prefixEnd_381642 := by exact prefixLift 381642
  have htrace : WordTrace (prefixWord ++ tailWord_381642) baseStart_381642 baseEnd_381642 := by
    simpa [prefixWord, tailWord_381642, baseEnd_381642] using wordTrace_append hprefix tailTrace_381642
  have hstable : (prefixWord ++ tailWord_381642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381642).length < 2 ^ (prefixWord ++ tailWord_381642).sum := by decide
  have hdescent : baseEnd_381642 < baseStart_381642 := by decide
  rcases family_descends (prefixWord ++ tailWord_381642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381655 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_381655 : Nat := 118140960795 + 381655 * 2 ^ 59
def prefixEnd_381655 : Nat := 4983230072969 + 3 ^ 40 * 381655 * 2
def baseEnd_381655 : Nat := 130648306127873004504871

theorem tailTrace_381655 : CollatzResearch.WordTrace tailWord_381655 prefixEnd_381655 130648306127873004504871 := by
  unfold tailWord_381655
  simp only [CollatzResearch.WordTrace]
  refine ⟨13920101432336591329746419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9280067621557727553164279 13920101432336591329746419)
  ·
    refine ⟨20880152148504886994619629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13920101432336591329746419 20880152148504886994619629)
    ·
      refine ⟨7830057055689332622982361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20880152148504886994619629 7830057055689332622982361)
      ·
        refine ⟨5872542791766999467236771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7830057055689332622982361 5872542791766999467236771)
        ·
          refine ⟨8808814187650499200855157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5872542791766999467236771 8808814187650499200855157)
          ·
            refine ⟨825826330092234300080171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8808814187650499200855157 825826330092234300080171)
            ·
              refine ⟨1238739495138351450120257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825826330092234300080171 1238739495138351450120257)
              ·
                refine ⟨929054621353763587590193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238739495138351450120257 929054621353763587590193)
                ·
                  refine ⟨696790966015322690692645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 929054621353763587590193 696790966015322690692645)
                  ·
                    refine ⟨130648306127873004504871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696790966015322690692645 130648306127873004504871)
                    ·
                      rfl

theorem cell22_381655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_381655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381655 prefixEnd_381655 := by exact prefixLift 381655
  have htrace : WordTrace (prefixWord ++ tailWord_381655) baseStart_381655 baseEnd_381655 := by
    simpa [prefixWord, tailWord_381655, baseEnd_381655] using wordTrace_append hprefix tailTrace_381655
  have hstable : (prefixWord ++ tailWord_381655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381655).length < 2 ^ (prefixWord ++ tailWord_381655).sum := by decide
  have hdescent : baseEnd_381655 < baseStart_381655 := by decide
  rcases family_descends (prefixWord ++ tailWord_381655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381715 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 5]
def baseStart_381715 : Nat := 118140960795 + 381715 * 2 ^ 59
def prefixEnd_381715 : Nat := 4983230072969 + 3 ^ 40 * 381715 * 2
def baseEnd_381715 : Nat := 43556281784684282668229

theorem tailTrace_381715 : CollatzResearch.WordTrace tailWord_381715 prefixEnd_381715 43556281784684282668229 := by
  unfold tailWord_381715
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922289812119221576930599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9281526541412814384620399 13922289812119221576930599)
  ·
    refine ⟨20883434718178832365395899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13922289812119221576930599 20883434718178832365395899)
    ·
      refine ⟨31325152077268248548093849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20883434718178832365395899 31325152077268248548093849)
      ·
        refine ⟨23493864057951186411070387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31325152077268248548093849 23493864057951186411070387)
        ·
          refine ⟨35240796086926779616605581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23493864057951186411070387 35240796086926779616605581)
          ·
            refine ⟨13215298532597542356227093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35240796086926779616605581 13215298532597542356227093)
            ·
              refine ⟨619467118715509797948145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13215298532597542356227093 619467118715509797948145)
              ·
                refine ⟨464600339036632348461109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619467118715509797948145 464600339036632348461109)
                ·
                  refine ⟨43556281784684282668229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 464600339036632348461109 43556281784684282668229)
                  ·
                    rfl

theorem cell22_381715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 5].length) (baseStart_381715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381715 prefixEnd_381715 := by exact prefixLift 381715
  have htrace : WordTrace (prefixWord ++ tailWord_381715) baseStart_381715 baseEnd_381715 := by
    simpa [prefixWord, tailWord_381715, baseEnd_381715] using wordTrace_append hprefix tailTrace_381715
  have hstable : (prefixWord ++ tailWord_381715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381715).length < 2 ^ (prefixWord ++ tailWord_381715).sum := by decide
  have hdescent : baseEnd_381715 < baseStart_381715 := by decide
  rcases family_descends (prefixWord ++ tailWord_381715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381730 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_381730 : Nat := 118140960795 + 381730 * 2 ^ 59
def prefixEnd_381730 : Nat := 4983230072969 + 3 ^ 40 * 381730 * 2
def baseEnd_381730 : Nat := 130673980160597808879641

theorem tailTrace_381730 : CollatzResearch.WordTrace tailWord_381730 prefixEnd_381730 130673980160597808879641 := by
  unfold tailWord_381730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480709226766219784681661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9281891271376586092484429 3480709226766219784681661)
  ·
    refine ⟨1305265960037332419255623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3480709226766219784681661 1305265960037332419255623)
    ·
      refine ⟨1957898940055998628883435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305265960037332419255623 1957898940055998628883435)
      ·
        refine ⟨2936848410083997943325153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957898940055998628883435 2936848410083997943325153)
        ·
          refine ⟨2202636307562998457493865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936848410083997943325153 2202636307562998457493865)
          ·
            refine ⟨1651977230672248843120399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202636307562998457493865 1651977230672248843120399)
            ·
              refine ⟨2477965846008373264680599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651977230672248843120399 2477965846008373264680599)
              ·
                refine ⟨3716948769012559897020899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477965846008373264680599 3716948769012559897020899)
                ·
                  refine ⟨5575423153518839845531349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716948769012559897020899 5575423153518839845531349)
                  ·
                    refine ⟨130673980160597808879641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5575423153518839845531349 130673980160597808879641)
                    ·
                      rfl

theorem cell22_381730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_381730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381730 prefixEnd_381730 := by exact prefixLift 381730
  have htrace : WordTrace (prefixWord ++ tailWord_381730) baseStart_381730 baseEnd_381730 := by
    simpa [prefixWord, tailWord_381730, baseEnd_381730] using wordTrace_append hprefix tailTrace_381730
  have hstable : (prefixWord ++ tailWord_381730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381730).length < 2 ^ (prefixWord ++ tailWord_381730).sum := by decide
  have hdescent : baseEnd_381730 < baseStart_381730 := by decide
  rcases family_descends (prefixWord ++ tailWord_381730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381745 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_381745 : Nat := 118140960795 + 381745 * 2 ^ 59
def prefixEnd_381745 : Nat := 4983230072969 + 3 ^ 40 * 381745 * 2
def baseEnd_381745 : Nat := 130679114967142769754595

theorem tailTrace_381745 : CollatzResearch.WordTrace tailWord_381745 prefixEnd_381745 130679114967142769754595 := by
  unfold tailWord_381745
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923384002010536700522689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9282256001340357800348459 13923384002010536700522689)
  ·
    refine ⟨10442538001507902525392017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13923384002010536700522689 10442538001507902525392017)
    ·
      refine ⟨7831903501130926894044013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10442538001507902525392017 7831903501130926894044013)
      ·
        refine ⟨2936963812924097585266505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7831903501130926894044013 2936963812924097585266505)
        ·
          refine ⟨2202722859693073188949879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936963812924097585266505 2202722859693073188949879)
          ·
            refine ⟨3304084289539609783424819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202722859693073188949879 3304084289539609783424819)
            ·
              refine ⟨4956126434309414675137229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304084289539609783424819 4956126434309414675137229)
              ·
                refine ⟨1858547412866030503176461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4956126434309414675137229 1858547412866030503176461)
                ·
                  refine ⟨696955279824761438691173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1858547412866030503176461 696955279824761438691173)
                  ·
                    refine ⟨130679114967142769754595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696955279824761438691173 130679114967142769754595)
                    ·
                      rfl

theorem cell22_381745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_381745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381745 prefixEnd_381745 := by exact prefixLift 381745
  have htrace : WordTrace (prefixWord ++ tailWord_381745) baseStart_381745 baseEnd_381745 := by
    simpa [prefixWord, tailWord_381745, baseEnd_381745] using wordTrace_append hprefix tailTrace_381745
  have hstable : (prefixWord ++ tailWord_381745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381745).length < 2 ^ (prefixWord ++ tailWord_381745).sum := by decide
  have hdescent : baseEnd_381745 < baseStart_381745 := by decide
  rcases family_descends (prefixWord ++ tailWord_381745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381777 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 6]
def baseStart_381777 : Nat := 118140960795 + 381777 * 2 ^ 59
def prefixEnd_381777 : Nat := 4983230072969 + 3 ^ 40 * 381777 * 2
def baseEnd_381777 : Nat := 43563356407035117651499

theorem tailTrace_381777 : CollatzResearch.WordTrace tailWord_381777 prefixEnd_381777 43563356407035117651499 := by
  unfold tailWord_381777
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924551137894606165687585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9283034091929737443791723 13924551137894606165687585)
  ·
    refine ⟨10443413353420954624265689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13924551137894606165687585 10443413353420954624265689)
    ·
      refine ⟨7832560015065715968199267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10443413353420954624265689 7832560015065715968199267)
      ·
        refine ⟨11748840022598573952298901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832560015065715968199267 11748840022598573952298901)
        ·
          refine ⟨550726876059308154014011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11748840022598573952298901 550726876059308154014011)
          ·
            refine ⟨826090314088962231021017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550726876059308154014011 826090314088962231021017)
            ·
              refine ⟨619567735566721673265763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826090314088962231021017 619567735566721673265763)
              ·
                refine ⟨929351603350082509898645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619567735566721673265763 929351603350082509898645)
                ·
                  refine ⟨43563356407035117651499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 929351603350082509898645 43563356407035117651499)
                  ·
                    rfl

theorem cell22_381777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_381777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381777 prefixEnd_381777 := by exact prefixLift 381777
  have htrace : WordTrace (prefixWord ++ tailWord_381777) baseStart_381777 baseEnd_381777 := by
    simpa [prefixWord, tailWord_381777, baseEnd_381777] using wordTrace_append hprefix tailTrace_381777
  have hstable : (prefixWord ++ tailWord_381777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381777).length < 2 ^ (prefixWord ++ tailWord_381777).sum := by decide
  have hdescent : baseEnd_381777 < baseStart_381777 := by decide
  rcases family_descends (prefixWord ++ tailWord_381777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381888 : List Nat := [2, 1, 1, 2, 3, 5, 2, 2, 1, 3]
def baseStart_381888 : Nat := 118140960795 + 381888 * 2 ^ 59
def prefixEnd_381888 : Nat := 4983230072969 + 3 ^ 40 * 381888 * 2
def baseEnd_381888 : Nat := 130728066789538063429157

theorem tailTrace_381888 : CollatzResearch.WordTrace tailWord_381888 prefixEnd_381888 130728066789538063429157 := by
  unfold tailWord_381888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6964299820246236061489159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9285733093661648081985545 6964299820246236061489159)
  ·
    refine ⟨10446449730369354092233739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6964299820246236061489159 10446449730369354092233739)
    ·
      refine ⟨15669674595554031138350609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10446449730369354092233739 15669674595554031138350609)
      ·
        refine ⟨11752255946665523353762957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15669674595554031138350609 11752255946665523353762957)
        ·
          refine ⟨4407095979999571257661109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11752255946665523353762957 4407095979999571257661109)
          ·
            refine ⟨413165248124959805405729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4407095979999571257661109 413165248124959805405729)
            ·
              refine ⟨309873936093719854054297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413165248124959805405729 309873936093719854054297)
              ·
                refine ⟨232405452070289890540723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309873936093719854054297 232405452070289890540723)
                ·
                  refine ⟨348608178105434835811085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232405452070289890540723 348608178105434835811085)
                  ·
                    refine ⟨130728066789538063429157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348608178105434835811085 130728066789538063429157)
                    ·
                      rfl

theorem cell22_381888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_381888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381888 prefixEnd_381888 := by exact prefixLift 381888
  have htrace : WordTrace (prefixWord ++ tailWord_381888) baseStart_381888 baseEnd_381888 := by
    simpa [prefixWord, tailWord_381888, baseEnd_381888] using wordTrace_append hprefix tailTrace_381888
  have hstable : (prefixWord ++ tailWord_381888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381888).length < 2 ^ (prefixWord ++ tailWord_381888).sum := by decide
  have hdescent : baseEnd_381888 < baseStart_381888 := by decide
  rcases family_descends (prefixWord ++ tailWord_381888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381912 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_381912 : Nat := 118140960795 + 381912 * 2 ^ 59
def prefixEnd_381912 : Nat := 4983230072969 + 3 ^ 40 * 381912 * 2
def baseEnd_381912 : Nat := 43578760826670000276361

theorem tailTrace_381912 : CollatzResearch.WordTrace tailWord_381912 prefixEnd_381912 43578760826670000276361 := by
  unfold tailWord_381912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6964737496202762110925995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9286316661603682814567993 6964737496202762110925995)
  ·
    refine ⟨10447106244304143166388993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6964737496202762110925995 10447106244304143166388993)
    ·
      refine ⟨7835329683228107374791745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10447106244304143166388993 7835329683228107374791745)
      ·
        refine ⟨5876497262421080531093809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7835329683228107374791745 5876497262421080531093809)
        ·
          refine ⟨4407372946815810398320357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876497262421080531093809 4407372946815810398320357)
          ·
            refine ⟨826382427527964449685067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4407372946815810398320357 826382427527964449685067)
            ·
              refine ⟨1239573641291946674527601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826382427527964449685067 1239573641291946674527601)
              ·
                refine ⟨929680230968960005895701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239573641291946674527601 929680230968960005895701)
                ·
                  refine ⟨43578760826670000276361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 929680230968960005895701 43578760826670000276361)
                  ·
                    rfl

theorem cell22_381912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_381912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_381912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_381912 prefixEnd_381912 := by exact prefixLift 381912
  have htrace : WordTrace (prefixWord ++ tailWord_381912) baseStart_381912 baseEnd_381912 := by
    simpa [prefixWord, tailWord_381912, baseEnd_381912] using wordTrace_append hprefix tailTrace_381912
  have hstable : (prefixWord ++ tailWord_381912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381912).length < 2 ^ (prefixWord ++ tailWord_381912).sum := by decide
  have hdescent : baseEnd_381912 < baseStart_381912 := by decide
  rcases family_descends (prefixWord ++ tailWord_381912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382002 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_382002 : Nat := 118140960795 + 382002 * 2 ^ 59
def prefixEnd_382002 : Nat := 4983230072969 + 3 ^ 40 * 382002 * 2
def baseEnd_382002 : Nat := 43589030439759922026269

theorem tailTrace_382002 : CollatzResearch.WordTrace tailWord_382002 prefixEnd_382002 43589030439759922026269 := by
  unfold tailWord_382002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483189390519867398157065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9288505041386313061752173 3483189390519867398157065)
  ·
    refine ⟨2612392042889900548617799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3483189390519867398157065 2612392042889900548617799)
    ·
      refine ⟨3918588064334850822926699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612392042889900548617799 3918588064334850822926699)
      ·
        refine ⟨5877882096502276234390049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3918588064334850822926699 5877882096502276234390049)
        ·
          refine ⟨4408411572376707175792537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5877882096502276234390049 4408411572376707175792537)
          ·
            refine ⟨3306308679282530381844403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4408411572376707175792537 3306308679282530381844403)
            ·
              refine ⟨4959463018923795572766605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306308679282530381844403 4959463018923795572766605)
              ·
                refine ⟨1859798632096423339787477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4959463018923795572766605 1859798632096423339787477)
                ·
                  refine ⟨43589030439759922026269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1859798632096423339787477 43589030439759922026269)
                  ·
                    rfl

theorem cell22_382002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_382002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382002 prefixEnd_382002 := by exact prefixLift 382002
  have htrace : WordTrace (prefixWord ++ tailWord_382002) baseStart_382002 baseEnd_382002 := by
    simpa [prefixWord, tailWord_382002, baseEnd_382002] using wordTrace_append hprefix tailTrace_382002
  have hstable : (prefixWord ++ tailWord_382002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382002).length < 2 ^ (prefixWord ++ tailWord_382002).sum := by decide
  have hdescent : baseEnd_382002 < baseStart_382002 := by decide
  rcases family_descends (prefixWord ++ tailWord_382002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382049 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_382049 : Nat := 118140960795 + 382049 * 2 ^ 59
def prefixEnd_382049 : Nat := 4983230072969 + 3 ^ 40 * 382049 * 2
def baseEnd_382049 : Nat := 130783180379787310153663

theorem tailTrace_382049 : CollatzResearch.WordTrace tailWord_382049 prefixEnd_382049 130783180379787310153663 := by
  unfold tailWord_382049
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934471792909196619589201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9289647861939464413059467 13934471792909196619589201)
  ·
    refine ⟨10450853844681897464691901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13934471792909196619589201 10450853844681897464691901)
    ·
      refine ⟨3919070191755711549259463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10450853844681897464691901 3919070191755711549259463)
      ·
        refine ⟨5878605287633567323889195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919070191755711549259463 5878605287633567323889195)
        ·
          refine ⟨8817907931450350985833793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878605287633567323889195 8817907931450350985833793)
          ·
            refine ⟨6613430948587763239375345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8817907931450350985833793 6613430948587763239375345)
            ·
              refine ⟨4960073211440822429531509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613430948587763239375345 4960073211440822429531509)
              ·
                refine ⟨465006863572577102768579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4960073211440822429531509 465006863572577102768579)
                ·
                  refine ⟨697510295358865654152869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465006863572577102768579 697510295358865654152869)
                  ·
                    refine ⟨130783180379787310153663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697510295358865654152869 130783180379787310153663)
                    ·
                      rfl

theorem cell22_382049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_382049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382049 prefixEnd_382049 := by exact prefixLift 382049
  have htrace : WordTrace (prefixWord ++ tailWord_382049) baseStart_382049 baseEnd_382049 := by
    simpa [prefixWord, tailWord_382049, baseEnd_382049] using wordTrace_append hprefix tailTrace_382049
  have hstable : (prefixWord ++ tailWord_382049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382049).length < 2 ^ (prefixWord ++ tailWord_382049).sum := by decide
  have hdescent : baseEnd_382049 < baseStart_382049 := by decide
  rcases family_descends (prefixWord ++ tailWord_382049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382092 : List Nat := [2, 2, 1, 2, 1, 1, 1, 12]
def baseStart_382092 : Nat := 118140960795 + 382092 * 2 ^ 59
def prefixEnd_382092 : Nat := 4983230072969 + 3 ^ 40 * 382092 * 2
def baseEnd_382092 : Nat := 14533100017616614592059

theorem tailTrace_382092 : CollatzResearch.WordTrace tailWord_382092 prefixEnd_382092 14533100017616614592059 := by
  unfold tailWord_382092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6968020065876707481702265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9290693421168943308936353 6968020065876707481702265)
  ·
    refine ⟨5226015049407530611276699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6968020065876707481702265 5226015049407530611276699)
    ·
      refine ⟨7839022574111295916915049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5226015049407530611276699 7839022574111295916915049)
      ·
        refine ⟨5879266930583471937686287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7839022574111295916915049 5879266930583471937686287)
        ·
          refine ⟨8818900395875207906529431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5879266930583471937686287 8818900395875207906529431)
          ·
            refine ⟨13228350593812811859794147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818900395875207906529431 13228350593812811859794147)
            ·
              refine ⟨19842525890719217789691221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13228350593812811859794147 19842525890719217789691221)
              ·
                refine ⟨14533100017616614592059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 19842525890719217789691221 14533100017616614592059)
                ·
                  rfl

theorem cell22_382092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_382092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382092 prefixEnd_382092 := by exact prefixLift 382092
  have htrace : WordTrace (prefixWord ++ tailWord_382092) baseStart_382092 baseEnd_382092 := by
    simpa [prefixWord, tailWord_382092, baseEnd_382092] using wordTrace_append hprefix tailTrace_382092
  have hstable : (prefixWord ++ tailWord_382092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382092).length < 2 ^ (prefixWord ++ tailWord_382092).sum := by decide
  have hdescent : baseEnd_382092 < baseStart_382092 := by decide
  rcases family_descends (prefixWord ++ tailWord_382092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382098 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_382098 : Nat := 118140960795 + 382098 * 2 ^ 59
def prefixEnd_382098 : Nat := 4983230072969 + 3 ^ 40 * 382098 * 2
def baseEnd_382098 : Nat := 43599984693722505226171

theorem tailTrace_382098 : CollatzResearch.WordTrace tailWord_382098 prefixEnd_382098 43599984693722505226171 := by
  unfold tailWord_382098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484064742432919497030737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9290839313154451992081965 3484064742432919497030737)
  ·
    refine ⟨2613048556824689622773053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3484064742432919497030737 2613048556824689622773053)
    ·
      refine ⟨979893208809258608539895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2613048556824689622773053 979893208809258608539895)
      ·
        refine ⟨1469839813213887912809843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979893208809258608539895 1469839813213887912809843)
        ·
          refine ⟨2204759719820831869214765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469839813213887912809843 2204759719820831869214765)
          ·
            refine ⟨826784894932811950955537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2204759719820831869214765 826784894932811950955537)
            ·
              refine ⟨620088671199608963216653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826784894932811950955537 620088671199608963216653)
              ·
                refine ⟨232533251699853361206245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 620088671199608963216653 232533251699853361206245)
                ·
                  refine ⟨43599984693722505226171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232533251699853361206245 43599984693722505226171)
                  ·
                    rfl

theorem cell22_382098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_382098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382098 prefixEnd_382098 := by exact prefixLift 382098
  have htrace : WordTrace (prefixWord ++ tailWord_382098) baseStart_382098 baseEnd_382098 := by
    simpa [prefixWord, tailWord_382098, baseEnd_382098] using wordTrace_append hprefix tailTrace_382098
  have hstable : (prefixWord ++ tailWord_382098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382098).length < 2 ^ (prefixWord ++ tailWord_382098).sum := by decide
  have hdescent : baseEnd_382098 < baseStart_382098 := by decide
  rcases family_descends (prefixWord ++ tailWord_382098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382141 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_382141 : Nat := 118140960795 + 382141 * 2 ^ 59
def prefixEnd_382141 : Nat := 4983230072969 + 3 ^ 40 * 382141 * 2
def baseEnd_382141 : Nat := 130814673859929736853381

theorem tailTrace_382141 : CollatzResearch.WordTrace tailWord_382141 prefixEnd_382141 130814673859929736853381 := by
  unfold tailWord_382141
  simp only [CollatzResearch.WordTrace]
  refine ⟨13937827308575896331938277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9291884872383930887958851 13937827308575896331938277)
  ·
    refine ⟨2613342620357980562238427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13937827308575896331938277 2613342620357980562238427)
    ·
      refine ⟨3920013930536970843357641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2613342620357980562238427 3920013930536970843357641)
      ·
        refine ⟨2940010447902728132518231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3920013930536970843357641 2940010447902728132518231)
        ·
          refine ⟨4410015671854092198777347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940010447902728132518231 4410015671854092198777347)
          ·
            refine ⟨6615023507781138298166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410015671854092198777347 6615023507781138298166021)
            ·
              refine ⟨1240316907708963430906129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6615023507781138298166021 1240316907708963430906129)
              ·
                refine ⟨930237680781722573179597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240316907708963430906129 930237680781722573179597)
                ·
                  refine ⟨348839130293145964942349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930237680781722573179597 348839130293145964942349)
                  ·
                    refine ⟨130814673859929736853381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348839130293145964942349 130814673859929736853381)
                    ·
                      rfl

theorem cell22_382141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_382141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382141 prefixEnd_382141 := by exact prefixLift 382141
  have htrace : WordTrace (prefixWord ++ tailWord_382141) baseStart_382141 baseEnd_382141 := by
    simpa [prefixWord, tailWord_382141, baseEnd_382141] using wordTrace_append hprefix tailTrace_382141
  have hstable : (prefixWord ++ tailWord_382141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382141).length < 2 ^ (prefixWord ++ tailWord_382141).sum := by decide
  have hdescent : baseEnd_382141 < baseStart_382141 := by decide
  rcases family_descends (prefixWord ++ tailWord_382141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382154 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_382154 : Nat := 118140960795 + 382154 * 2 ^ 59
def prefixEnd_382154 : Nat := 4983230072969 + 3 ^ 40 * 382154 * 2
def baseEnd_382154 : Nat := 43606374675200678759447

theorem tailTrace_382154 : CollatzResearch.WordTrace tailWord_382154 prefixEnd_382154 43606374675200678759447 := by
  unfold tailWord_382154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484575364382199888040379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9292200971685866368107677 3484575364382199888040379)
  ·
    refine ⟨5226863046573299832060569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3484575364382199888040379 5226863046573299832060569)
    ·
      refine ⟨3920147284929974874045427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5226863046573299832060569 3920147284929974874045427)
      ·
        refine ⟨5880220927394962311068141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920147284929974874045427 5880220927394962311068141)
        ·
          refine ⟨2205082847773110866650553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5880220927394962311068141 2205082847773110866650553)
          ·
            refine ⟨1653812135829833149987915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205082847773110866650553 1653812135829833149987915)
            ·
              refine ⟨2480718203744749724981873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653812135829833149987915 2480718203744749724981873)
              ·
                refine ⟨1860538652808562293736405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2480718203744749724981873 1860538652808562293736405)
                ·
                  refine ⟨43606374675200678759447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1860538652808562293736405 43606374675200678759447)
                  ·
                    rfl

theorem cell22_382154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_382154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382154 prefixEnd_382154 := by exact prefixLift 382154
  have htrace : WordTrace (prefixWord ++ tailWord_382154) baseStart_382154 baseEnd_382154 := by
    simpa [prefixWord, tailWord_382154, baseEnd_382154] using wordTrace_append hprefix tailTrace_382154
  have hstable : (prefixWord ++ tailWord_382154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382154).length < 2 ^ (prefixWord ++ tailWord_382154).sum := by decide
  have hdescent : baseEnd_382154 < baseStart_382154 := by decide
  rcases family_descends (prefixWord ++ tailWord_382154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382188 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_382188 : Nat := 118140960795 + 382188 * 2 ^ 59
def prefixEnd_382188 : Nat := 4983230072969 + 3 ^ 40 * 382188 * 2
def baseEnd_382188 : Nat := 43610254306812426976079

theorem tailTrace_382188 : CollatzResearch.WordTrace tailWord_382188 prefixEnd_382188 43610254306812426976079 := by
  unfold tailWord_382188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6969770769702811679449609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9293027692937082239266145 6969770769702811679449609)
  ·
    refine ⟨5227328077277108759587207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6969770769702811679449609 5227328077277108759587207)
    ·
      refine ⟨7840992115915663139380811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5227328077277108759587207 7840992115915663139380811)
      ·
        refine ⟨11761488173873494709071217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7840992115915663139380811 11761488173873494709071217)
        ·
          refine ⟨8821116130405121031803413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11761488173873494709071217 8821116130405121031803413)
          ·
            refine ⟨413489818612740048365785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8821116130405121031803413 413489818612740048365785)
            ·
              refine ⟨310117363959555036274339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413489818612740048365785 310117363959555036274339)
              ·
                refine ⟨465176045939332554411509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310117363959555036274339 465176045939332554411509)
                ·
                  refine ⟨43610254306812426976079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465176045939332554411509 43610254306812426976079)
                  ·
                    rfl

theorem cell22_382188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_382188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382188 prefixEnd_382188 := by exact prefixLift 382188
  have htrace : WordTrace (prefixWord ++ tailWord_382188) baseStart_382188 baseEnd_382188 := by
    simpa [prefixWord, tailWord_382188, baseEnd_382188] using wordTrace_append hprefix tailTrace_382188
  have hstable : (prefixWord ++ tailWord_382188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382188).length < 2 ^ (prefixWord ++ tailWord_382188).sum := by decide
  have hdescent : baseEnd_382188 < baseStart_382188 := by decide
  rcases family_descends (prefixWord ++ tailWord_382188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382226 : List Nat := [3, 2, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_382226 : Nat := 118140960795 + 382226 * 2 ^ 59
def prefixEnd_382226 : Nat := 4983230072969 + 3 ^ 40 * 382226 * 2
def baseEnd_382226 : Nat := 130843771097017848478121

theorem tailTrace_382226 : CollatzResearch.WordTrace tailWord_382226 prefixEnd_382226 130843771097017848478121 := by
  unfold tailWord_382226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3485231878316988962195633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9293951675511970565855021 3485231878316988962195633)
  ·
    refine ⟨2613923908737741721646725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3485231878316988962195633 2613923908737741721646725)
    ·
      refine ⟨490110732888326572808761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2613923908737741721646725 490110732888326572808761)
      ·
        refine ⟨367583049666244929606571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490110732888326572808761 367583049666244929606571)
        ·
          refine ⟨551374574499367394409857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367583049666244929606571 551374574499367394409857)
          ·
            refine ⟨413530930874525545807393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551374574499367394409857 413530930874525545807393)
            ·
              refine ⟨310148198155894159355545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413530930874525545807393 310148198155894159355545)
              ·
                refine ⟨232611148616920619516659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310148198155894159355545 232611148616920619516659)
                ·
                  refine ⟨348916722925380929274989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232611148616920619516659 348916722925380929274989)
                  ·
                    refine ⟨130843771097017848478121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348916722925380929274989 130843771097017848478121)
                    ·
                      rfl

theorem cell22_382226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_382226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382226 prefixEnd_382226 := by exact prefixLift 382226
  have htrace : WordTrace (prefixWord ++ tailWord_382226) baseStart_382226 baseEnd_382226 := by
    simpa [prefixWord, tailWord_382226, baseEnd_382226] using wordTrace_append hprefix tailTrace_382226
  have hstable : (prefixWord ++ tailWord_382226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382226).length < 2 ^ (prefixWord ++ tailWord_382226).sum := by decide
  have hdescent : baseEnd_382226 < baseStart_382226 := by decide
  rcases family_descends (prefixWord ++ tailWord_382226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382229 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_382229 : Nat := 118140960795 + 382229 * 2 ^ 59
def prefixEnd_382229 : Nat := 4983230072969 + 3 ^ 40 * 382229 * 2
def baseEnd_382229 : Nat := 130844798058326840653111

theorem tailTrace_382229 : CollatzResearch.WordTrace tailWord_382229 prefixEnd_382229 130844798058326840653111 := by
  unfold tailWord_382229
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941036932257087361141741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9294024621504724907427827 13941036932257087361141741)
  ·
    refine ⟨5227888849596407760428153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13941036932257087361141741 5227888849596407760428153)
    ·
      refine ⟨3920916637197305820321115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5227888849596407760428153 3920916637197305820321115)
      ·
        refine ⟨5881374955795958730481673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3920916637197305820321115 5881374955795958730481673)
        ·
          refine ⟨4411031216846969047861255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881374955795958730481673 4411031216846969047861255)
          ·
            refine ⟨6616546825270453571791883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411031216846969047861255 6616546825270453571791883)
            ·
              refine ⟨9924820237905680357687825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616546825270453571791883 9924820237905680357687825)
              ·
                refine ⟨7443615178429260268265869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9924820237905680357687825 7443615178429260268265869)
                ·
                  refine ⟨2791355691910972600599701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7443615178429260268265869 2791355691910972600599701)
                  ·
                    refine ⟨130844798058326840653111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2791355691910972600599701 130844798058326840653111)
                    ·
                      rfl

theorem cell22_382229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_382229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382229 prefixEnd_382229 := by exact prefixLift 382229
  have htrace : WordTrace (prefixWord ++ tailWord_382229) baseStart_382229 baseEnd_382229 := by
    simpa [prefixWord, tailWord_382229, baseEnd_382229] using wordTrace_append hprefix tailTrace_382229
  have hstable : (prefixWord ++ tailWord_382229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382229).length < 2 ^ (prefixWord ++ tailWord_382229).sum := by decide
  have hdescent : baseEnd_382229 < baseStart_382229 := by decide
  rcases family_descends (prefixWord ++ tailWord_382229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382248 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_382248 : Nat := 118140960795 + 382248 * 2 ^ 59
def prefixEnd_382248 : Nat := 4983230072969 + 3 ^ 40 * 382248 * 2
def baseEnd_382248 : Nat := 130851302146617124428053

theorem tailTrace_382248 : CollatzResearch.WordTrace tailWord_382248 prefixEnd_382248 130851302146617124428053 := by
  unfold tailWord_382248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970864959594126803041699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9294486612792169070722265 6970864959594126803041699)
  ·
    refine ⟨10456297439391190204562549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6970864959594126803041699 10456297439391190204562549)
    ·
      refine ⟨980277884942924081677739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10456297439391190204562549 980277884942924081677739)
      ·
        refine ⟨1470416827414386122516609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980277884942924081677739 1470416827414386122516609)
        ·
          refine ⟨1102812620560789591887457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470416827414386122516609 1102812620560789591887457)
          ·
            refine ⟨827109465420592193915593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102812620560789591887457 827109465420592193915593)
            ·
              refine ⟨620332099065444145436695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827109465420592193915593 620332099065444145436695)
              ·
                refine ⟨930498148598166218155043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620332099065444145436695 930498148598166218155043)
                ·
                  refine ⟨1395747222897249327232565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930498148598166218155043 1395747222897249327232565)
                  ·
                    refine ⟨130851302146617124428053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1395747222897249327232565 130851302146617124428053)
                    ·
                      rfl

theorem cell22_382248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_382248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382248 prefixEnd_382248 := by exact prefixLift 382248
  have htrace : WordTrace (prefixWord ++ tailWord_382248) baseStart_382248 baseEnd_382248 := by
    simpa [prefixWord, tailWord_382248, baseEnd_382248] using wordTrace_append hprefix tailTrace_382248
  have hstable : (prefixWord ++ tailWord_382248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382248).length < 2 ^ (prefixWord ++ tailWord_382248).sum := by decide
  have hdescent : baseEnd_382248 < baseStart_382248 := by decide
  rcases family_descends (prefixWord ++ tailWord_382248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382269 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_382269 : Nat := 118140960795 + 382269 * 2 ^ 59
def prefixEnd_382269 : Nat := 4983230072969 + 3 ^ 40 * 382269 * 2
def baseEnd_382269 : Nat := 130858490875780069652989

theorem tailTrace_382269 : CollatzResearch.WordTrace tailWord_382269 prefixEnd_382269 130858490875780069652989 := by
  unfold tailWord_382269
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942495852112174192597861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9294997234741449461731907 13942495852112174192597861)
  ·
    refine ⟨2614217972271032661112099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13942495852112174192597861 2614217972271032661112099)
    ·
      refine ⟨3921326958406548991668149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614217972271032661112099 3921326958406548991668149)
      ·
        refine ⟨367624402350613967968889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3921326958406548991668149 367624402350613967968889)
        ·
          refine ⟨275718301762960475976667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367624402350613967968889 275718301762960475976667)
          ·
            refine ⟨413577452644440713965001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275718301762960475976667 413577452644440713965001)
            ·
              refine ⟨310183089483330535473751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413577452644440713965001 310183089483330535473751)
              ·
                refine ⟨465274634224995803210627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310183089483330535473751 465274634224995803210627)
                ·
                  refine ⟨697911951337493704815941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465274634224995803210627 697911951337493704815941)
                  ·
                    refine ⟨130858490875780069652989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697911951337493704815941 130858490875780069652989)
                    ·
                      rfl

theorem cell22_382269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_382269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382269 prefixEnd_382269 := by exact prefixLift 382269
  have htrace : WordTrace (prefixWord ++ tailWord_382269) baseStart_382269 baseEnd_382269 := by
    simpa [prefixWord, tailWord_382269, baseEnd_382269] using wordTrace_append hprefix tailTrace_382269
  have hstable : (prefixWord ++ tailWord_382269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382269).length < 2 ^ (prefixWord ++ tailWord_382269).sum := by decide
  have hdescent : baseEnd_382269 < baseStart_382269 := by decide
  rcases family_descends (prefixWord ++ tailWord_382269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382293 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_382293 : Nat := 118140960795 + 382293 * 2 ^ 59
def prefixEnd_382293 : Nat := 4983230072969 + 3 ^ 40 * 382293 * 2
def baseEnd_382293 : Nat := 130866706566252007052915

theorem tailTrace_382293 : CollatzResearch.WordTrace tailWord_382293 prefixEnd_382293 130866706566252007052915 := by
  unfold tailWord_382293
  simp only [CollatzResearch.WordTrace]
  refine ⟨13943371204025226291471533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9295580802683484194314355 13943371204025226291471533)
  ·
    refine ⟨5228764201509459859301825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13943371204025226291471533 5228764201509459859301825)
    ·
      refine ⟨3921573151132094894476369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5228764201509459859301825 3921573151132094894476369)
      ·
        refine ⟨2941179863349071170857277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3921573151132094894476369 2941179863349071170857277)
        ·
          refine ⟨1102942448755901689071479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2941179863349071170857277 1102942448755901689071479)
          ·
            refine ⟨1654413673133852533607219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102942448755901689071479 1654413673133852533607219)
            ·
              refine ⟨2481620509700778800410829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654413673133852533607219 2481620509700778800410829)
              ·
                refine ⟨930607691137792050154061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2481620509700778800410829 930607691137792050154061)
                ·
                  refine ⟨348977884176672018807773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930607691137792050154061 348977884176672018807773)
                  ·
                    refine ⟨130866706566252007052915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348977884176672018807773 130866706566252007052915)
                    ·
                      rfl

theorem cell22_382293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_382293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382293 prefixEnd_382293 := by exact prefixLift 382293
  have htrace : WordTrace (prefixWord ++ tailWord_382293) baseStart_382293 baseEnd_382293 := by
    simpa [prefixWord, tailWord_382293, baseEnd_382293] using wordTrace_append hprefix tailTrace_382293
  have hstable : (prefixWord ++ tailWord_382293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382293).length < 2 ^ (prefixWord ++ tailWord_382293).sum := by decide
  have hdescent : baseEnd_382293 < baseStart_382293 := by decide
  rcases family_descends (prefixWord ++ tailWord_382293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382370 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_382370 : Nat := 118140960795 + 382370 * 2 ^ 59
def prefixEnd_382370 : Nat := 4983230072969 + 3 ^ 40 * 382370 * 2
def baseEnd_382370 : Nat := 130893065239849472877679

theorem tailTrace_382370 : CollatzResearch.WordTrace tailWord_382370 prefixEnd_382370 130893065239849472877679 := by
  unfold tailWord_382370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486544906186567110506141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9297453083164178961349709 3486544906186567110506141)
  ·
    refine ⟨1307454339819962666439803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3486544906186567110506141 1307454339819962666439803)
    ·
      refine ⟨1961181509729943999659705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307454339819962666439803 1961181509729943999659705)
      ·
        refine ⟨1470886132297457999744779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1961181509729943999659705 1470886132297457999744779)
        ·
          refine ⟨2206329198446186999617169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470886132297457999744779 2206329198446186999617169)
          ·
            refine ⟨1654746898834640249712877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206329198446186999617169 1654746898834640249712877)
            ·
              refine ⟨620530087062990093642329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1654746898834640249712877 620530087062990093642329)
              ·
                refine ⟨465397565297242570231747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620530087062990093642329 465397565297242570231747)
                ·
                  refine ⟨698096347945863855347621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465397565297242570231747 698096347945863855347621)
                  ·
                    refine ⟨130893065239849472877679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698096347945863855347621 130893065239849472877679)
                    ·
                      rfl

theorem cell22_382370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_382370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382370 prefixEnd_382370 := by exact prefixLift 382370
  have htrace : WordTrace (prefixWord ++ tailWord_382370) baseStart_382370 baseEnd_382370 := by
    simpa [prefixWord, tailWord_382370, baseEnd_382370] using wordTrace_append hprefix tailTrace_382370
  have hstable : (prefixWord ++ tailWord_382370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382370).length < 2 ^ (prefixWord ++ tailWord_382370).sum := by decide
  have hdescent : baseEnd_382370 < baseStart_382370 := by decide
  rcases family_descends (prefixWord ++ tailWord_382370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382396 : List Nat := [2, 2, 2, 4, 12]
def baseStart_382396 : Nat := 118140960795 + 382396 * 2 ^ 59
def prefixEnd_382396 : Nat := 4983230072969 + 3 ^ 40 * 382396 * 2
def baseEnd_382396 : Nat := 538691216342362435093

theorem tailTrace_382396 : CollatzResearch.WordTrace tailWord_382396 prefixEnd_382396 538691216342362435093 := by
  unfold tailWord_382396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973563961326037441235521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9298085281768049921647361 6973563961326037441235521)
  ·
    refine ⟨5230172970994528080926641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6973563961326037441235521 5230172970994528080926641)
    ·
      refine ⟨3922629728245896060694981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5230172970994528080926641 3922629728245896060694981)
      ·
        refine ⟨735493074046105511380309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3922629728245896060694981 735493074046105511380309)
        ·
          refine ⟨538691216342362435093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 735493074046105511380309 538691216342362435093)
          ·
            rfl

theorem cell22_382396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 12].length) (baseStart_382396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382396 prefixEnd_382396 := by exact prefixLift 382396
  have htrace : WordTrace (prefixWord ++ tailWord_382396) baseStart_382396 baseEnd_382396 := by
    simpa [prefixWord, tailWord_382396, baseEnd_382396] using wordTrace_append hprefix tailTrace_382396
  have hstable : (prefixWord ++ tailWord_382396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382396).length < 2 ^ (prefixWord ++ tailWord_382396).sum := by decide
  have hdescent : baseEnd_382396 < baseStart_382396 := by decide
  rcases family_descends (prefixWord ++ tailWord_382396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382520 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 6]
def baseStart_382520 : Nat := 118140960795 + 382520 * 2 ^ 59
def prefixEnd_382520 : Nat := 4983230072969 + 3 ^ 40 * 382520 * 2
def baseEnd_382520 : Nat := 43648137768433027209073

theorem tailTrace_382520 : CollatzResearch.WordTrace tailWord_382520 prefixEnd_382520 43648137768433027209073 := by
  unfold tailWord_382520
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975825287101422029992507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9301100382801896039990009 6975825287101422029992507)
  ·
    refine ⟨10463737930652133044988761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6975825287101422029992507 10463737930652133044988761)
    ·
      refine ⟨7847803447989099783741571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10463737930652133044988761 7847803447989099783741571)
      ·
        refine ⟨11771705171983649675612357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847803447989099783741571 11771705171983649675612357)
        ·
          refine ⟨2207194719746934314177317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11771705171983649675612357 2207194719746934314177317)
          ·
            refine ⟨413849009952550183908247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2207194719746934314177317 413849009952550183908247)
            ·
              refine ⟨620773514928825275862371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413849009952550183908247 620773514928825275862371)
              ·
                refine ⟨931160272393237913793557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620773514928825275862371 931160272393237913793557)
                ·
                  refine ⟨43648137768433027209073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 931160272393237913793557 43648137768433027209073)
                  ·
                    rfl

theorem cell22_382520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 6].length) (baseStart_382520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382520 prefixEnd_382520 := by exact prefixLift 382520
  have htrace : WordTrace (prefixWord ++ tailWord_382520) baseStart_382520 baseEnd_382520 := by
    simpa [prefixWord, tailWord_382520, baseEnd_382520] using wordTrace_append hprefix tailTrace_382520
  have hstable : (prefixWord ++ tailWord_382520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382520).length < 2 ^ (prefixWord ++ tailWord_382520).sum := by decide
  have hdescent : baseEnd_382520 < baseStart_382520 := by decide
  rcases family_descends (prefixWord ++ tailWord_382520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382533 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_382533 : Nat := 118140960795 + 382533 * 2 ^ 59
def prefixEnd_382533 : Nat := 4983230072969 + 3 ^ 40 * 382533 * 2
def baseEnd_382533 : Nat := 130948863470971381052179

theorem tailTrace_382533 : CollatzResearch.WordTrace tailWord_382533 prefixEnd_382533 130948863470971381052179 := by
  unfold tailWord_382533
  simp only [CollatzResearch.WordTrace]
  refine ⟨13952124723155747280208253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9301416482103831520138835 13952124723155747280208253)
  ·
    refine ⟨5232046771183405230078095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13952124723155747280208253 5232046771183405230078095)
    ·
      refine ⟨7848070156775107845117143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5232046771183405230078095 7848070156775107845117143)
      ·
        refine ⟨11772105235162661767675715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7848070156775107845117143 11772105235162661767675715)
        ·
          refine ⟨17658157852743992651513573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11772105235162661767675715 17658157852743992651513573)
          ·
            refine ⟨3310904597389498622158795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17658157852743992651513573 3310904597389498622158795)
            ·
              refine ⟨4966356896084247933238193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310904597389498622158795 4966356896084247933238193)
              ·
                refine ⟨3724767672063185949928645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4966356896084247933238193 3724767672063185949928645)
                ·
                  refine ⟨698393938511847365611621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3724767672063185949928645 698393938511847365611621)
                  ·
                    refine ⟨130948863470971381052179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698393938511847365611621 130948863470971381052179)
                    ·
                      rfl

theorem cell22_382533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_382533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382533 prefixEnd_382533 := by exact prefixLift 382533
  have htrace : WordTrace (prefixWord ++ tailWord_382533) baseStart_382533 baseEnd_382533 := by
    simpa [prefixWord, tailWord_382533, baseEnd_382533] using wordTrace_append hprefix tailTrace_382533
  have hstable : (prefixWord ++ tailWord_382533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382533).length < 2 ^ (prefixWord ++ tailWord_382533).sum := by decide
  have hdescent : baseEnd_382533 < baseStart_382533 := by decide
  rcases family_descends (prefixWord ++ tailWord_382533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382548 : List Nat := [2, 4, 1, 1, 1, 2, 1, 10]
def baseStart_382548 : Nat := 118140960795 + 382548 * 2 ^ 59
def prefixEnd_382548 : Nat := 4983230072969 + 3 ^ 40 * 382548 * 2
def baseEnd_382548 : Nat := 14550444253057371325237

theorem tailTrace_382548 : CollatzResearch.WordTrace tailWord_382548 prefixEnd_382548 14550444253057371325237 := by
  unfold tailWord_382548
  simp only [CollatzResearch.WordTrace]
  refine ⟨6976335909050702421002149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9301781212067603228002865 6976335909050702421002149)
  ·
    refine ⟨1308062982947006703937903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6976335909050702421002149 1308062982947006703937903)
    ·
      refine ⟨1962094474420510055906855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308062982947006703937903 1962094474420510055906855)
      ·
        refine ⟨2943141711630765083860283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962094474420510055906855 2943141711630765083860283)
        ·
          refine ⟨4414712567446147625790425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943141711630765083860283 4414712567446147625790425)
          ·
            refine ⟨3311034425584610719342819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414712567446147625790425 3311034425584610719342819)
            ·
              refine ⟨4966551638376916079014229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3311034425584610719342819 4966551638376916079014229)
              ·
                refine ⟨14550444253057371325237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4966551638376916079014229 14550444253057371325237)
                ·
                  rfl

theorem cell22_382548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_382548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382548 prefixEnd_382548 := by exact prefixLift 382548
  have htrace : WordTrace (prefixWord ++ tailWord_382548) baseStart_382548 baseEnd_382548 := by
    simpa [prefixWord, tailWord_382548, baseEnd_382548] using wordTrace_append hprefix tailTrace_382548
  have hstable : (prefixWord ++ tailWord_382548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382548).length < 2 ^ (prefixWord ++ tailWord_382548).sum := by decide
  have hdescent : baseEnd_382548 < baseStart_382548 := by decide
  rcases family_descends (prefixWord ++ tailWord_382548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382582 : List Nat := [5, 1, 1, 2, 2, 3, 1, 7]
def baseStart_382582 : Nat := 118140960795 + 382582 * 2 ^ 59
def prefixEnd_382582 : Nat := 4983230072969 + 3 ^ 40 * 382582 * 2
def baseEnd_382582 : Nat := 14551737463594620730781

theorem tailTrace_382582 : CollatzResearch.WordTrace tailWord_382582 prefixEnd_382582 14551737463594620730781 := by
  unfold tailWord_382582
  simp only [CollatzResearch.WordTrace]
  refine ⟨872119493748639290546375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9302607933318819099161333 872119493748639290546375)
  ·
    refine ⟨1308179240622958935819563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872119493748639290546375 1308179240622958935819563)
    ·
      refine ⟨1962268860934438403729345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308179240622958935819563 1962268860934438403729345)
      ·
        refine ⟨1471701645700828802797009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1962268860934438403729345 1471701645700828802797009)
        ·
          refine ⟨1103776234275621602097757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471701645700828802797009 1103776234275621602097757)
          ·
            refine ⟨413916087853358100786659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103776234275621602097757 413916087853358100786659)
            ·
              refine ⟨620874131780037151179989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413916087853358100786659 620874131780037151179989)
              ·
                refine ⟨14551737463594620730781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 620874131780037151179989 14551737463594620730781)
                ·
                  rfl

theorem cell22_382582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_382582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382582 prefixEnd_382582 := by exact prefixLift 382582
  have htrace : WordTrace (prefixWord ++ tailWord_382582) baseStart_382582 baseEnd_382582 := by
    simpa [prefixWord, tailWord_382582, baseEnd_382582] using wordTrace_append hprefix tailTrace_382582
  have hstable : (prefixWord ++ tailWord_382582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382582).length < 2 ^ (prefixWord ++ tailWord_382582).sum := by decide
  have hdescent : baseEnd_382582 < baseStart_382582 := by decide
  rcases family_descends (prefixWord ++ tailWord_382582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382625 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_382625 : Nat := 118140960795 + 382625 * 2 ^ 59
def prefixEnd_382625 : Nat := 4983230072969 + 3 ^ 40 * 382625 * 2
def baseEnd_382625 : Nat := 130980356951113807751897

theorem tailTrace_382625 : CollatzResearch.WordTrace tailWord_382625 prefixEnd_382625 130980356951113807751897 := by
  unfold tailWord_382625
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955480238822446992557329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9303653492548297995038219 13955480238822446992557329)
  ·
    refine ⟨10466610179116835244417997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13955480238822446992557329 10466610179116835244417997)
    ·
      refine ⟨3924978817168813216656749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10466610179116835244417997 3924978817168813216656749)
      ·
        refine ⟨1471867056438304956246281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3924978817168813216656749 1471867056438304956246281)
        ·
          refine ⟨1103900292328728717184711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471867056438304956246281 1103900292328728717184711)
          ·
            refine ⟨1655850438493093075777067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103900292328728717184711 1655850438493093075777067)
            ·
              refine ⟨2483775657739639613665601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655850438493093075777067 2483775657739639613665601)
              ·
                refine ⟨1862831743304729710249201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483775657739639613665601 1862831743304729710249201)
                ·
                  refine ⟨1397123807478547282686901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862831743304729710249201 1397123807478547282686901)
                  ·
                    refine ⟨130980356951113807751897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1397123807478547282686901 130980356951113807751897)
                    ·
                      rfl

theorem cell22_382625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_382625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382625 prefixEnd_382625 := by exact prefixLift 382625
  have htrace : WordTrace (prefixWord ++ tailWord_382625) baseStart_382625 baseEnd_382625 := by
    simpa [prefixWord, tailWord_382625, baseEnd_382625] using wordTrace_append hprefix tailTrace_382625
  have hstable : (prefixWord ++ tailWord_382625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382625).length < 2 ^ (prefixWord ++ tailWord_382625).sum := by decide
  have hdescent : baseEnd_382625 < baseStart_382625 := by decide
  rcases family_descends (prefixWord ++ tailWord_382625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382670 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_382670 : Nat := 118140960795 + 382670 * 2 ^ 59
def prefixEnd_382670 : Nat := 4983230072969 + 3 ^ 40 * 382670 * 2
def baseEnd_382670 : Nat := 130995761370748690376759

theorem tailTrace_382670 : CollatzResearch.WordTrace tailWord_382670 prefixEnd_382670 130995761370748690376759 := by
  unfold tailWord_382670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1744640190457427459743183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9304747682439613118630309 1744640190457427459743183)
  ·
    refine ⟨2616960285686141189614775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1744640190457427459743183 2616960285686141189614775)
    ·
      refine ⟨3925440428529211784422163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2616960285686141189614775 3925440428529211784422163)
      ·
        refine ⟨5888160642793817676633245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925440428529211784422163 5888160642793817676633245)
        ·
          refine ⟨2208060241047681628737467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5888160642793817676633245 2208060241047681628737467)
          ·
            refine ⟨3312090361571522443106201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208060241047681628737467 3312090361571522443106201)
            ·
              refine ⟨2484067771178641832329651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3312090361571522443106201 2484067771178641832329651)
              ·
                refine ⟨3726101656767962748494477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484067771178641832329651 3726101656767962748494477)
                ·
                  refine ⟨1397288121287986030685429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3726101656767962748494477 1397288121287986030685429)
                  ·
                    refine ⟨130995761370748690376759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1397288121287986030685429 130995761370748690376759)
                    ·
                      rfl

theorem cell22_382670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_382670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382670 prefixEnd_382670 := by exact prefixLift 382670
  have htrace : WordTrace (prefixWord ++ tailWord_382670) baseStart_382670 baseEnd_382670 := by
    simpa [prefixWord, tailWord_382670, baseEnd_382670] using wordTrace_append hprefix tailTrace_382670
  have hstable : (prefixWord ++ tailWord_382670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382670).length < 2 ^ (prefixWord ++ tailWord_382670).sum := by decide
  have hdescent : baseEnd_382670 < baseStart_382670 := by decide
  rcases family_descends (prefixWord ++ tailWord_382670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382687 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 2, 3]
def baseStart_382687 : Nat := 118140960795 + 382687 * 2 ^ 59
def prefixEnd_382687 : Nat := 4983230072969 + 3 ^ 40 * 382687 * 2
def baseEnd_382687 : Nat := 131001580818166312701707

theorem tailTrace_382687 : CollatzResearch.WordTrace tailWord_382687 prefixEnd_382687 131001580818166312701707 := by
  unfold tailWord_382687
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957741564597831581314315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9305161043065221054209543 13957741564597831581314315)
  ·
    refine ⟨20936612346896747371971473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13957741564597831581314315 20936612346896747371971473)
    ·
      refine ⟨15702459260172560528978605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20936612346896747371971473 15702459260172560528978605)
      ·
        refine ⟨5888422222564710198366977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15702459260172560528978605 5888422222564710198366977)
        ·
          refine ⟨4416316666923532648775233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5888422222564710198366977 4416316666923532648775233)
          ·
            refine ⟨3312237500192649486581425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4416316666923532648775233 3312237500192649486581425)
            ·
              refine ⟨2484178125144487114936069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3312237500192649486581425 2484178125144487114936069)
              ·
                refine ⟨465783398464591334050513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2484178125144487114936069 465783398464591334050513)
                ·
                  refine ⟨349337548848443500537885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465783398464591334050513 349337548848443500537885)
                  ·
                    refine ⟨131001580818166312701707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349337548848443500537885 131001580818166312701707)
                    ·
                      rfl

theorem cell22_382687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_382687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382687 prefixEnd_382687 := by exact prefixLift 382687
  have htrace : WordTrace (prefixWord ++ tailWord_382687) baseStart_382687 baseEnd_382687 := by
    simpa [prefixWord, tailWord_382687, baseEnd_382687] using wordTrace_append hprefix tailTrace_382687
  have hstable : (prefixWord ++ tailWord_382687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382687).length < 2 ^ (prefixWord ++ tailWord_382687).sum := by decide
  have hdescent : baseEnd_382687 < baseStart_382687 := by decide
  rcases family_descends (prefixWord ++ tailWord_382687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382689 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 6]
def baseStart_382689 : Nat := 118140960795 + 382689 * 2 ^ 59
def prefixEnd_382689 : Nat := 4983230072969 + 3 ^ 40 * 382689 * 2
def baseEnd_382689 : Nat := 43667421819679658050567

theorem tailTrace_382689 : CollatzResearch.WordTrace tailWord_382689 prefixEnd_382689 43667421819679658050567 := by
  unfold tailWord_382689
  simp only [CollatzResearch.WordTrace]
  refine ⟨13957814510590585922887121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9305209673727057281924747 13957814510590585922887121)
  ·
    refine ⟨10468360882942939442165341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13957814510590585922887121 10468360882942939442165341)
    ·
      refine ⟨3925635331103602290812003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10468360882942939442165341 3925635331103602290812003)
      ·
        refine ⟨5888452996655403436218005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925635331103602290812003 5888452996655403436218005)
        ·
          refine ⟨276021234218222036072719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5888452996655403436218005 276021234218222036072719)
          ·
            refine ⟨414031851327333054109079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276021234218222036072719 414031851327333054109079)
            ·
              refine ⟨621047776990999581163619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414031851327333054109079 621047776990999581163619)
              ·
                refine ⟨931571665486499371745429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621047776990999581163619 931571665486499371745429)
                ·
                  refine ⟨43667421819679658050567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 931571665486499371745429 43667421819679658050567)
                  ·
                    rfl

theorem cell22_382689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_382689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382689 prefixEnd_382689 := by exact prefixLift 382689
  have htrace : WordTrace (prefixWord ++ tailWord_382689) baseStart_382689 baseEnd_382689 := by
    simpa [prefixWord, tailWord_382689, baseEnd_382689] using wordTrace_append hprefix tailTrace_382689
  have hstable : (prefixWord ++ tailWord_382689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382689).length < 2 ^ (prefixWord ++ tailWord_382689).sum := by decide
  have hdescent : baseEnd_382689 < baseStart_382689 := by decide
  rcases family_descends (prefixWord ++ tailWord_382689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382708 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_382708 : Nat := 118140960795 + 382708 * 2 ^ 59
def prefixEnd_382708 : Nat := 4983230072969 + 3 ^ 40 * 382708 * 2
def baseEnd_382708 : Nat := 131008769547329257926643

theorem tailTrace_382708 : CollatzResearch.WordTrace tailWord_382708 prefixEnd_382708 131008769547329257926643 := by
  unfold tailWord_382708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979253748760876083914389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9305671665014501445219185 6979253748760876083914389)
  ·
    refine ⟨327152519473166066433487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6979253748760876083914389 327152519473166066433487)
    ·
      refine ⟨490728779209749099650231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327152519473166066433487 490728779209749099650231)
      ·
        refine ⟨736093168814623649475347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490728779209749099650231 736093168814623649475347)
        ·
          refine ⟨1104139753221935474213021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736093168814623649475347 1104139753221935474213021)
          ·
            refine ⟨414052407458225802829883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1104139753221935474213021 414052407458225802829883)
            ·
              refine ⟨621078611187338704244825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414052407458225802829883 621078611187338704244825)
              ·
                refine ⟨465808958390504028183619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621078611187338704244825 465808958390504028183619)
                ·
                  refine ⟨698713437585756042275429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465808958390504028183619 698713437585756042275429)
                  ·
                    refine ⟨131008769547329257926643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 698713437585756042275429 131008769547329257926643)
                    ·
                      rfl

theorem cell22_382708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_382708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382708 prefixEnd_382708 := by exact prefixLift 382708
  have htrace : WordTrace (prefixWord ++ tailWord_382708) baseStart_382708 baseEnd_382708 := by
    simpa [prefixWord, tailWord_382708, baseEnd_382708] using wordTrace_append hprefix tailTrace_382708
  have hstable : (prefixWord ++ tailWord_382708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382708).length < 2 ^ (prefixWord ++ tailWord_382708).sum := by decide
  have hdescent : baseEnd_382708 < baseStart_382708 := by decide
  rcases family_descends (prefixWord ++ tailWord_382708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382766 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 3, 3]
def baseStart_382766 : Nat := 118140960795 + 382766 * 2 ^ 59
def prefixEnd_382766 : Nat := 4983230072969 + 3 ^ 40 * 382766 * 2
def baseEnd_382766 : Nat := 131028624132636439976465

theorem tailTrace_382766 : CollatzResearch.WordTrace tailWord_382766 prefixEnd_382766 131028624132636439976465 := by
  unfold tailWord_382766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745077866413953509180019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9307081954207752048960101 1745077866413953509180019)
  ·
    refine ⟨2617616799620930263770029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745077866413953509180019 2617616799620930263770029)
    ·
      refine ⟨981606299857848848913761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2617616799620930263770029 981606299857848848913761)
      ·
        refine ⟨736204724893386636685321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 981606299857848848913761 736204724893386636685321)
        ·
          refine ⟨552153543670039977513991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736204724893386636685321 552153543670039977513991)
          ·
            refine ⟨828230315505059966270987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552153543670039977513991 828230315505059966270987)
            ·
              refine ⟨1242345473257589949406481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828230315505059966270987 1242345473257589949406481)
              ·
                refine ⟨931759104943192462054861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242345473257589949406481 931759104943192462054861)
                ·
                  refine ⟨349409664353697173270573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931759104943192462054861 349409664353697173270573)
                  ·
                    refine ⟨131028624132636439976465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349409664353697173270573 131028624132636439976465)
                    ·
                      rfl

theorem cell22_382766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_382766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382766 prefixEnd_382766 := by exact prefixLift 382766
  have htrace : WordTrace (prefixWord ++ tailWord_382766) baseStart_382766 baseEnd_382766 := by
    simpa [prefixWord, tailWord_382766, baseEnd_382766] using wordTrace_append hprefix tailTrace_382766
  have hstable : (prefixWord ++ tailWord_382766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382766).length < 2 ^ (prefixWord ++ tailWord_382766).sum := by decide
  have hdescent : baseEnd_382766 < baseStart_382766 := by decide
  rcases family_descends (prefixWord ++ tailWord_382766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382796 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 5]
def baseStart_382796 : Nat := 118140960795 + 382796 * 2 ^ 59
def prefixEnd_382796 : Nat := 4983230072969 + 3 ^ 40 * 382796 * 2
def baseEnd_382796 : Nat := 43679631248575453908791

theorem tailTrace_382796 : CollatzResearch.WordTrace tailWord_382796 prefixEnd_382796 43679631248575453908791 := by
  unfold tailWord_382796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980858560601471598516121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9307811414135295464688161 6980858560601471598516121)
  ·
    refine ⟨5235643920451103698887091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6980858560601471598516121 5235643920451103698887091)
    ·
      refine ⟨7853465880676655548330637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235643920451103698887091 7853465880676655548330637)
      ·
        refine ⟨2945049705253745830623989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7853465880676655548330637 2945049705253745830623989)
        ·
          refine ⟨276098409867538671620999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2945049705253745830623989 276098409867538671620999)
          ·
            refine ⟨414147614801308007431499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276098409867538671620999 414147614801308007431499)
            ·
              refine ⟨621221422201962011147249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414147614801308007431499 621221422201962011147249)
              ·
                refine ⟨465916066651471508360437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621221422201962011147249 465916066651471508360437)
                ·
                  refine ⟨43679631248575453908791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 465916066651471508360437 43679631248575453908791)
                  ·
                    rfl

theorem cell22_382796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_382796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382796 prefixEnd_382796 := by exact prefixLift 382796
  have htrace : WordTrace (prefixWord ++ tailWord_382796) baseStart_382796 baseEnd_382796 := by
    simpa [prefixWord, tailWord_382796, baseEnd_382796] using wordTrace_append hprefix tailTrace_382796
  have hstable : (prefixWord ++ tailWord_382796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382796).length < 2 ^ (prefixWord ++ tailWord_382796).sum := by decide
  have hdescent : baseEnd_382796 < baseStart_382796 := by decide
  rcases family_descends (prefixWord ++ tailWord_382796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382837 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_382837 : Nat := 118140960795 + 382837 * 2 ^ 59
def prefixEnd_382837 : Nat := 4983230072969 + 3 ^ 40 * 382837 * 2
def baseEnd_382837 : Nat := 131052928883615921451247

theorem tailTrace_382837 : CollatzResearch.WordTrace tailWord_382837 prefixEnd_382837 131052928883615921451247 := by
  unfold tailWord_382837
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963212514054407199274765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9308808342702938132849843 13963212514054407199274765)
  ·
    refine ⟨5236204692770402699728037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13963212514054407199274765 5236204692770402699728037)
    ·
      refine ⟨981788379894450506199007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5236204692770402699728037 981788379894450506199007)
      ·
        refine ⟨1472682569841675759298511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981788379894450506199007 1472682569841675759298511)
        ·
          refine ⟨2209023854762513638947767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472682569841675759298511 2209023854762513638947767)
          ·
            refine ⟨3313535782143770458421651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209023854762513638947767 3313535782143770458421651)
            ·
              refine ⟨4970303673215655687632477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313535782143770458421651 4970303673215655687632477)
              ·
                refine ⟨1863863877455870882862179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4970303673215655687632477 1863863877455870882862179)
                ·
                  refine ⟨2795795816183806324293269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863863877455870882862179 2795795816183806324293269)
                  ·
                    refine ⟨131052928883615921451247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2795795816183806324293269 131052928883615921451247)
                    ·
                      rfl

theorem cell22_382837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_382837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382837 prefixEnd_382837 := by exact prefixLift 382837
  have htrace : WordTrace (prefixWord ++ tailWord_382837) baseStart_382837 baseEnd_382837 := by
    simpa [prefixWord, tailWord_382837, baseEnd_382837] using wordTrace_append hprefix tailTrace_382837
  have hstable : (prefixWord ++ tailWord_382837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382837).length < 2 ^ (prefixWord ++ tailWord_382837).sum := by decide
  have hdescent : baseEnd_382837 < baseStart_382837 := by decide
  rcases family_descends (prefixWord ++ tailWord_382837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382858 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_382858 : Nat := 118140960795 + 382858 * 2 ^ 59
def prefixEnd_382858 : Nat := 4983230072969 + 3 ^ 40 * 382858 * 2
def baseEnd_382858 : Nat := 43686705870926288892061

theorem tailTrace_382858 : CollatzResearch.WordTrace tailWord_382858 prefixEnd_382858 43686705870926288892061 := by
  unfold tailWord_382858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490994611744581946447307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9309318964652218523859485 3490994611744581946447307)
  ·
    refine ⟨5236491917616872919670961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3490994611744581946447307 5236491917616872919670961)
    ·
      refine ⟨3927368938212654689753221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5236491917616872919670961 3927368938212654689753221)
      ·
        refine ⟨736381675914872754328729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3927368938212654689753221 736381675914872754328729)
        ·
          refine ⟨552286256936154565746547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736381675914872754328729 552286256936154565746547)
          ·
            refine ⟨828429385404231848619821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552286256936154565746547 828429385404231848619821)
            ·
              refine ⟨310661019526586943232433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828429385404231848619821 310661019526586943232433)
              ·
                refine ⟨232995764644940207424325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310661019526586943232433 232995764644940207424325)
                ·
                  refine ⟨43686705870926288892061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 232995764644940207424325 43686705870926288892061)
                  ·
                    rfl

theorem cell22_382858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_382858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382858 prefixEnd_382858 := by exact prefixLift 382858
  have htrace : WordTrace (prefixWord ++ tailWord_382858) baseStart_382858 baseEnd_382858 := by
    simpa [prefixWord, tailWord_382858, baseEnd_382858] using wordTrace_append hprefix tailTrace_382858
  have hstable : (prefixWord ++ tailWord_382858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382858).length < 2 ^ (prefixWord ++ tailWord_382858).sum := by decide
  have hdescent : baseEnd_382858 < baseStart_382858 := by decide
  rcases family_descends (prefixWord ++ tailWord_382858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382888 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 2, 4]
def baseStart_382888 : Nat := 118140960795 + 382888 * 2 ^ 59
def prefixEnd_382888 : Nat := 4983230072969 + 3 ^ 40 * 382888 * 2
def baseEnd_382888 : Nat := 131070387225868788426091

theorem tailTrace_382888 : CollatzResearch.WordTrace tailWord_382888 prefixEnd_382888 131070387225868788426091 := by
  unfold tailWord_382888
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982536318434821454690659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9310048424579761939587545 6982536318434821454690659)
  ·
    refine ⟨10473804477652232182035989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982536318434821454690659 10473804477652232182035989)
    ·
      refine ⟨490959584889948383532937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10473804477652232182035989 490959584889948383532937)
      ·
        refine ⟨368219688667461287649703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490959584889948383532937 368219688667461287649703)
        ·
          refine ⟨552329533001191931474555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368219688667461287649703 552329533001191931474555)
          ·
            refine ⟨828494299501787897211833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552329533001191931474555 828494299501787897211833)
            ·
              refine ⟨621370724626340922908875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828494299501787897211833 621370724626340922908875)
              ·
                refine ⟨932056086939511384363313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621370724626340922908875 932056086939511384363313)
                ·
                  refine ⟨699042065204633538272485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932056086939511384363313 699042065204633538272485)
                  ·
                    refine ⟨131070387225868788426091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699042065204633538272485 131070387225868788426091)
                    ·
                      rfl

theorem cell22_382888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_382888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382888 prefixEnd_382888 := by exact prefixLift 382888
  have htrace : WordTrace (prefixWord ++ tailWord_382888) baseStart_382888 baseEnd_382888 := by
    simpa [prefixWord, tailWord_382888, baseEnd_382888] using wordTrace_append hprefix tailTrace_382888
  have hstable : (prefixWord ++ tailWord_382888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382888).length < 2 ^ (prefixWord ++ tailWord_382888).sum := by decide
  have hdescent : baseEnd_382888 < baseStart_382888 := by decide
  rcases family_descends (prefixWord ++ tailWord_382888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382912 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_382912 : Nat := 118140960795 + 382912 * 2 ^ 59
def prefixEnd_382912 : Nat := 4983230072969 + 3 ^ 40 * 382912 * 2
def baseEnd_382912 : Nat := 131078602916340725826017

theorem tailTrace_382912 : CollatzResearch.WordTrace tailWord_382912 prefixEnd_382912 131078602916340725826017 := by
  unfold tailWord_382912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982973994391347504127495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9310631992521796672169993 6982973994391347504127495)
  ·
    refine ⟨10474460991587021256191243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6982973994391347504127495 10474460991587021256191243)
    ·
      refine ⟨15711691487380531884286865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10474460991587021256191243 15711691487380531884286865)
      ·
        refine ⟨11783768615535398913215149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15711691487380531884286865 11783768615535398913215149)
        ·
          refine ⟨4418913230825774592455681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11783768615535398913215149 4418913230825774592455681)
          ·
            refine ⟨3314184923119330944341761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4418913230825774592455681 3314184923119330944341761)
            ·
              refine ⟨2485638692339498208256321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314184923119330944341761 2485638692339498208256321)
              ·
                refine ⟨1864229019254623656192241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485638692339498208256321 1864229019254623656192241)
                ·
                  refine ⟨1398171764440967742144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864229019254623656192241 1398171764440967742144181)
                  ·
                    refine ⟨131078602916340725826017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1398171764440967742144181 131078602916340725826017)
                    ·
                      rfl

theorem cell22_382912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_382912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382912 prefixEnd_382912 := by exact prefixLift 382912
  have htrace : WordTrace (prefixWord ++ tailWord_382912) baseStart_382912 baseEnd_382912 := by
    simpa [prefixWord, tailWord_382912, baseEnd_382912] using wordTrace_append hprefix tailTrace_382912
  have hstable : (prefixWord ++ tailWord_382912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382912).length < 2 ^ (prefixWord ++ tailWord_382912).sum := by decide
  have hdescent : baseEnd_382912 < baseStart_382912 := by decide
  rcases family_descends (prefixWord ++ tailWord_382912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382927 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_382927 : Nat := 118140960795 + 382927 * 2 ^ 59
def prefixEnd_382927 : Nat := 4983230072969 + 3 ^ 40 * 382927 * 2
def baseEnd_382927 : Nat := 131083737722885686700971

theorem tailTrace_382927 : CollatzResearch.WordTrace tailWord_382927 prefixEnd_382927 131083737722885686700971 := by
  unfold tailWord_382927
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966495083728352570051035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9310996722485568380034023 13966495083728352570051035)
  ·
    refine ⟨20949742625592528855076553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13966495083728352570051035 20949742625592528855076553)
    ·
      refine ⟨15712306969194396641307415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20949742625592528855076553 15712306969194396641307415)
      ·
        refine ⟨23568460453791594961961123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15712306969194396641307415 23568460453791594961961123)
        ·
          refine ⟨35352690680687392442941685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23568460453791594961961123 35352690680687392442941685)
          ·
            refine ⟨3314314751314443041525783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35352690680687392442941685 3314314751314443041525783)
            ·
              refine ⟨4971472126971664562288675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314314751314443041525783 4971472126971664562288675)
              ·
                refine ⟨7457208190457496843433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971472126971664562288675 7457208190457496843433013)
                ·
                  refine ⟨699113267855390329071845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7457208190457496843433013 699113267855390329071845)
                  ·
                    refine ⟨131083737722885686700971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699113267855390329071845 131083737722885686700971)
                    ·
                      rfl

theorem cell22_382927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_382927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382927 prefixEnd_382927 := by exact prefixLift 382927
  have htrace : WordTrace (prefixWord ++ tailWord_382927) baseStart_382927 baseEnd_382927 := by
    simpa [prefixWord, tailWord_382927, baseEnd_382927] using wordTrace_append hprefix tailTrace_382927
  have hstable : (prefixWord ++ tailWord_382927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382927).length < 2 ^ (prefixWord ++ tailWord_382927).sum := by decide
  have hdescent : baseEnd_382927 < baseStart_382927 := by decide
  rcases family_descends (prefixWord ++ tailWord_382927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382961 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_382961 : Nat := 118140960795 + 382961 * 2 ^ 59
def prefixEnd_382961 : Nat := 4983230072969 + 3 ^ 40 * 382961 * 2
def baseEnd_382961 : Nat := 131095376617720931350867

theorem tailTrace_382961 : CollatzResearch.WordTrace tailWord_382961 prefixEnd_382961 131095376617720931350867 := by
  unfold tailWord_382961
  simp only [CollatzResearch.WordTrace]
  refine ⟨13967735165605176376788737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9311823443736784251192491 13967735165605176376788737)
  ·
    refine ⟨10475801374203882282591553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13967735165605176376788737 10475801374203882282591553)
    ·
      refine ⟨7856851030652911711943665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10475801374203882282591553 7856851030652911711943665)
      ·
        refine ⟨5892638272989683783957749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7856851030652911711943665 5892638272989683783957749)
        ·
          refine ⟨552434838092782854746039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5892638272989683783957749 552434838092782854746039)
          ·
            refine ⟨828652257139174282119059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552434838092782854746039 828652257139174282119059)
            ·
              refine ⟨1242978385708761423178589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828652257139174282119059 1242978385708761423178589)
              ·
                refine ⟨466116894640785533691971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1242978385708761423178589 466116894640785533691971)
                ·
                  refine ⟨699175341961178300537957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466116894640785533691971 699175341961178300537957)
                  ·
                    refine ⟨131095376617720931350867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699175341961178300537957 131095376617720931350867)
                    ·
                      rfl

theorem cell22_382961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_382961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382961 prefixEnd_382961 := by exact prefixLift 382961
  have htrace : WordTrace (prefixWord ++ tailWord_382961) baseStart_382961 baseEnd_382961 := by
    simpa [prefixWord, tailWord_382961, baseEnd_382961] using wordTrace_append hprefix tailTrace_382961
  have hstable : (prefixWord ++ tailWord_382961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382961).length < 2 ^ (prefixWord ++ tailWord_382961).sum := by decide
  have hdescent : baseEnd_382961 < baseStart_382961 := by decide
  rcases family_descends (prefixWord ++ tailWord_382961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382987 : List Nat := [1, 1, 1, 1, 6, 1, 2, 9]
def baseStart_382987 : Nat := 118140960795 + 382987 * 2 ^ 59
def prefixEnd_382987 : Nat := 4983230072969 + 3 ^ 40 * 382987 * 2
def baseEnd_382987 : Nat := 14567141883229503355643

theorem tailTrace_382987 : CollatzResearch.WordTrace tailWord_382987 prefixEnd_382987 14567141883229503355643 := by
  unfold tailWord_382987
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968683463510982817235215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9312455642340655211490143 13968683463510982817235215)
  ·
    refine ⟨20953025195266474225852823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13968683463510982817235215 20953025195266474225852823)
    ·
      refine ⟨31429537792899711338779235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20953025195266474225852823 31429537792899711338779235)
      ·
        refine ⟨47144306689349567008168853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31429537792899711338779235 47144306689349567008168853)
        ·
          refine ⟨2209889376063260953507915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47144306689349567008168853 2209889376063260953507915)
          ·
            refine ⟨3314834064094891430261873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209889376063260953507915 3314834064094891430261873)
            ·
              refine ⟨2486125548071168572696405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314834064094891430261873 2486125548071168572696405)
              ·
                refine ⟨14567141883229503355643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2486125548071168572696405 14567141883229503355643)
                ·
                  rfl

theorem cell22_382987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 9].length) (baseStart_382987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_382987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_382987 prefixEnd_382987 := by exact prefixLift 382987
  have htrace : WordTrace (prefixWord ++ tailWord_382987) baseStart_382987 baseEnd_382987 := by
    simpa [prefixWord, tailWord_382987, baseEnd_382987] using wordTrace_append hprefix tailTrace_382987
  have hstable : (prefixWord ++ tailWord_382987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382987).length < 2 ^ (prefixWord ++ tailWord_382987).sum := by decide
  have hdescent : baseEnd_382987 < baseStart_382987 := by decide
  rcases family_descends (prefixWord ++ tailWord_382987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383004 : List Nat := [2, 2, 3, 1, 3, 2, 1, 8]
def baseStart_383004 : Nat := 118140960795 + 383004 * 2 ^ 59
def prefixEnd_383004 : Nat := 4983230072969 + 3 ^ 40 * 383004 * 2
def baseEnd_383004 : Nat := 14567788488498128058415

theorem tailTrace_383004 : CollatzResearch.WordTrace tailWord_383004 prefixEnd_383004 14567788488498128058415 := by
  unfold tailWord_383004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984651752224697360302033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9312869002966263147069377 6984651752224697360302033)
  ·
    refine ⟨5238488814168523020226525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6984651752224697360302033 5238488814168523020226525)
    ·
      refine ⟨1964433305313196132584947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5238488814168523020226525 1964433305313196132584947)
      ·
        refine ⟨2946649957969794198877421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964433305313196132584947 2946649957969794198877421)
        ·
          refine ⟨1104993734238672824579033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946649957969794198877421 1104993734238672824579033)
          ·
            refine ⟨828745300679004618434275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1104993734238672824579033 828745300679004618434275)
            ·
              refine ⟨1243117951018506927651413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828745300679004618434275 1243117951018506927651413)
              ·
                refine ⟨14567788488498128058415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1243117951018506927651413 14567788488498128058415)
                ·
                  rfl

theorem cell22_383004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_383004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383004 prefixEnd_383004 := by exact prefixLift 383004
  have htrace : WordTrace (prefixWord ++ tailWord_383004) baseStart_383004 baseEnd_383004 := by
    simpa [prefixWord, tailWord_383004, baseEnd_383004] using wordTrace_append hprefix tailTrace_383004
  have hstable : (prefixWord ++ tailWord_383004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383004).length < 2 ^ (prefixWord ++ tailWord_383004).sum := by decide
  have hdescent : baseEnd_383004 < baseStart_383004 := by decide
  rcases family_descends (prefixWord ++ tailWord_383004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383049 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 5]
def baseStart_383049 : Nat := 118140960795 + 383049 * 2 ^ 59
def prefixEnd_383049 : Nat := 4983230072969 + 3 ^ 40 * 383049 * 2
def baseEnd_383049 : Nat := 43708500272039345050199

theorem tailTrace_383049 : CollatzResearch.WordTrace tailWord_383049 prefixEnd_383049 43708500272039345050199 := by
  unfold tailWord_383049
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970944789286367405992201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9313963192857578270661467 13970944789286367405992201)
  ·
    refine ⟨10478208591964775554494151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13970944789286367405992201 10478208591964775554494151)
    ·
      refine ⟨15717312887947163331741227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10478208591964775554494151 15717312887947163331741227)
      ·
        refine ⟨23575969331920744997611841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15717312887947163331741227 23575969331920744997611841)
        ·
          refine ⟨17681976998940558748208881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23575969331920744997611841 17681976998940558748208881)
          ·
            refine ⟨13261482749205419061156661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681976998940558748208881 13261482749205419061156661)
            ·
              refine ⟨1243264007738008036983437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13261482749205419061156661 1243264007738008036983437)
              ·
                refine ⟨466224002901753013868789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1243264007738008036983437 466224002901753013868789)
                ·
                  refine ⟨43708500272039345050199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466224002901753013868789 43708500272039345050199)
                  ·
                    rfl

theorem cell22_383049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_383049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383049 prefixEnd_383049 := by exact prefixLift 383049
  have htrace : WordTrace (prefixWord ++ tailWord_383049) baseStart_383049 baseEnd_383049 := by
    simpa [prefixWord, tailWord_383049, baseEnd_383049] using wordTrace_append hprefix tailTrace_383049
  have hstable : (prefixWord ++ tailWord_383049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383049).length < 2 ^ (prefixWord ++ tailWord_383049).sum := by decide
  have hdescent : baseEnd_383049 < baseStart_383049 := by decide
  rcases family_descends (prefixWord ++ tailWord_383049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383201 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 5]
def baseStart_383201 : Nat := 118140960795 + 383201 * 2 ^ 59
def prefixEnd_383201 : Nat := 4983230072969 + 3 ^ 40 * 383201 * 2
def baseEnd_383201 : Nat := 43725844507480101783377

theorem tailTrace_383201 : CollatzResearch.WordTrace tailWord_383201 prefixEnd_383201 43725844507480101783377 := by
  unfold tailWord_383201
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976488684735697365525457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9317659123157131577016971 13976488684735697365525457)
  ·
    refine ⟨10482366513551773024144093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13976488684735697365525457 10482366513551773024144093)
    ·
      refine ⟨3930887442581914884054035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10482366513551773024144093 3930887442581914884054035)
      ·
        refine ⟨5896331163872872326081053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3930887442581914884054035 5896331163872872326081053)
        ·
          refine ⟨2211124186452327122280395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5896331163872872326081053 2211124186452327122280395)
          ·
            refine ⟨3316686279678490683420593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2211124186452327122280395 3316686279678490683420593)
            ·
              refine ⟨2487514709758868012565445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316686279678490683420593 2487514709758868012565445)
              ·
                refine ⟨466409008079787752356021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2487514709758868012565445 466409008079787752356021)
                ·
                  refine ⟨43725844507480101783377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466409008079787752356021 43725844507480101783377)
                  ·
                    rfl

theorem cell22_383201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_383201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383201 prefixEnd_383201 := by exact prefixLift 383201
  have htrace : WordTrace (prefixWord ++ tailWord_383201) baseStart_383201 baseEnd_383201 := by
    simpa [prefixWord, tailWord_383201, baseEnd_383201] using wordTrace_append hprefix tailTrace_383201
  have hstable : (prefixWord ++ tailWord_383201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383201).length < 2 ^ (prefixWord ++ tailWord_383201).sum := by decide
  have hdescent : baseEnd_383201 < baseStart_383201 := by decide
  rcases family_descends (prefixWord ++ tailWord_383201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383205 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_383205 : Nat := 118140960795 + 383205 * 2 ^ 59
def prefixEnd_383205 : Nat := 4983230072969 + 3 ^ 40 * 383205 * 2
def baseEnd_383205 : Nat := 131178902804185628250119

theorem tailTrace_383205 : CollatzResearch.WordTrace tailWord_383205 prefixEnd_383205 131178902804185628250119 := by
  unfold tailWord_383205
  simp only [CollatzResearch.WordTrace]
  refine ⟨13976634576721206048671069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9317756384480804032447379 13976634576721206048671069)
  ·
    refine ⟨5241237966270452268251651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13976634576721206048671069 5241237966270452268251651)
    ·
      refine ⟨7861856949405678402377477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241237966270452268251651 7861856949405678402377477)
      ·
        refine ⟨1474098178013564700445777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7861856949405678402377477 1474098178013564700445777)
        ·
          refine ⟨1105573633510173525334333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474098178013564700445777 1105573633510173525334333)
          ·
            refine ⟨414590112566315072000375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105573633510173525334333 414590112566315072000375)
            ·
              refine ⟨621885168849472608000563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414590112566315072000375 621885168849472608000563)
              ·
                refine ⟨932827753274208912000845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621885168849472608000563 932827753274208912000845)
                ·
                  refine ⟨349810407477828342000317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 932827753274208912000845 349810407477828342000317)
                  ·
                    refine ⟨131178902804185628250119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349810407477828342000317 131178902804185628250119)
                    ·
                      rfl

theorem cell22_383205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_383205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383205 prefixEnd_383205 := by exact prefixLift 383205
  have htrace : WordTrace (prefixWord ++ tailWord_383205) baseStart_383205 baseEnd_383205 := by
    simpa [prefixWord, tailWord_383205, baseEnd_383205] using wordTrace_append hprefix tailTrace_383205
  have hstable : (prefixWord ++ tailWord_383205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383205).length < 2 ^ (prefixWord ++ tailWord_383205).sum := by decide
  have hdescent : baseEnd_383205 < baseStart_383205 := by decide
  rcases family_descends (prefixWord ++ tailWord_383205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383218 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_383218 : Nat := 118140960795 + 383218 * 2 ^ 59
def prefixEnd_383218 : Nat := 4983230072969 + 3 ^ 40 * 383218 * 2
def baseEnd_383218 : Nat := 43727784323285975891693

theorem tailTrace_383218 : CollatzResearch.WordTrace tailWord_383218 prefixEnd_383218 43727784323285975891693 := by
  unfold tailWord_383218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494277181418527317223577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9318072483782739512596205 3494277181418527317223577)
  ·
    refine ⟨2620707886063895487917683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3494277181418527317223577 2620707886063895487917683)
    ·
      refine ⟨3931061829095843231876525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620707886063895487917683 3931061829095843231876525)
      ·
        refine ⟨1474148185910941211953697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3931061829095843231876525 1474148185910941211953697)
        ·
          refine ⟨1105611139433205908965273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474148185910941211953697 1105611139433205908965273)
          ·
            refine ⟨829208354574904431723955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105611139433205908965273 829208354574904431723955)
            ·
              refine ⟨1243812531862356647585933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829208354574904431723955 1243812531862356647585933)
              ·
                refine ⟨466429699448383742844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1243812531862356647585933 466429699448383742844725)
                ·
                  refine ⟨43727784323285975891693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466429699448383742844725 43727784323285975891693)
                  ·
                    rfl

theorem cell22_383218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_383218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383218 prefixEnd_383218 := by exact prefixLift 383218
  have htrace : WordTrace (prefixWord ++ tailWord_383218) baseStart_383218 baseEnd_383218 := by
    simpa [prefixWord, tailWord_383218, baseEnd_383218] using wordTrace_append hprefix tailTrace_383218
  have hstable : (prefixWord ++ tailWord_383218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383218).length < 2 ^ (prefixWord ++ tailWord_383218).sum := by decide
  have hdescent : baseEnd_383218 < baseStart_383218 := by decide
  rcases family_descends (prefixWord ++ tailWord_383218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383231 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_383231 : Nat := 118140960795 + 383231 * 2 ^ 59
def prefixEnd_383231 : Nat := 4983230072969 + 3 ^ 40 * 383231 * 2
def baseEnd_383231 : Nat := 131187803135530227100039

theorem tailTrace_383231 : CollatzResearch.WordTrace tailWord_383231 prefixEnd_383231 131187803135530227100039 := by
  unfold tailWord_383231
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977582874627012489117547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9318388583084674992745031 13977582874627012489117547)
  ·
    refine ⟨20966374311940518733676321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13977582874627012489117547 20966374311940518733676321)
    ·
      refine ⟨15724780733955389050257241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20966374311940518733676321 15724780733955389050257241)
      ·
        refine ⟨11793585550466541787692931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15724780733955389050257241 11793585550466541787692931)
        ·
          refine ⟨17690378325699812681539397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11793585550466541787692931 17690378325699812681539397)
          ·
            refine ⟨3316945936068714877788637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17690378325699812681539397 3316945936068714877788637)
            ·
              refine ⟨1243854726025768079170739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3316945936068714877788637 1243854726025768079170739)
              ·
                refine ⟨1865782089038652118756109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243854726025768079170739 1865782089038652118756109)
                ·
                  refine ⟨699668283389494544533541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1865782089038652118756109 699668283389494544533541)
                  ·
                    refine ⟨131187803135530227100039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699668283389494544533541 131187803135530227100039)
                    ·
                      rfl

theorem cell22_383231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_383231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383231 prefixEnd_383231 := by exact prefixLift 383231
  have htrace : WordTrace (prefixWord ++ tailWord_383231) baseStart_383231 baseEnd_383231 := by
    simpa [prefixWord, tailWord_383231, baseEnd_383231] using wordTrace_append hprefix tailTrace_383231
  have hstable : (prefixWord ++ tailWord_383231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383231).length < 2 ^ (prefixWord ++ tailWord_383231).sum := by decide
  have hdescent : baseEnd_383231 < baseStart_383231 := by decide
  rcases family_descends (prefixWord ++ tailWord_383231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383276 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_383276 : Nat := 118140960795 + 383276 * 2 ^ 59
def prefixEnd_383276 : Nat := 4983230072969 + 3 ^ 40 * 383276 * 2
def baseEnd_383276 : Nat := 131203207555165109724901

theorem tailTrace_383276 : CollatzResearch.WordTrace tailWord_383276 prefixEnd_383276 131203207555165109724901 := by
  unfold tailWord_383276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989612079731992587252841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9319482772975990116337121 6989612079731992587252841)
  ·
    refine ⟨5242209059798994440439631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6989612079731992587252841 5242209059798994440439631)
    ·
      refine ⟨7863313589698491660659447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5242209059798994440439631 7863313589698491660659447)
      ·
        refine ⟨11794970384547737490989171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863313589698491660659447 11794970384547737490989171)
        ·
          refine ⟨17692455576821606236483757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11794970384547737490989171 17692455576821606236483757)
          ·
            refine ⟨6634670841308102338681409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17692455576821606236483757 6634670841308102338681409)
            ·
              refine ⟨4976003130981076754011057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634670841308102338681409 4976003130981076754011057)
              ·
                refine ⟨3732002348235807565508293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4976003130981076754011057 3732002348235807565508293)
                ·
                  refine ⟨699750440294213918532805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3732002348235807565508293 699750440294213918532805)
                  ·
                    refine ⟨131203207555165109724901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699750440294213918532805 131203207555165109724901)
                    ·
                      rfl

theorem cell22_383276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_383276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383276 prefixEnd_383276 := by exact prefixLift 383276
  have htrace : WordTrace (prefixWord ++ tailWord_383276) baseStart_383276 baseEnd_383276 := by
    simpa [prefixWord, tailWord_383276, baseEnd_383276] using wordTrace_append hprefix tailTrace_383276
  have hstable : (prefixWord ++ tailWord_383276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383276).length < 2 ^ (prefixWord ++ tailWord_383276).sum := by decide
  have hdescent : baseEnd_383276 < baseStart_383276 := by decide
  rcases family_descends (prefixWord ++ tailWord_383276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383297 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 4]
def baseStart_383297 : Nat := 118140960795 + 383297 * 2 ^ 59
def prefixEnd_383297 : Nat := 4983230072969 + 3 ^ 40 * 383297 * 2
def baseEnd_383297 : Nat := 43736798761442684983279

theorem tailTrace_383297 : CollatzResearch.WordTrace tailWord_383297 prefixEnd_383297 43736798761442684983279 := by
  unfold tailWord_383297
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979990092387905761020145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9319993394925270507346763 13979990092387905761020145)
  ·
    refine ⟨10484992569290929320765109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13979990092387905761020145 10484992569290929320765109)
    ·
      refine ⟨982968053371024623821729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10484992569290929320765109 982968053371024623821729)
      ·
        refine ⟨737226040028268467866297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982968053371024623821729 737226040028268467866297)
        ·
          refine ⟨552919530021201350899723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737226040028268467866297 552919530021201350899723)
          ·
            refine ⟨829379295031802026349585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552919530021201350899723 829379295031802026349585)
            ·
              refine ⟨622034471273851519762189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829379295031802026349585 622034471273851519762189)
              ·
                refine ⟨233262926727694319910821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622034471273851519762189 233262926727694319910821)
                ·
                  refine ⟨43736798761442684983279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233262926727694319910821 43736798761442684983279)
                  ·
                    rfl

theorem cell22_383297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_383297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383297 prefixEnd_383297 := by exact prefixLift 383297
  have htrace : WordTrace (prefixWord ++ tailWord_383297) baseStart_383297 baseEnd_383297 := by
    simpa [prefixWord, tailWord_383297, baseEnd_383297] using wordTrace_append hprefix tailTrace_383297
  have hstable : (prefixWord ++ tailWord_383297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383297).length < 2 ^ (prefixWord ++ tailWord_383297).sum := by decide
  have hdescent : baseEnd_383297 < baseStart_383297 := by decide
  rcases family_descends (prefixWord ++ tailWord_383297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383351 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_383351 : Nat := 118140960795 + 383351 * 2 ^ 59
def prefixEnd_383351 : Nat := 4983230072969 + 3 ^ 40 * 383351 * 2
def baseEnd_383351 : Nat := 131228881587889914099671

theorem tailTrace_383351 : CollatzResearch.WordTrace tailWord_383351 prefixEnd_383351 131228881587889914099671 := by
  unfold tailWord_383351
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981959634192272983485907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321306422794848655657271 13981959634192272983485907)
  ·
    refine ⟨20972939451288409475228861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13981959634192272983485907 20972939451288409475228861)
    ·
      refine ⟨7864852294233153553210823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20972939451288409475228861 7864852294233153553210823)
      ·
        refine ⟨11797278441349730329816235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7864852294233153553210823 11797278441349730329816235)
        ·
          refine ⟨17695917662024595494724353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11797278441349730329816235 17695917662024595494724353)
          ·
            refine ⟨13271938246518446621043265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17695917662024595494724353 13271938246518446621043265)
            ·
              refine ⟨9953953684888834965782449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13271938246518446621043265 9953953684888834965782449)
              ·
                refine ⟨7465465263666626224336837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9953953684888834965782449 7465465263666626224336837)
                ·
                  refine ⟨1399774736937492417063157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7465465263666626224336837 1399774736937492417063157)
                  ·
                    refine ⟨131228881587889914099671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1399774736937492417063157 131228881587889914099671)
                    ·
                      rfl

theorem cell22_383351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_383351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383351 prefixEnd_383351 := by exact prefixLift 383351
  have htrace : WordTrace (prefixWord ++ tailWord_383351) baseStart_383351 baseEnd_383351 := by
    simpa [prefixWord, tailWord_383351, baseEnd_383351] using wordTrace_append hprefix tailTrace_383351
  have hstable : (prefixWord ++ tailWord_383351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383351).length < 2 ^ (prefixWord ++ tailWord_383351).sum := by decide
  have hdescent : baseEnd_383351 < baseStart_383351 := by decide
  rcases family_descends (prefixWord ++ tailWord_383351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383357 : List Nat := [1, 4, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_383357 : Nat := 118140960795 + 383357 * 2 ^ 59
def prefixEnd_383357 : Nat := 4983230072969 + 3 ^ 40 * 383357 * 2
def baseEnd_383357 : Nat := 131230935510507898449653

theorem tailTrace_383357 : CollatzResearch.WordTrace tailWord_383357 prefixEnd_383357 131230935510507898449653 := by
  unfold tailWord_383357
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982178472170536008204325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321452314780357338802883 13982178472170536008204325)
  ·
    refine ⟨2621658463531975501538311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13982178472170536008204325 2621658463531975501538311)
    ·
      refine ⟨3932487695297963252307467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621658463531975501538311 3932487695297963252307467)
      ·
        refine ⟨5898731542946944878461201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932487695297963252307467 5898731542946944878461201)
        ·
          refine ⟨4424048657210208658845901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5898731542946944878461201 4424048657210208658845901)
          ·
            refine ⟨1659018246453828247067213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4424048657210208658845901 1659018246453828247067213)
            ·
              refine ⟨622131842420185592650205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1659018246453828247067213 622131842420185592650205)
              ·
                refine ⟨233299440907569597243827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622131842420185592650205 233299440907569597243827)
                ·
                  refine ⟨349949161361354395865741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233299440907569597243827 349949161361354395865741)
                  ·
                    refine ⟨131230935510507898449653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349949161361354395865741 131230935510507898449653)
                    ·
                      rfl

theorem cell22_383357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_383357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383357 prefixEnd_383357 := by exact prefixLift 383357
  have htrace : WordTrace (prefixWord ++ tailWord_383357) baseStart_383357 baseEnd_383357 := by
    simpa [prefixWord, tailWord_383357, baseEnd_383357] using wordTrace_append hprefix tailTrace_383357
  have hstable : (prefixWord ++ tailWord_383357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383357).length < 2 ^ (prefixWord ++ tailWord_383357).sum := by decide
  have hdescent : baseEnd_383357 < baseStart_383357 := by decide
  rcases family_descends (prefixWord ++ tailWord_383357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383417 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_383417 : Nat := 118140960795 + 383417 * 2 ^ 59
def prefixEnd_383417 : Nat := 4983230072969 + 3 ^ 40 * 383417 * 2
def baseEnd_383417 : Nat := 131251474736687741949469

theorem tailTrace_383417 : CollatzResearch.WordTrace tailWord_383417 prefixEnd_383417 131251474736687741949469 := by
  unfold tailWord_383417
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984366851953166255388505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9322911234635444170259003 13984366851953166255388505)
  ·
    refine ⟨10488275138964874691541379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13984366851953166255388505 10488275138964874691541379)
    ·
      refine ⟨15732412708447312037312069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10488275138964874691541379 15732412708447312037312069)
      ·
        refine ⟨2949827382833871006996013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15732412708447312037312069 2949827382833871006996013)
        ·
          refine ⟨1106185268562701627623505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2949827382833871006996013 1106185268562701627623505)
          ·
            refine ⟨829638951422026220717629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106185268562701627623505 829638951422026220717629)
            ·
              refine ⟨311114606783259832769111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829638951422026220717629 311114606783259832769111)
              ·
                refine ⟨466671910174889749153667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311114606783259832769111 466671910174889749153667)
                ·
                  refine ⟨700007865262334623730501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466671910174889749153667 700007865262334623730501)
                  ·
                    refine ⟨131251474736687741949469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700007865262334623730501 131251474736687741949469)
                    ·
                      rfl

theorem cell22_383417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_383417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383417 prefixEnd_383417 := by exact prefixLift 383417
  have htrace : WordTrace (prefixWord ++ tailWord_383417) baseStart_383417 baseEnd_383417 := by
    simpa [prefixWord, tailWord_383417, baseEnd_383417] using wordTrace_append hprefix tailTrace_383417
  have hstable : (prefixWord ++ tailWord_383417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383417).length < 2 ^ (prefixWord ++ tailWord_383417).sum := by decide
  have hdescent : baseEnd_383417 < baseStart_383417 := by decide
  rcases family_descends (prefixWord ++ tailWord_383417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383425 : List Nat := [1, 2, 7, 1, 1, 2, 2, 2, 1, 3]
def baseStart_383425 : Nat := 118140960795 + 383425 * 2 ^ 59
def prefixEnd_383425 : Nat := 4983230072969 + 3 ^ 40 * 383425 * 2
def baseEnd_383425 : Nat := 131254213300178387749445

theorem tailTrace_383425 : CollatzResearch.WordTrace tailWord_383425 prefixEnd_383425 131254213300178387749445 := by
  unfold tailWord_383425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984658635924183621679729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9323105757282789081119819 13984658635924183621679729)
  ·
    refine ⟨10488493976943137716259797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13984658635924183621679729 10488493976943137716259797)
    ·
      refine ⟨245824077584604790224839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10488493976943137716259797 245824077584604790224839)
      ·
        refine ⟨368736116376907185337259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245824077584604790224839 368736116376907185337259)
        ·
          refine ⟨553104174565360778005889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368736116376907185337259 553104174565360778005889)
          ·
            refine ⟨414828130924020583504417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553104174565360778005889 414828130924020583504417)
            ·
              refine ⟨311121098193015437628313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414828130924020583504417 311121098193015437628313)
              ·
                refine ⟨233340823644761578221235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311121098193015437628313 233340823644761578221235)
                ·
                  refine ⟨350011235467142367331853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233340823644761578221235 350011235467142367331853)
                  ·
                    refine ⟨131254213300178387749445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350011235467142367331853 131254213300178387749445)
                    ·
                      rfl

theorem cell22_383425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_383425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383425 prefixEnd_383425 := by exact prefixLift 383425
  have htrace : WordTrace (prefixWord ++ tailWord_383425) baseStart_383425 baseEnd_383425 := by
    simpa [prefixWord, tailWord_383425, baseEnd_383425] using wordTrace_append hprefix tailTrace_383425
  have hstable : (prefixWord ++ tailWord_383425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383425).length < 2 ^ (prefixWord ++ tailWord_383425).sum := by decide
  have hdescent : baseEnd_383425 < baseStart_383425 := by decide
  rcases family_descends (prefixWord ++ tailWord_383425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383432 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_383432 : Nat := 118140960795 + 383432 * 2 ^ 59
def prefixEnd_383432 : Nat := 4983230072969 + 3 ^ 40 * 383432 * 2
def baseEnd_383432 : Nat := 43752203181077567608141

theorem tailTrace_383432 : CollatzResearch.WordTrace tailWord_383432 prefixEnd_383432 43752203181077567608141 := by
  unfold tailWord_383432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992456973449411908592275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9323275964599215878123033 6992456973449411908592275)
  ·
    refine ⟨10488685460174117862888413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6992456973449411908592275 10488685460174117862888413)
    ·
      refine ⟨3933257047565294198583155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10488685460174117862888413 3933257047565294198583155)
      ·
        refine ⟨5899885571347941297874733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933257047565294198583155 5899885571347941297874733)
        ·
          refine ⟨2212457089255477986703025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5899885571347941297874733 2212457089255477986703025)
          ·
            refine ⟨1659342816941608490027269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2212457089255477986703025 1659342816941608490027269)
            ·
              refine ⟨311126778176551591880113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1659342816941608490027269 311126778176551591880113)
              ·
                refine ⟨233345083632413693910085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311126778176551591880113 233345083632413693910085)
                ·
                  refine ⟨43752203181077567608141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 233345083632413693910085 43752203181077567608141)
                  ·
                    rfl

theorem cell22_383432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_383432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383432 prefixEnd_383432 := by exact prefixLift 383432
  have htrace : WordTrace (prefixWord ++ tailWord_383432) baseStart_383432 baseEnd_383432 := by
    simpa [prefixWord, tailWord_383432, baseEnd_383432] using wordTrace_append hprefix tailTrace_383432
  have hstable : (prefixWord ++ tailWord_383432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383432).length < 2 ^ (prefixWord ++ tailWord_383432).sum := by decide
  have hdescent : baseEnd_383432 < baseStart_383432 := by decide
  rcases family_descends (prefixWord ++ tailWord_383432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383492 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_383492 : Nat := 118140960795 + 383492 * 2 ^ 59
def prefixEnd_383492 : Nat := 4983230072969 + 3 ^ 40 * 383492 * 2
def baseEnd_383492 : Nat := 131277148769412546324239

theorem tailTrace_383492 : CollatzResearch.WordTrace tailWord_383492 prefixEnd_383492 131277148769412546324239 := by
  unfold tailWord_383492
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993551163340727032184365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9324734884454302709579153 6993551163340727032184365)
  ·
    refine ⟨2622581686252772637069137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6993551163340727032184365 2622581686252772637069137)
    ·
      refine ⟨1966936264689579477801853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2622581686252772637069137 1966936264689579477801853)
      ·
        refine ⟨737601099258592304175695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1966936264689579477801853 737601099258592304175695)
        ·
          refine ⟨1106401648887888456263543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737601099258592304175695 1106401648887888456263543)
          ·
            refine ⟨1659602473331832684395315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106401648887888456263543 1659602473331832684395315)
            ·
              refine ⟨2489403709997749026592973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659602473331832684395315 2489403709997749026592973)
              ·
                refine ⟨933526391249155884972365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489403709997749026592973 933526391249155884972365)
                ·
                  refine ⟨350072396718433456864637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 933526391249155884972365 350072396718433456864637)
                  ·
                    refine ⟨131277148769412546324239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350072396718433456864637 131277148769412546324239)
                    ·
                      rfl

theorem cell22_383492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_383492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383492 prefixEnd_383492 := by exact prefixLift 383492
  have htrace : WordTrace (prefixWord ++ tailWord_383492) baseStart_383492 baseEnd_383492 := by
    simpa [prefixWord, tailWord_383492, baseEnd_383492] using wordTrace_append hprefix tailTrace_383492
  have hstable : (prefixWord ++ tailWord_383492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383492).length < 2 ^ (prefixWord ++ tailWord_383492).sum := by decide
  have hdescent : baseEnd_383492 < baseStart_383492 := by decide
  rcases family_descends (prefixWord ++ tailWord_383492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383556 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_383556 : Nat := 118140960795 + 383556 * 2 ^ 59
def prefixEnd_383556 : Nat := 4983230072969 + 3 ^ 40 * 383556 * 2
def baseEnd_383556 : Nat := 43766352425779237574681

theorem tailTrace_383556 : CollatzResearch.WordTrace tailWord_383556 prefixEnd_383556 43766352425779237574681 := by
  unfold tailWord_383556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6994718299224796497349261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9326291065633061996465681 6994718299224796497349261)
  ·
    refine ⟨2623019362209298686505973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6994718299224796497349261 2623019362209298686505973)
    ·
      refine ⟨245908065207121751859935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2623019362209298686505973 245908065207121751859935)
      ·
        refine ⟨368862097810682627789903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245908065207121751859935 368862097810682627789903)
        ·
          refine ⟨553293146716023941684855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368862097810682627789903 553293146716023941684855)
          ·
            refine ⟨829939720074035912527283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553293146716023941684855 829939720074035912527283)
            ·
              refine ⟨1244909580111053868790925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829939720074035912527283 1244909580111053868790925)
              ·
                refine ⟨466841092541645200796597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244909580111053868790925 466841092541645200796597)
                ·
                  refine ⟨43766352425779237574681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 466841092541645200796597 43766352425779237574681)
                  ·
                    rfl

theorem cell22_383556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_383556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383556 prefixEnd_383556 := by exact prefixLift 383556
  have htrace : WordTrace (prefixWord ++ tailWord_383556) baseStart_383556 baseEnd_383556 := by
    simpa [prefixWord, tailWord_383556, baseEnd_383556] using wordTrace_append hprefix tailTrace_383556
  have hstable : (prefixWord ++ tailWord_383556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383556).length < 2 ^ (prefixWord ++ tailWord_383556).sum := by decide
  have hdescent : baseEnd_383556 < baseStart_383556 := by decide
  rcases family_descends (prefixWord ++ tailWord_383556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383563 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_383563 : Nat := 118140960795 + 383563 * 2 ^ 59
def prefixEnd_383563 : Nat := 4983230072969 + 3 ^ 40 * 383563 * 2
def baseEnd_383563 : Nat := 131301453520392027799021

theorem tailTrace_383563 : CollatzResearch.WordTrace tailWord_383563 prefixEnd_383563 131301453520392027799021 := by
  unfold tailWord_383563
  simp only [CollatzResearch.WordTrace]
  refine ⟨13989691909424233190203343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9326461272949488793468895 13989691909424233190203343)
  ·
    refine ⟨20984537864136349785305015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13989691909424233190203343 20984537864136349785305015)
    ·
      refine ⟨31476806796204524677957523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984537864136349785305015 31476806796204524677957523)
      ·
        refine ⟨47215210194306787016936285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31476806796204524677957523 47215210194306787016936285)
        ·
          refine ⟨17705703822865045131351107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47215210194306787016936285 17705703822865045131351107)
          ·
            refine ⟨26558555734297567697026661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17705703822865045131351107 26558555734297567697026661)
            ·
              refine ⟨4979729200180793943192499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26558555734297567697026661 4979729200180793943192499)
              ·
                refine ⟨7469593800271190914788749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979729200180793943192499 7469593800271190914788749)
                ·
                  refine ⟨2801097675101696593045781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7469593800271190914788749 2801097675101696593045781)
                  ·
                    refine ⟨131301453520392027799021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2801097675101696593045781 131301453520392027799021)
                    ·
                      rfl

theorem cell22_383563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_383563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383563 prefixEnd_383563 := by exact prefixLift 383563
  have htrace : WordTrace (prefixWord ++ tailWord_383563) baseStart_383563 baseEnd_383563 := by
    simpa [prefixWord, tailWord_383563, baseEnd_383563] using wordTrace_append hprefix tailTrace_383563
  have hstable : (prefixWord ++ tailWord_383563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383563).length < 2 ^ (prefixWord ++ tailWord_383563).sum := by decide
  have hdescent : baseEnd_383563 < baseStart_383563 := by decide
  rcases family_descends (prefixWord ++ tailWord_383563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383597 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_383597 : Nat := 118140960795 + 383597 * 2 ^ 59
def prefixEnd_383597 : Nat := 4983230072969 + 3 ^ 40 * 383597 * 2
def baseEnd_383597 : Nat := 131313092415227272448917

theorem tailTrace_383597 : CollatzResearch.WordTrace tailWord_383597 prefixEnd_383597 131313092415227272448917 := by
  unfold tailWord_383597
  simp only [CollatzResearch.WordTrace]
  refine ⟨13990931991301056996941045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9327287994200704664627363 13990931991301056996941045)
  ·
    refine ⟨1311649874184474093463223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13990931991301056996941045 1311649874184474093463223)
    ·
      refine ⟨1967474811276711140194835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311649874184474093463223 1967474811276711140194835)
      ·
        refine ⟨2951212216915066710292253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967474811276711140194835 2951212216915066710292253)
        ·
          refine ⟨1106704581343150016359595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2951212216915066710292253 1106704581343150016359595)
          ·
            refine ⟨1660056872014725024539393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106704581343150016359595 1660056872014725024539393)
            ·
              refine ⟨1245042654011043768404545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660056872014725024539393 1245042654011043768404545)
              ·
                refine ⟨933781990508282826303409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245042654011043768404545 933781990508282826303409)
                ·
                  refine ⟨700336492881212119727557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 933781990508282826303409 700336492881212119727557)
                  ·
                    refine ⟨131313092415227272448917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 700336492881212119727557 131313092415227272448917)
                    ·
                      rfl

theorem cell22_383597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_383597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383597 prefixEnd_383597 := by exact prefixLift 383597
  have htrace : WordTrace (prefixWord ++ tailWord_383597) baseStart_383597 baseEnd_383597 := by
    simpa [prefixWord, tailWord_383597, baseEnd_383597] using wordTrace_append hprefix tailTrace_383597
  have hstable : (prefixWord ++ tailWord_383597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383597).length < 2 ^ (prefixWord ++ tailWord_383597).sum := by decide
  have hdescent : baseEnd_383597 < baseStart_383597 := by decide
  rcases family_descends (prefixWord ++ tailWord_383597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383640 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_383640 : Nat := 118140960795 + 383640 * 2 ^ 59
def prefixEnd_383640 : Nat := 4983230072969 + 3 ^ 40 * 383640 * 2
def baseEnd_383640 : Nat := 43775937397996497874595

theorem tailTrace_383640 : CollatzResearch.WordTrace tailWord_383640 prefixEnd_383640 43775937397996497874595 := by
  unfold tailWord_383640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996250165072637670378187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9328333553430183560504249 6996250165072637670378187)
  ·
    refine ⟨10494375247608956505567281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996250165072637670378187 10494375247608956505567281)
    ·
      refine ⟨7870781435706717379175461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10494375247608956505567281 7870781435706717379175461)
      ·
        refine ⟨1475771519195009508595399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7870781435706717379175461 1475771519195009508595399)
        ·
          refine ⟨2213657278792514262893099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475771519195009508595399 2213657278792514262893099)
          ·
            refine ⟨3320485918188771394339649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213657278792514262893099 3320485918188771394339649)
            ·
              refine ⟨2490364438641578545754737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3320485918188771394339649 2490364438641578545754737)
              ·
                refine ⟨1867773328981183909316053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490364438641578545754737 1867773328981183909316053)
                ·
                  refine ⟨43775937397996497874595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1867773328981183909316053 43775937397996497874595)
                  ·
                    rfl

theorem cell22_383640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_383640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383640 prefixEnd_383640 := by exact prefixLift 383640
  have htrace : WordTrace (prefixWord ++ tailWord_383640) baseStart_383640 baseEnd_383640 := by
    simpa [prefixWord, tailWord_383640, baseEnd_383640] using wordTrace_append hprefix tailTrace_383640
  have hstable : (prefixWord ++ tailWord_383640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383640).length < 2 ^ (prefixWord ++ tailWord_383640).sum := by decide
  have hdescent : baseEnd_383640 < baseStart_383640 := by decide
  rcases family_descends (prefixWord ++ tailWord_383640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383661 : List Nat := [1, 5, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_383661 : Nat := 118140960795 + 383661 * 2 ^ 59
def prefixEnd_383661 : Nat := 4983230072969 + 3 ^ 40 * 383661 * 2
def baseEnd_383661 : Nat := 131335000923152438848721

theorem tailTrace_383661 : CollatzResearch.WordTrace tailWord_383661 prefixEnd_383661 131335000923152438848721 := by
  unfold tailWord_383661
  simp only [CollatzResearch.WordTrace]
  refine ⟨13993266263069195927270837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9328844175379463951513891 13993266263069195927270837)
  ·
    refine ⟨1311868712162737118181641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13993266263069195927270837 1311868712162737118181641)
    ·
      refine ⟨983901534122052838636231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1311868712162737118181641 983901534122052838636231)
      ·
        refine ⟨1475852301183079257954347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 983901534122052838636231 1475852301183079257954347)
        ·
          refine ⟨2213778451774618886931521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1475852301183079257954347 2213778451774618886931521)
          ·
            refine ⟨1660333838830964165198641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2213778451774618886931521 1660333838830964165198641)
            ·
              refine ⟨1245250379123223123898981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660333838830964165198641 1245250379123223123898981)
              ·
                refine ⟨233484446085604335731059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1245250379123223123898981 233484446085604335731059)
                ·
                  refine ⟨350226669128406503596589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233484446085604335731059 350226669128406503596589)
                  ·
                    refine ⟨131335000923152438848721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350226669128406503596589 131335000923152438848721)
                    ·
                      rfl

theorem cell22_383661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_383661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383661 prefixEnd_383661 := by exact prefixLift 383661
  have htrace : WordTrace (prefixWord ++ tailWord_383661) baseStart_383661 baseEnd_383661 := by
    simpa [prefixWord, tailWord_383661, baseEnd_383661] using wordTrace_append hprefix tailTrace_383661
  have hstable : (prefixWord ++ tailWord_383661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383661).length < 2 ^ (prefixWord ++ tailWord_383661).sum := by decide
  have hdescent : baseEnd_383661 < baseStart_383661 := by decide
  rcases family_descends (prefixWord ++ tailWord_383661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383867 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_383867 : Nat := 118140960795 + 383867 * 2 ^ 59
def prefixEnd_383867 : Nat := 4983230072969 + 3 ^ 40 * 383867 * 2
def baseEnd_383867 : Nat := 131405518933036568198089

theorem tailTrace_383867 : CollatzResearch.WordTrace tailWord_383867 prefixEnd_383867 131405518933036568198089 := by
  unfold tailWord_383867
  simp only [CollatzResearch.WordTrace]
  refine ⟨14000779700322893109269855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9333853133548595406179903 14000779700322893109269855)
  ·
    refine ⟨21001169550484339663904783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14000779700322893109269855 21001169550484339663904783)
    ·
      refine ⟨31501754325726509495857175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21001169550484339663904783 31501754325726509495857175)
      ·
        refine ⟨47252631488589764243785763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31501754325726509495857175 47252631488589764243785763)
        ·
          refine ⟨70878947232884646365678645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47252631488589764243785763 70878947232884646365678645)
          ·
            refine ⟨6644901303082935596782373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70878947232884646365678645 6644901303082935596782373)
            ·
              refine ⟨1245918994328050424396695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6644901303082935596782373 1245918994328050424396695)
              ·
                refine ⟨1868878491492075636595043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245918994328050424396695 1868878491492075636595043)
                ·
                  refine ⟨2803317737238113454892565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868878491492075636595043 2803317737238113454892565)
                  ·
                    refine ⟨131405518933036568198089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2803317737238113454892565 131405518933036568198089)
                    ·
                      rfl

theorem cell22_383867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_383867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383867 prefixEnd_383867 := by exact prefixLift 383867
  have htrace : WordTrace (prefixWord ++ tailWord_383867) baseStart_383867 baseEnd_383867 := by
    simpa [prefixWord, tailWord_383867, baseEnd_383867] using wordTrace_append hprefix tailTrace_383867
  have hstable : (prefixWord ++ tailWord_383867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383867).length < 2 ^ (prefixWord ++ tailWord_383867).sum := by decide
  have hdescent : baseEnd_383867 < baseStart_383867 := by decide
  rcases family_descends (prefixWord ++ tailWord_383867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383869 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_383869 : Nat := 118140960795 + 383869 * 2 ^ 59
def prefixEnd_383869 : Nat := 4983230072969 + 3 ^ 40 * 383869 * 2
def baseEnd_383869 : Nat := 131406203573909229648083

theorem tailTrace_383869 : CollatzResearch.WordTrace tailWord_383869 prefixEnd_383869 131406203573909229648083 := by
  unfold tailWord_383869
  simp only [CollatzResearch.WordTrace]
  refine ⟨14000852646315647450842661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9333901764210431633895107 14000852646315647450842661)
  ·
    refine ⟨2625159871184183897032999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14000852646315647450842661 2625159871184183897032999)
    ·
      refine ⟨3937739806776275845549499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625159871184183897032999 3937739806776275845549499)
      ·
        refine ⟨5906609710164413768324249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937739806776275845549499 5906609710164413768324249)
        ·
          refine ⟨4429957282623310326243187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5906609710164413768324249 4429957282623310326243187)
          ·
            refine ⟨6644935923934965489364781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429957282623310326243187 6644935923934965489364781)
            ·
              refine ⟨2491850971475612058511793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6644935923934965489364781 2491850971475612058511793)
              ·
                refine ⟨1868888228606709043883845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2491850971475612058511793 1868888228606709043883845)
                ·
                  refine ⟨350416542863757945728221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868888228606709043883845 350416542863757945728221)
                  ·
                    refine ⟨131406203573909229648083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350416542863757945728221 131406203573909229648083)
                    ·
                      rfl

theorem cell22_383869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_383869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383869 prefixEnd_383869 := by exact prefixLift 383869
  have htrace : WordTrace (prefixWord ++ tailWord_383869) baseStart_383869 baseEnd_383869 := by
    simpa [prefixWord, tailWord_383869, baseEnd_383869] using wordTrace_append hprefix tailTrace_383869
  have hstable : (prefixWord ++ tailWord_383869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383869).length < 2 ^ (prefixWord ++ tailWord_383869).sum := by decide
  have hdescent : baseEnd_383869 < baseStart_383869 := by decide
  rcases family_descends (prefixWord ++ tailWord_383869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383903 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 2, 3]
def baseStart_383903 : Nat := 118140960795 + 383903 * 2 ^ 59
def prefixEnd_383903 : Nat := 4983230072969 + 3 ^ 40 * 383903 * 2
def baseEnd_383903 : Nat := 131417842468744474297979

theorem tailTrace_383903 : CollatzResearch.WordTrace tailWord_383903 prefixEnd_383903 131417842468744474297979 := by
  unfold tailWord_383903
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002092728192471257580363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9334728485461647505053575 14002092728192471257580363)
  ·
    refine ⟨21003139092288706886370545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14002092728192471257580363 21003139092288706886370545)
    ·
      refine ⟨15752354319216530164777909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21003139092288706886370545 15752354319216530164777909)
      ·
        refine ⟨1476783217426549702947929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15752354319216530164777909 1476783217426549702947929)
        ·
          refine ⟨1107587413069912277210947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476783217426549702947929 1107587413069912277210947)
          ·
            refine ⟨1661381119604868415816421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107587413069912277210947 1661381119604868415816421)
            ·
              refine ⟨311508959925912827965579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1661381119604868415816421 311508959925912827965579)
              ·
                refine ⟨467263439888869241948369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311508959925912827965579 467263439888869241948369)
                ·
                  refine ⟨350447579916651931461277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467263439888869241948369 350447579916651931461277)
                  ·
                    refine ⟨131417842468744474297979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350447579916651931461277 131417842468744474297979)
                    ·
                      rfl

theorem cell22_383903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_383903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383903 prefixEnd_383903 := by exact prefixLift 383903
  have htrace : WordTrace (prefixWord ++ tailWord_383903) baseStart_383903 baseEnd_383903 := by
    simpa [prefixWord, tailWord_383903, baseEnd_383903] using wordTrace_append hprefix tailTrace_383903
  have hstable : (prefixWord ++ tailWord_383903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383903).length < 2 ^ (prefixWord ++ tailWord_383903).sum := by decide
  have hdescent : baseEnd_383903 < baseStart_383903 := by decide
  rcases family_descends (prefixWord ++ tailWord_383903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383927 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 9]
def baseStart_383927 : Nat := 118140960795 + 383927 * 2 ^ 59
def prefixEnd_383927 : Nat := 4983230072969 + 3 ^ 40 * 383927 * 2
def baseEnd_383927 : Nat := 43808686053072137232635

theorem tailTrace_383927 : CollatzResearch.WordTrace tailWord_383927 prefixEnd_383927 43808686053072137232635 := by
  unfold tailWord_383927
  simp only [CollatzResearch.WordTrace]
  refine ⟨14002968080105523356454035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9335312053403682237636023 14002968080105523356454035)
  ·
    refine ⟨21004452120158285034681053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14002968080105523356454035 21004452120158285034681053)
    ·
      refine ⟨7876669545059356888005395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21004452120158285034681053 7876669545059356888005395)
      ·
        refine ⟨11815004317589035332008093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876669545059356888005395 11815004317589035332008093)
        ·
          refine ⟨4430626619095888249503035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11815004317589035332008093 4430626619095888249503035)
          ·
            refine ⟨6645939928643832374254553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430626619095888249503035 6645939928643832374254553)
            ·
              refine ⟨4984454946482874280690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6645939928643832374254553 4984454946482874280690915)
              ·
                refine ⟨7476682419724311421036373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984454946482874280690915 7476682419724311421036373)
                ·
                  refine ⟨43808686053072137232635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7476682419724311421036373 43808686053072137232635)
                  ·
                    rfl

theorem cell22_383927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_383927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383927 prefixEnd_383927 := by exact prefixLift 383927
  have htrace : WordTrace (prefixWord ++ tailWord_383927) baseStart_383927 baseEnd_383927 := by
    simpa [prefixWord, tailWord_383927, baseEnd_383927] using wordTrace_append hprefix tailTrace_383927
  have hstable : (prefixWord ++ tailWord_383927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383927).length < 2 ^ (prefixWord ++ tailWord_383927).sum := by decide
  have hdescent : baseEnd_383927 < baseStart_383927 := by decide
  rcases family_descends (prefixWord ++ tailWord_383927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383948 : List Nat := [2, 2, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_383948 : Nat := 118140960795 + 383948 * 2 ^ 59
def prefixEnd_383948 : Nat := 4983230072969 + 3 ^ 40 * 383948 * 2
def baseEnd_383948 : Nat := 131433246888379356922841

theorem tailTrace_383948 : CollatzResearch.WordTrace tailWord_383948 prefixEnd_383948 131433246888379356922841 := by
  unfold tailWord_383948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001867006514721971484249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9335822675352962628645665 7001867006514721971484249)
  ·
    refine ⟨5251400254886041478613187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7001867006514721971484249 5251400254886041478613187)
    ·
      refine ⟨7877100382329062217919781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251400254886041478613187 7877100382329062217919781)
      ·
        refine ⟨1476956321686699165859959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7877100382329062217919781 1476956321686699165859959)
        ·
          refine ⟨2215434482530048748789939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476956321686699165859959 2215434482530048748789939)
          ·
            refine ⟨3323151723795073123184909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215434482530048748789939 3323151723795073123184909)
            ·
              refine ⟨1246181896423152421194341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3323151723795073123184909 1246181896423152421194341)
              ·
                refine ⟨233659105579341078973939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1246181896423152421194341 233659105579341078973939)
                ·
                  refine ⟨350488658369011618460909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233659105579341078973939 350488658369011618460909)
                  ·
                    refine ⟨131433246888379356922841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350488658369011618460909 131433246888379356922841)
                    ·
                      rfl

theorem cell22_383948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_383948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_383948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_383948 prefixEnd_383948 := by exact prefixLift 383948
  have htrace : WordTrace (prefixWord ++ tailWord_383948) baseStart_383948 baseEnd_383948 := by
    simpa [prefixWord, tailWord_383948, baseEnd_383948] using wordTrace_append hprefix tailTrace_383948
  have hstable : (prefixWord ++ tailWord_383948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383948).length < 2 ^ (prefixWord ++ tailWord_383948).sum := by decide
  have hdescent : baseEnd_383948 < baseStart_383948 := by decide
  rcases family_descends (prefixWord ++ tailWord_383948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384021 : List Nat := [1, 3, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_384021 : Nat := 118140960795 + 384021 * 2 ^ 59
def prefixEnd_384021 : Nat := 4983230072969 + 3 ^ 40 * 384021 * 2
def baseEnd_384021 : Nat := 131458236280231499847617

theorem tailTrace_384021 : CollatzResearch.WordTrace tailWord_384021 prefixEnd_384021 131458236280231499847617 := by
  unfold tailWord_384021
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006396541764977410375917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9337597694509984940250611 14006396541764977410375917)
  ·
    refine ⟨5252398703161866528890969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14006396541764977410375917 5252398703161866528890969)
    ·
      refine ⟨3939299027371399896668227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5252398703161866528890969 3939299027371399896668227)
      ·
        refine ⟨5908948541057099845002341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939299027371399896668227 5908948541057099845002341)
        ·
          refine ⟨1107927851448206220937939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5908948541057099845002341 1107927851448206220937939)
          ·
            refine ⟨1661891777172309331406909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107927851448206220937939 1661891777172309331406909)
            ·
              refine ⟨623209416439615999277591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1661891777172309331406909 623209416439615999277591)
              ·
                refine ⟨934814124659423998916387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623209416439615999277591 934814124659423998916387)
                ·
                  refine ⟨1402221186989135998374581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934814124659423998916387 1402221186989135998374581)
                  ·
                    refine ⟨131458236280231499847617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1402221186989135998374581 131458236280231499847617)
                    ·
                      rfl

theorem cell22_384021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_384021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384021 prefixEnd_384021 := by exact prefixLift 384021
  have htrace : WordTrace (prefixWord ++ tailWord_384021) baseStart_384021 baseEnd_384021 := by
    simpa [prefixWord, tailWord_384021, baseEnd_384021] using wordTrace_append hprefix tailTrace_384021
  have hstable : (prefixWord ++ tailWord_384021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384021).length < 2 ^ (prefixWord ++ tailWord_384021).sum := by decide
  have hdescent : baseEnd_384021 < baseStart_384021 := by decide
  rcases family_descends (prefixWord ++ tailWord_384021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384036 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_384036 : Nat := 118140960795 + 384036 * 2 ^ 59
def prefixEnd_384036 : Nat := 4983230072969 + 3 ^ 40 * 384036 * 2
def baseEnd_384036 : Nat := 131463371086776460722571

theorem tailTrace_384036 : CollatzResearch.WordTrace tailWord_384036 prefixEnd_384036 131463371086776460722571 := by
  unfold tailWord_384036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003471818355317486085981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9337962424473756648114641 7003471818355317486085981)
  ·
    refine ⟨2626301931883244057282243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7003471818355317486085981 2626301931883244057282243)
    ·
      refine ⟨3939452897824866085923365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2626301931883244057282243 3939452897824866085923365)
      ·
        refine ⟨738647418342162391110631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3939452897824866085923365 738647418342162391110631)
        ·
          refine ⟨1107971127513243586665947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738647418342162391110631 1107971127513243586665947)
          ·
            refine ⟨1661956691269865379998921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107971127513243586665947 1661956691269865379998921)
            ·
              refine ⟨1246467518452399034999191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661956691269865379998921 1246467518452399034999191)
              ·
                refine ⟨1869701277678598552498787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246467518452399034999191 1869701277678598552498787)
                ·
                  refine ⟨2804551916517897828748181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869701277678598552498787 2804551916517897828748181)
                  ·
                    refine ⟨131463371086776460722571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2804551916517897828748181 131463371086776460722571)
                    ·
                      rfl

theorem cell22_384036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_384036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384036 prefixEnd_384036 := by exact prefixLift 384036
  have htrace : WordTrace (prefixWord ++ tailWord_384036) baseStart_384036 baseEnd_384036 := by
    simpa [prefixWord, tailWord_384036, baseEnd_384036] using wordTrace_append hprefix tailTrace_384036
  have hstable : (prefixWord ++ tailWord_384036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384036).length < 2 ^ (prefixWord ++ tailWord_384036).sum := by decide
  have hdescent : baseEnd_384036 < baseStart_384036 := by decide
  rcases family_descends (prefixWord ++ tailWord_384036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384064 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 6]
def baseStart_384064 : Nat := 118140960795 + 384064 * 2 ^ 59
def prefixEnd_384064 : Nat := 4983230072969 + 3 ^ 40 * 384064 * 2
def baseEnd_384064 : Nat := 131472956058993721022485

theorem tailTrace_384064 : CollatzResearch.WordTrace tailWord_384064 prefixEnd_384064 131472956058993721022485 := by
  unfold tailWord_384064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003982440304597877095623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9338643253739463836127497 7003982440304597877095623)
  ·
    refine ⟨10505973660456896815643435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7003982440304597877095623 10505973660456896815643435)
    ·
      refine ⟨15758960490685345223465153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505973660456896815643435 15758960490685345223465153)
      ·
        refine ⟨11819220368014008917598865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15758960490685345223465153 11819220368014008917598865)
        ·
          refine ⟨8864415276010506688199149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11819220368014008917598865 8864415276010506688199149)
          ·
            refine ⟨3324155728503940008074681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8864415276010506688199149 3324155728503940008074681)
            ·
              refine ⟨2493116796377955006056011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3324155728503940008074681 2493116796377955006056011)
              ·
                refine ⟨3739675194566932509084017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493116796377955006056011 3739675194566932509084017)
                ·
                  refine ⟨2804756395925199381813013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3739675194566932509084017 2804756395925199381813013)
                  ·
                    refine ⟨131472956058993721022485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2804756395925199381813013 131472956058993721022485)
                    ·
                      rfl

theorem cell22_384064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_384064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384064 prefixEnd_384064 := by exact prefixLift 384064
  have htrace : WordTrace (prefixWord ++ tailWord_384064) baseStart_384064 baseEnd_384064 := by
    simpa [prefixWord, tailWord_384064, baseEnd_384064] using wordTrace_append hprefix tailTrace_384064
  have hstable : (prefixWord ++ tailWord_384064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384064).length < 2 ^ (prefixWord ++ tailWord_384064).sum := by decide
  have hdescent : baseEnd_384064 < baseStart_384064 := by decide
  rcases family_descends (prefixWord ++ tailWord_384064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384190 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_384190 : Nat := 118140960795 + 384190 * 2 ^ 59
def prefixEnd_384190 : Nat := 4983230072969 + 3 ^ 40 * 384190 * 2
def baseEnd_384190 : Nat := 131516088433971392372099

theorem tailTrace_384190 : CollatzResearch.WordTrace tailWord_384190 prefixEnd_384190 131516088433971392372099 := by
  unfold tailWord_384190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1751570059769089909159753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9341706985435146182185349 1751570059769089909159753)
  ·
    refine ⟨1313677544826817431869815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1751570059769089909159753 1313677544826817431869815)
    ·
      refine ⟨1970516317240226147804723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1313677544826817431869815 1970516317240226147804723)
      ·
        refine ⟨2955774475860339221707085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1970516317240226147804723 2955774475860339221707085)
        ·
          refine ⟨1108415428447627208140157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2955774475860339221707085 1108415428447627208140157)
          ·
            refine ⟨415655785667860203052559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1108415428447627208140157 415655785667860203052559)
            ·
              refine ⟨623483678501790304578839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415655785667860203052559 623483678501790304578839)
              ·
                refine ⟨935225517752685456868259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623483678501790304578839 935225517752685456868259)
                ·
                  refine ⟨1402838276629028185302389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935225517752685456868259 1402838276629028185302389)
                  ·
                    refine ⟨131516088433971392372099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1402838276629028185302389 131516088433971392372099)
                    ·
                      rfl

theorem cell22_384190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_384190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384190 prefixEnd_384190 := by exact prefixLift 384190
  have htrace : WordTrace (prefixWord ++ tailWord_384190) baseStart_384190 baseEnd_384190 := by
    simpa [prefixWord, tailWord_384190, baseEnd_384190] using wordTrace_append hprefix tailTrace_384190
  have hstable : (prefixWord ++ tailWord_384190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384190).length < 2 ^ (prefixWord ++ tailWord_384190).sum := by decide
  have hdescent : baseEnd_384190 < baseStart_384190 := by decide
  rcases family_descends (prefixWord ++ tailWord_384190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384194 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_384194 : Nat := 118140960795 + 384194 * 2 ^ 59
def prefixEnd_384194 : Nat := 4983230072969 + 3 ^ 40 * 384194 * 2
def baseEnd_384194 : Nat := 131517457715716715272087

theorem tailTrace_384194 : CollatzResearch.WordTrace tailWord_384194 prefixEnd_384194 131517457715716715272087 := by
  unfold tailWord_384194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503176592534556989105909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9341804246758818637615757 3503176592534556989105909)
  ·
    refine ⟨328422805550114717728679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3503176592534556989105909 328422805550114717728679)
    ·
      refine ⟨492634208325172076593019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328422805550114717728679 492634208325172076593019)
      ·
        refine ⟨738951312487758114889529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492634208325172076593019 738951312487758114889529)
        ·
          refine ⟨554213484365818586167147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738951312487758114889529 554213484365818586167147)
          ·
            refine ⟨831320226548727879250721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554213484365818586167147 831320226548727879250721)
            ·
              refine ⟨623490169911545909438041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831320226548727879250721 623490169911545909438041)
              ·
                refine ⟨467617627433659432078531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623490169911545909438041 467617627433659432078531)
                ·
                  refine ⟨701426441150489148117797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467617627433659432078531 701426441150489148117797)
                  ·
                    refine ⟨131517457715716715272087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701426441150489148117797 131517457715716715272087)
                    ·
                      rfl

theorem cell22_384194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_384194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384194 prefixEnd_384194 := by exact prefixLift 384194
  have htrace : WordTrace (prefixWord ++ tailWord_384194) baseStart_384194 baseEnd_384194 := by
    simpa [prefixWord, tailWord_384194, baseEnd_384194] using wordTrace_append hprefix tailTrace_384194
  have hstable : (prefixWord ++ tailWord_384194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384194).length < 2 ^ (prefixWord ++ tailWord_384194).sum := by decide
  have hdescent : baseEnd_384194 < baseStart_384194 := by decide
  rcases family_descends (prefixWord ++ tailWord_384194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384235 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 3, 3]
def baseStart_384235 : Nat := 118140960795 + 384235 * 2 ^ 59
def prefixEnd_384235 : Nat := 4983230072969 + 3 ^ 40 * 384235 * 2
def baseEnd_384235 : Nat := 131531492853606274996961

theorem tailTrace_384235 : CollatzResearch.WordTrace tailWord_384235 prefixEnd_384235 131531492853606274996961 := by
  unfold tailWord_384235
  simp only [CollatzResearch.WordTrace]
  refine ⟨14014201762989691958666159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342801175326461305777439 14014201762989691958666159)
  ·
    refine ⟨21021302644484537937999239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14014201762989691958666159 21021302644484537937999239)
    ·
      refine ⟨31531953966726806906998859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21021302644484537937999239 31531953966726806906998859)
      ·
        refine ⟨47297930950090210360498289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31531953966726806906998859 47297930950090210360498289)
        ·
          refine ⟨35473448212567657770373717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47297930950090210360498289 35473448212567657770373717)
          ·
            refine ⟨415704471241027239496567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 35473448212567657770373717 415704471241027239496567)
            ·
              refine ⟨623556706861540859244851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415704471241027239496567 623556706861540859244851)
              ·
                refine ⟨935335060292311288867277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623556706861540859244851 935335060292311288867277)
                ·
                  refine ⟨350750647609616733325229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935335060292311288867277 350750647609616733325229)
                  ·
                    refine ⟨131531492853606274996961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350750647609616733325229 131531492853606274996961)
                    ·
                      rfl

theorem cell22_384235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3].length) (baseStart_384235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384235 prefixEnd_384235 := by exact prefixLift 384235
  have htrace : WordTrace (prefixWord ++ tailWord_384235) baseStart_384235 baseEnd_384235 := by
    simpa [prefixWord, tailWord_384235, baseEnd_384235] using wordTrace_append hprefix tailTrace_384235
  have hstable : (prefixWord ++ tailWord_384235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384235).length < 2 ^ (prefixWord ++ tailWord_384235).sum := by decide
  have hdescent : baseEnd_384235 < baseStart_384235 := by decide
  rcases family_descends (prefixWord ++ tailWord_384235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384286 : List Nat := [4, 3, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_384286 : Nat := 118140960795 + 384286 * 2 ^ 59
def prefixEnd_384286 : Nat := 4983230072969 + 3 ^ 40 * 384286 * 2
def baseEnd_384286 : Nat := 131548951195859141971805

theorem tailTrace_384286 : CollatzResearch.WordTrace tailWord_384286 prefixEnd_384286 131548951195859141971805 := by
  unfold tailWord_384286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1752007735725615958596589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9344041257203285112515141 1752007735725615958596589)
  ·
    refine ⟨657002900897105984473721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1752007735725615958596589 657002900897105984473721)
    ·
      refine ⟨492752175672829488355291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 657002900897105984473721 492752175672829488355291)
      ·
        refine ⟨739128263509244232532937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492752175672829488355291 739128263509244232532937)
        ·
          refine ⟨554346197631933174399703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739128263509244232532937 554346197631933174399703)
          ·
            refine ⟨831519296447899761599555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554346197631933174399703 831519296447899761599555)
            ·
              refine ⟨1247278944671849642399333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831519296447899761599555 1247278944671849642399333)
              ·
                refine ⟨233864802125971807949875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1247278944671849642399333 233864802125971807949875)
                ·
                  refine ⟨350797203188957711924813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233864802125971807949875 350797203188957711924813)
                  ·
                    refine ⟨131548951195859141971805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350797203188957711924813 131548951195859141971805)
                    ·
                      rfl

theorem cell22_384286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_384286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384286 prefixEnd_384286 := by exact prefixLift 384286
  have htrace : WordTrace (prefixWord ++ tailWord_384286) baseStart_384286 baseEnd_384286 := by
    simpa [prefixWord, tailWord_384286, baseEnd_384286] using wordTrace_append hprefix tailTrace_384286
  have hstable : (prefixWord ++ tailWord_384286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384286).length < 2 ^ (prefixWord ++ tailWord_384286).sum := by decide
  have hdescent : baseEnd_384286 < baseStart_384286 := by decide
  rcases family_descends (prefixWord ++ tailWord_384286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384359 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 2, 3]
def baseStart_384359 : Nat := 118140960795 + 384359 * 2 ^ 59
def prefixEnd_384359 : Nat := 4983230072969 + 3 ^ 40 * 384359 * 2
def baseEnd_384359 : Nat := 131573940587711284896581

theorem tailTrace_384359 : CollatzResearch.WordTrace tailWord_384359 prefixEnd_384359 131573940587711284896581 := by
  unfold tailWord_384359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14018724414540461136180131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9345816276360307424120087 14018724414540461136180131)
  ·
    refine ⟨21028086621810691704270197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14018724414540461136180131 21028086621810691704270197)
    ·
      refine ⟨1971383120794752347275331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21028086621810691704270197 1971383120794752347275331)
      ·
        refine ⟨2957074681192128520912997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971383120794752347275331 2957074681192128520912997)
        ·
          refine ⟨554451502723524097671187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2957074681192128520912997 554451502723524097671187)
          ·
            refine ⟨831677254085286146506781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554451502723524097671187 831677254085286146506781)
            ·
              refine ⟨311878970281982304940043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 831677254085286146506781 311878970281982304940043)
              ·
                refine ⟨467818455422973457410065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311878970281982304940043 467818455422973457410065)
                ·
                  refine ⟨350863841567230093057549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467818455422973457410065 350863841567230093057549)
                  ·
                    refine ⟨131573940587711284896581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350863841567230093057549 131573940587711284896581)
                    ·
                      rfl

theorem cell22_384359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_384359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384359 prefixEnd_384359 := by exact prefixLift 384359
  have htrace : WordTrace (prefixWord ++ tailWord_384359) baseStart_384359 baseEnd_384359 := by
    simpa [prefixWord, tailWord_384359, baseEnd_384359] using wordTrace_append hprefix tailTrace_384359
  have hstable : (prefixWord ++ tailWord_384359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384359).length < 2 ^ (prefixWord ++ tailWord_384359).sum := by decide
  have hdescent : baseEnd_384359 < baseStart_384359 := by decide
  rcases family_descends (prefixWord ++ tailWord_384359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384370 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_384370 : Nat := 118140960795 + 384370 * 2 ^ 59
def prefixEnd_384370 : Nat := 4983230072969 + 3 ^ 40 * 384370 * 2
def baseEnd_384370 : Nat := 131577706112510922871547

theorem tailTrace_384370 : CollatzResearch.WordTrace tailWord_384370 prefixEnd_384370 131577706112510922871547 := by
  unfold tailWord_384370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504781404375152503707641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9346083745000406676553709 3504781404375152503707641)
  ·
    refine ⟨2628586053281364377780731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3504781404375152503707641 2628586053281364377780731)
    ·
      refine ⟨3942879079922046566671097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628586053281364377780731 3942879079922046566671097)
      ·
        refine ⟨2957159309941534925003323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3942879079922046566671097 2957159309941534925003323)
        ·
          refine ⟨4435738964912302387504985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957159309941534925003323 4435738964912302387504985)
          ·
            refine ⟨3326804223684226790628739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4435738964912302387504985 3326804223684226790628739)
            ·
              refine ⟨4990206335526340185943109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326804223684226790628739 4990206335526340185943109)
              ·
                refine ⟨935663687911188784864333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4990206335526340185943109 935663687911188784864333)
                ·
                  refine ⟨350873882966695794324125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935663687911188784864333 350873882966695794324125)
                  ·
                    refine ⟨131577706112510922871547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350873882966695794324125 131577706112510922871547)
                    ·
                      rfl

theorem cell22_384370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_384370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384370 prefixEnd_384370 := by exact prefixLift 384370
  have htrace : WordTrace (prefixWord ++ tailWord_384370) baseStart_384370 baseEnd_384370 := by
    simpa [prefixWord, tailWord_384370, baseEnd_384370] using wordTrace_append hprefix tailTrace_384370
  have hstable : (prefixWord ++ tailWord_384370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384370).length < 2 ^ (prefixWord ++ tailWord_384370).sum := by decide
  have hdescent : baseEnd_384370 < baseStart_384370 := by decide
  rcases family_descends (prefixWord ++ tailWord_384370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384404 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_384404 : Nat := 118140960795 + 384404 * 2 ^ 59
def prefixEnd_384404 : Nat := 4983230072969 + 3 ^ 40 * 384404 * 2
def baseEnd_384404 : Nat := 131589345007346167521443

theorem tailTrace_384404 : CollatzResearch.WordTrace tailWord_384404 prefixEnd_384404 131589345007346167521443 := by
  unfold tailWord_384404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010182849688716910784133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9346910466251622547712177 7010182849688716910784133)
  ·
    refine ⟨1314409284316634420772025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7010182849688716910784133 1314409284316634420772025)
    ·
      refine ⟨985806963237475815579019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1314409284316634420772025 985806963237475815579019)
      ·
        refine ⟨1478710444856213723368529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985806963237475815579019 1478710444856213723368529)
        ·
          refine ⟨1109032833642160292526397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478710444856213723368529 1109032833642160292526397)
          ·
            refine ⟨415887312615810109697399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1109032833642160292526397 415887312615810109697399)
            ·
              refine ⟨623830968923715164546099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415887312615810109697399 623830968923715164546099)
              ·
                refine ⟨935746453385572746819149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623830968923715164546099 935746453385572746819149)
                ·
                  refine ⟨350904920019589780057181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935746453385572746819149 350904920019589780057181)
                  ·
                    refine ⟨131589345007346167521443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350904920019589780057181 131589345007346167521443)
                    ·
                      rfl

theorem cell22_384404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_384404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384404 prefixEnd_384404 := by exact prefixLift 384404
  have htrace : WordTrace (prefixWord ++ tailWord_384404) baseStart_384404 baseEnd_384404 := by
    simpa [prefixWord, tailWord_384404, baseEnd_384404] using wordTrace_append hprefix tailTrace_384404
  have hstable : (prefixWord ++ tailWord_384404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384404).length < 2 ^ (prefixWord ++ tailWord_384404).sum := by decide
  have hdescent : baseEnd_384404 < baseStart_384404 := by decide
  rcases family_descends (prefixWord ++ tailWord_384404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384428 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 6]
def baseStart_384428 : Nat := 118140960795 + 384428 * 2 ^ 59
def prefixEnd_384428 : Nat := 4983230072969 + 3 ^ 40 * 384428 * 2
def baseEnd_384428 : Nat := 43865853565939368307123

theorem tailTrace_384428 : CollatzResearch.WordTrace tailWord_384428 prefixEnd_384428 43865853565939368307123 := by
  unfold tailWord_384428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010620525645242960220969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9347494034193657280294625 7010620525645242960220969)
  ·
    refine ⟨5257965394233932220165727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7010620525645242960220969 5257965394233932220165727)
    ·
      refine ⟨7886948091350898330248591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257965394233932220165727 7886948091350898330248591)
      ·
        refine ⟨11830422137026347495372887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7886948091350898330248591 11830422137026347495372887)
        ·
          refine ⟨17745633205539521243059331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11830422137026347495372887 17745633205539521243059331)
          ·
            refine ⟨26618449808309281864588997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17745633205539521243059331 26618449808309281864588997)
            ·
              refine ⟨4990959339057990349610437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26618449808309281864588997 4990959339057990349610437)
              ·
                refine ⟨935804876073373190551957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4990959339057990349610437 935804876073373190551957)
                ·
                  refine ⟨43865853565939368307123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 935804876073373190551957 43865853565939368307123)
                  ·
                    rfl

theorem cell22_384428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_384428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384428 prefixEnd_384428 := by exact prefixLift 384428
  have htrace : WordTrace (prefixWord ++ tailWord_384428) baseStart_384428 baseEnd_384428 := by
    simpa [prefixWord, tailWord_384428, baseEnd_384428] using wordTrace_append hprefix tailTrace_384428
  have hstable : (prefixWord ++ tailWord_384428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384428).length < 2 ^ (prefixWord ++ tailWord_384428).sum := by decide
  have hdescent : baseEnd_384428 < baseStart_384428 := by decide
  rcases family_descends (prefixWord ++ tailWord_384428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384477 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_384477 : Nat := 118140960795 + 384477 * 2 ^ 59
def prefixEnd_384477 : Nat := 4983230072969 + 3 ^ 40 * 384477 * 2
def baseEnd_384477 : Nat := 131614334399198310446219

theorem tailTrace_384477 : CollatzResearch.WordTrace tailWord_384477 prefixEnd_384477 131614334399198310446219 := by
  unfold tailWord_384477
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023028228112967288975685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9348685485408644859317123 14023028228112967288975685)
  ·
    refine ⟨2629317792771181366682941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14023028228112967288975685 2629317792771181366682941)
    ·
      refine ⟨985994172289193012506103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2629317792771181366682941 985994172289193012506103)
      ·
        refine ⟨1478991258433789518759155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985994172289193012506103 1478991258433789518759155)
        ·
          refine ⟨2218486887650684278138733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478991258433789518759155 2218486887650684278138733)
          ·
            refine ⟨831932582869006604302025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2218486887650684278138733 831932582869006604302025)
            ·
              refine ⟨623949437151754953226519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831932582869006604302025 623949437151754953226519)
              ·
                refine ⟨935924155727632429839779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623949437151754953226519 935924155727632429839779)
                ·
                  refine ⟨1403886233591448644759669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935924155727632429839779 1403886233591448644759669)
                  ·
                    refine ⟨131614334399198310446219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1403886233591448644759669 131614334399198310446219)
                    ·
                      rfl

theorem cell22_384477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_384477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384477 prefixEnd_384477 := by exact prefixLift 384477
  have htrace : WordTrace (prefixWord ++ tailWord_384477) baseStart_384477 baseEnd_384477 := by
    simpa [prefixWord, tailWord_384477, baseEnd_384477] using wordTrace_append hprefix tailTrace_384477
  have hstable : (prefixWord ++ tailWord_384477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384477).length < 2 ^ (prefixWord ++ tailWord_384477).sum := by decide
  have hdescent : baseEnd_384477 < baseStart_384477 := by decide
  rcases family_descends (prefixWord ++ tailWord_384477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_384503 : Nat := 118140960795 + 384503 * 2 ^ 59
def prefixEnd_384503 : Nat := 4983230072969 + 3 ^ 40 * 384503 * 2
def baseEnd_384503 : Nat := 131623234730542909296139

theorem tailTrace_384503 : CollatzResearch.WordTrace tailWord_384503 prefixEnd_384503 131623234730542909296139 := by
  unfold tailWord_384503
  simp only [CollatzResearch.WordTrace]
  refine ⟨14023976526018773729422163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9349317684012515819614775 14023976526018773729422163)
  ·
    refine ⟨21035964789028160594133245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14023976526018773729422163 21035964789028160594133245)
    ·
      refine ⟨7888486795885560222799967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21035964789028160594133245 7888486795885560222799967)
      ·
        refine ⟨11832730193828340334199951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888486795885560222799967 11832730193828340334199951)
        ·
          refine ⟨17749095290742510501299927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832730193828340334199951 17749095290742510501299927)
          ·
            refine ⟨26623642936113765751949891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17749095290742510501299927 26623642936113765751949891)
            ·
              refine ⟨39935464404170648627924837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26623642936113765751949891 39935464404170648627924837)
              ·
                refine ⟨7487899575781996617735907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39935464404170648627924837 7487899575781996617735907)
                ·
                  refine ⟨11231849363672994926603861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487899575781996617735907 11231849363672994926603861)
                  ·
                    refine ⟨131623234730542909296139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11231849363672994926603861 131623234730542909296139)
                    ·
                      rfl

theorem cell22_384503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_384503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384503 prefixEnd_384503 := by exact prefixLift 384503
  have htrace : WordTrace (prefixWord ++ tailWord_384503) baseStart_384503 baseEnd_384503 := by
    simpa [prefixWord, tailWord_384503, baseEnd_384503] using wordTrace_append hprefix tailTrace_384503
  have hstable : (prefixWord ++ tailWord_384503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384503).length < 2 ^ (prefixWord ++ tailWord_384503).sum := by decide
  have hdescent : baseEnd_384503 < baseStart_384503 := by decide
  rcases family_descends (prefixWord ++ tailWord_384503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384505 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_384505 : Nat := 118140960795 + 384505 * 2 ^ 59
def prefixEnd_384505 : Nat := 4983230072969 + 3 ^ 40 * 384505 * 2
def baseEnd_384505 : Nat := 131623919371415570746133

theorem tailTrace_384505 : CollatzResearch.WordTrace tailWord_384505 prefixEnd_384505 131623919371415570746133 := by
  unfold tailWord_384505
  simp only [CollatzResearch.WordTrace]
  refine ⟨14024049472011528070994969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9349366314674352047329979 14024049472011528070994969)
  ·
    refine ⟨10518037104008646053246227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14024049472011528070994969 10518037104008646053246227)
    ·
      refine ⟨15777055656012969079869341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10518037104008646053246227 15777055656012969079869341)
      ·
        refine ⟨5916395871004863404951003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15777055656012969079869341 5916395871004863404951003)
        ·
          refine ⟨8874593806507295107426505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5916395871004863404951003 8874593806507295107426505)
          ·
            refine ⟨6655945354880471330569879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8874593806507295107426505 6655945354880471330569879)
            ·
              refine ⟨9983918032320706995854819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655945354880471330569879 9983918032320706995854819)
              ·
                refine ⟨14975877048481060493782229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9983918032320706995854819 14975877048481060493782229)
                ·
                  refine ⟨350997118323774855323021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14975877048481060493782229 350997118323774855323021)
                  ·
                    refine ⟨131623919371415570746133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350997118323774855323021 131623919371415570746133)
                    ·
                      rfl

theorem cell22_384505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_384505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384505 prefixEnd_384505 := by exact prefixLift 384505
  have htrace : WordTrace (prefixWord ++ tailWord_384505) baseStart_384505 baseEnd_384505 := by
    simpa [prefixWord, tailWord_384505, baseEnd_384505] using wordTrace_append hprefix tailTrace_384505
  have hstable : (prefixWord ++ tailWord_384505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384505).length < 2 ^ (prefixWord ++ tailWord_384505).sum := by decide
  have hdescent : baseEnd_384505 < baseStart_384505 := by decide
  rcases family_descends (prefixWord ++ tailWord_384505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384522 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_384522 : Nat := 118140960795 + 384522 * 2 ^ 59
def prefixEnd_384522 : Nat := 4983230072969 + 3 ^ 40 * 384522 * 2
def baseEnd_384522 : Nat := 131629738818833193071081

theorem tailTrace_384522 : CollatzResearch.WordTrace tailWord_384522 prefixEnd_384522 131629738818833193071081 := by
  unfold tailWord_384522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506167378237484993590955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9349779675299959982909213 3506167378237484993590955)
  ·
    refine ⟨5259251067356227490386433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506167378237484993590955 5259251067356227490386433)
    ·
      refine ⟨3944438300517170617789825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5259251067356227490386433 3944438300517170617789825)
      ·
        refine ⟨2958328725387877963342369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944438300517170617789825 2958328725387877963342369)
        ·
          refine ⟨2218746544040908472506777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2958328725387877963342369 2218746544040908472506777)
          ·
            refine ⟨1664059908030681354380083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2218746544040908472506777 1664059908030681354380083)
            ·
              refine ⟨2496089862046022031570125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664059908030681354380083 2496089862046022031570125)
              ·
                refine ⟨936033698267258261838797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2496089862046022031570125 936033698267258261838797)
                ·
                  refine ⟨351012636850221848189549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936033698267258261838797 351012636850221848189549)
                  ·
                    refine ⟨131629738818833193071081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351012636850221848189549 131629738818833193071081)
                    ·
                      rfl

theorem cell22_384522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_384522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384522 prefixEnd_384522 := by exact prefixLift 384522
  have htrace : WordTrace (prefixWord ++ tailWord_384522) baseStart_384522 baseEnd_384522 := by
    simpa [prefixWord, tailWord_384522, baseEnd_384522] using wordTrace_append hprefix tailTrace_384522
  have hstable : (prefixWord ++ tailWord_384522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384522).length < 2 ^ (prefixWord ++ tailWord_384522).sum := by decide
  have hdescent : baseEnd_384522 < baseStart_384522 := by decide
  rcases family_descends (prefixWord ++ tailWord_384522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384573 : List Nat := [1, 4, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_384573 : Nat := 118140960795 + 384573 * 2 ^ 59
def prefixEnd_384573 : Nat := 4983230072969 + 3 ^ 40 * 384573 * 2
def baseEnd_384573 : Nat := 131647197161086060045925

theorem tailTrace_384573 : CollatzResearch.WordTrace tailWord_384573 prefixEnd_384573 131647197161086060045925 := by
  unfold tailWord_384573
  simp only [CollatzResearch.WordTrace]
  refine ⟨14026529635765175684470373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9351019757176783789646915 14026529635765175684470373)
  ·
    refine ⟨2629974306705970440838195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14026529635765175684470373 2629974306705970440838195)
    ·
      refine ⟨3944961460058955661257293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629974306705970440838195 3944961460058955661257293)
      ·
        refine ⟨1479360547522108372971485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3944961460058955661257293 1479360547522108372971485)
        ·
          refine ⟨554760205320790639864307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1479360547522108372971485 554760205320790639864307)
          ·
            refine ⟨832140307981185959796461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554760205320790639864307 832140307981185959796461)
            ·
              refine ⟨312052615492944734923673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832140307981185959796461 312052615492944734923673)
              ·
                refine ⟨234039461619708551192755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312052615492944734923673 234039461619708551192755)
                ·
                  refine ⟨351059192429562826789133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234039461619708551192755 351059192429562826789133)
                  ·
                    refine ⟨131647197161086060045925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351059192429562826789133 131647197161086060045925)
                    ·
                      rfl

theorem cell22_384573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_384573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384573 prefixEnd_384573 := by exact prefixLift 384573
  have htrace : WordTrace (prefixWord ++ tailWord_384573) baseStart_384573 baseEnd_384573 := by
    simpa [prefixWord, tailWord_384573, baseEnd_384573] using wordTrace_append hprefix tailTrace_384573
  have hstable : (prefixWord ++ tailWord_384573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384573).length < 2 ^ (prefixWord ++ tailWord_384573).sum := by decide
  have hdescent : baseEnd_384573 < baseStart_384573 := by decide
  rcases family_descends (prefixWord ++ tailWord_384573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384599 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 1, 4]
def baseStart_384599 : Nat := 118140960795 + 384599 * 2 ^ 59
def prefixEnd_384599 : Nat := 4983230072969 + 3 ^ 40 * 384599 * 2
def baseEnd_384599 : Nat := 131656097492430658895845

theorem tailTrace_384599 : CollatzResearch.WordTrace tailWord_384599 prefixEnd_384599 131656097492430658895845 := by
  unfold tailWord_384599
  simp only [CollatzResearch.WordTrace]
  refine ⟨14027477933670982124916851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9351651955780654749944567 14027477933670982124916851)
  ·
    refine ⟨21041216900506473187375277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14027477933670982124916851 21041216900506473187375277)
    ·
      refine ⟨7890456337689927445265729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21041216900506473187375277 7890456337689927445265729)
      ·
        refine ⟨5917842253267445583949297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7890456337689927445265729 5917842253267445583949297)
        ·
          refine ⟨4438381689950584187961973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5917842253267445583949297 4438381689950584187961973)
          ·
            refine ⟨416098283432867267621435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4438381689950584187961973 416098283432867267621435)
            ·
              refine ⟨624147425149300901432153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416098283432867267621435 624147425149300901432153)
              ·
                refine ⟨468110568861975676074115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 624147425149300901432153 468110568861975676074115)
                ·
                  refine ⟨702165853292963514111173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468110568861975676074115 702165853292963514111173)
                  ·
                    refine ⟨131656097492430658895845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702165853292963514111173 131656097492430658895845)
                    ·
                      rfl

theorem cell22_384599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_384599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384599 prefixEnd_384599 := by exact prefixLift 384599
  have htrace : WordTrace (prefixWord ++ tailWord_384599) baseStart_384599 baseEnd_384599 := by
    simpa [prefixWord, tailWord_384599, baseEnd_384599] using wordTrace_append hprefix tailTrace_384599
  have hstable : (prefixWord ++ tailWord_384599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384599).length < 2 ^ (prefixWord ++ tailWord_384599).sum := by decide
  have hdescent : baseEnd_384599 < baseStart_384599 := by decide
  rcases family_descends (prefixWord ++ tailWord_384599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384612 : List Nat := [2, 3, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_384612 : Nat := 118140960795 + 384612 * 2 ^ 59
def prefixEnd_384612 : Nat := 4983230072969 + 3 ^ 40 * 384612 * 2
def baseEnd_384612 : Nat := 131660547658102958320805

theorem tailTrace_384612 : CollatzResearch.WordTrace tailWord_384612 prefixEnd_384612 131660547658102958320805 := by
  unfold tailWord_384612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7013976041311942672570045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9351968055082590230093393 7013976041311942672570045)
  ·
    refine ⟨2630241015491978502213767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7013976041311942672570045 2630241015491978502213767)
    ·
      refine ⟨3945361523237967753320651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630241015491978502213767 3945361523237967753320651)
      ·
        refine ⟨5918042284856951629980977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945361523237967753320651 5918042284856951629980977)
        ·
          refine ⟨4438531713642713722485733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5918042284856951629980977 4438531713642713722485733)
          ·
            refine ⟨832224696308008822966075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4438531713642713722485733 832224696308008822966075)
            ·
              refine ⟨1248337044462013234449113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832224696308008822966075 1248337044462013234449113)
              ·
                refine ⟨936252783346509925836835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248337044462013234449113 936252783346509925836835)
                ·
                  refine ⟨1404379175019764888755253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936252783346509925836835 1404379175019764888755253)
                  ·
                    refine ⟨131660547658102958320805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1404379175019764888755253 131660547658102958320805)
                    ·
                      rfl

theorem cell22_384612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_384612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384612 prefixEnd_384612 := by exact prefixLift 384612
  have htrace : WordTrace (prefixWord ++ tailWord_384612) baseStart_384612 baseEnd_384612 := by
    simpa [prefixWord, tailWord_384612, baseEnd_384612] using wordTrace_append hprefix tailTrace_384612
  have hstable : (prefixWord ++ tailWord_384612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384612).length < 2 ^ (prefixWord ++ tailWord_384612).sum := by decide
  have hdescent : baseEnd_384612 < baseStart_384612 := by decide
  rcases family_descends (prefixWord ++ tailWord_384612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384616 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 1, 4]
def baseStart_384616 : Nat := 118140960795 + 384616 * 2 ^ 59
def prefixEnd_384616 : Nat := 4983230072969 + 3 ^ 40 * 384616 * 2
def baseEnd_384616 : Nat := 131661916939848281220793

theorem tailTrace_384616 : CollatzResearch.WordTrace tailWord_384616 prefixEnd_384616 131661916939848281220793 := by
  unfold tailWord_384616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014048987304697014142851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9352065316406262685523801 7014048987304697014142851)
  ·
    refine ⟨10521073480957045521214277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7014048987304697014142851 10521073480957045521214277)
    ·
      refine ⟨1972701277679446035227677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10521073480957045521214277 1972701277679446035227677)
      ·
        refine ⟨739762979129792263210379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1972701277679446035227677 739762979129792263210379)
        ·
          refine ⟨1109644468694688394815569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739762979129792263210379 1109644468694688394815569)
          ·
            refine ⟨832233351521016296111677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109644468694688394815569 832233351521016296111677)
            ·
              refine ⟨312087506820381111041879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832233351521016296111677 312087506820381111041879)
              ·
                refine ⟨468131260230571666562819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312087506820381111041879 468131260230571666562819)
                ·
                  refine ⟨702196890345857499844229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468131260230571666562819 702196890345857499844229)
                  ·
                    refine ⟨131661916939848281220793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702196890345857499844229 131661916939848281220793)
                    ·
                      rfl

theorem cell22_384616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_384616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384616 prefixEnd_384616 := by exact prefixLift 384616
  have htrace : WordTrace (prefixWord ++ tailWord_384616) baseStart_384616 baseEnd_384616 := by
    simpa [prefixWord, tailWord_384616, baseEnd_384616] using wordTrace_append hprefix tailTrace_384616
  have hstable : (prefixWord ++ tailWord_384616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384616).length < 2 ^ (prefixWord ++ tailWord_384616).sum := by decide
  have hdescent : baseEnd_384616 < baseStart_384616 := by decide
  rcases family_descends (prefixWord ++ tailWord_384616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384704 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 5]
def baseStart_384704 : Nat := 118140960795 + 384704 * 2 ^ 59
def prefixEnd_384704 : Nat := 4983230072969 + 3 ^ 40 * 384704 * 2
def baseEnd_384704 : Nat := 43897347046081795006841

theorem tailTrace_384704 : CollatzResearch.WordTrace tailWord_384704 prefixEnd_384704 43897347046081795006841 := by
  unfold tailWord_384704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7015653799145292528744583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9354205065527056704992777 7015653799145292528744583)
  ·
    refine ⟨10523480698717938793116875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7015653799145292528744583 10523480698717938793116875)
    ·
      refine ⟨15785221048076908189675313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10523480698717938793116875 15785221048076908189675313)
      ·
        refine ⟨11838915786057681142256485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15785221048076908189675313 11838915786057681142256485)
        ·
          refine ⟨2219796709885815214173091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11838915786057681142256485 2219796709885815214173091)
          ·
            refine ⟨3329695064828722821259637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219796709885815214173091 3329695064828722821259637)
            ·
              refine ⟨312158912327692764493091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3329695064828722821259637 312158912327692764493091)
              ·
                refine ⟨468238368491539146739637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312158912327692764493091 468238368491539146739637)
                ·
                  refine ⟨43897347046081795006841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468238368491539146739637 43897347046081795006841)
                  ·
                    rfl

theorem cell22_384704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 5].length) (baseStart_384704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384704 prefixEnd_384704 := by exact prefixLift 384704
  have htrace : WordTrace (prefixWord ++ tailWord_384704) baseStart_384704 baseEnd_384704 := by
    simpa [prefixWord, tailWord_384704, baseEnd_384704] using wordTrace_append hprefix tailTrace_384704
  have hstable : (prefixWord ++ tailWord_384704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384704).length < 2 ^ (prefixWord ++ tailWord_384704).sum := by decide
  have hdescent : baseEnd_384704 < baseStart_384704 := by decide
  rcases family_descends (prefixWord ++ tailWord_384704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384749 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 6]
def baseStart_384749 : Nat := 118140960795 + 384749 * 2 ^ 59
def prefixEnd_384749 : Nat := 4983230072969 + 3 ^ 40 * 384749 * 2
def baseEnd_384749 : Nat := 43902481852626755881795

theorem tailTrace_384749 : CollatzResearch.WordTrace tailWord_384749 prefixEnd_384749 43902481852626755881795 := by
  unfold tailWord_384749
  simp only [CollatzResearch.WordTrace]
  refine ⟨14032948883127557742877301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9355299255418371828584867 14032948883127557742877301)
  ·
    refine ⟨1315588957793208538394747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14032948883127557742877301 1315588957793208538394747)
    ·
      refine ⟨1973383436689812807592121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315588957793208538394747 1973383436689812807592121)
      ·
        refine ⟨1480037577517359605694091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1973383436689812807592121 1480037577517359605694091)
        ·
          refine ⟨2220056366276039408541137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480037577517359605694091 2220056366276039408541137)
          ·
            refine ⟨1665042274707029556405853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2220056366276039408541137 1665042274707029556405853)
            ·
              refine ⟨624390853015136083652195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1665042274707029556405853 624390853015136083652195)
              ·
                refine ⟨936586279522704125478293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624390853015136083652195 936586279522704125478293)
                ·
                  refine ⟨43902481852626755881795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 936586279522704125478293 43902481852626755881795)
                  ·
                    rfl

theorem cell22_384749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_384749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384749 prefixEnd_384749 := by exact prefixLift 384749
  have htrace : WordTrace (prefixWord ++ tailWord_384749) baseStart_384749 baseEnd_384749 := by
    simpa [prefixWord, tailWord_384749, baseEnd_384749] using wordTrace_append hprefix tailTrace_384749
  have hstable : (prefixWord ++ tailWord_384749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384749).length < 2 ^ (prefixWord ++ tailWord_384749).sum := by decide
  have hdescent : baseEnd_384749 < baseStart_384749 := by decide
  rcases family_descends (prefixWord ++ tailWord_384749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384762 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_384762 : Nat := 118140960795 + 384762 * 2 ^ 59
def prefixEnd_384762 : Nat := 4983230072969 + 3 ^ 40 * 384762 * 2
def baseEnd_384762 : Nat := 131711895723552567070345

theorem tailTrace_384762 : CollatzResearch.WordTrace tailWord_384762 prefixEnd_384762 131711895723552567070345 := by
  unfold tailWord_384762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508355758020115240775135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9355615354720307308733693 3508355758020115240775135)
  ·
    refine ⟨5262533637030172861162703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3508355758020115240775135 5262533637030172861162703)
    ·
      refine ⟨7893800455545259291744055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262533637030172861162703 7893800455545259291744055)
      ·
        refine ⟨11840700683317888937616083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7893800455545259291744055 11840700683317888937616083)
        ·
          refine ⟨17761051024976833406424125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840700683317888937616083 17761051024976833406424125)
          ·
            refine ⟨6660394134366312527409047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17761051024976833406424125 6660394134366312527409047)
            ·
              refine ⟨9990591201549468791113571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660394134366312527409047 9990591201549468791113571)
              ·
                refine ⟨14985886802324203186670357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9990591201549468791113571 14985886802324203186670357)
                ·
                  refine ⟨702463443858947024375173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14985886802324203186670357 702463443858947024375173)
                  ·
                    refine ⟨131711895723552567070345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702463443858947024375173 131711895723552567070345)
                    ·
                      rfl

theorem cell22_384762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_384762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384762 prefixEnd_384762 := by exact prefixLift 384762
  have htrace : WordTrace (prefixWord ++ tailWord_384762) baseStart_384762 baseEnd_384762 := by
    simpa [prefixWord, tailWord_384762, baseEnd_384762] using wordTrace_append hprefix tailTrace_384762
  have hstable : (prefixWord ++ tailWord_384762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384762).length < 2 ^ (prefixWord ++ tailWord_384762).sum := by decide
  have hdescent : baseEnd_384762 < baseStart_384762 := by decide
  rcases family_descends (prefixWord ++ tailWord_384762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384826 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_384826 : Nat := 118140960795 + 384826 * 2 ^ 59
def prefixEnd_384826 : Nat := 4983230072969 + 3 ^ 40 * 384826 * 2
def baseEnd_384826 : Nat := 131733804231477733470149

theorem tailTrace_384826 : CollatzResearch.WordTrace tailWord_384826 prefixEnd_384826 131733804231477733470149 := by
  unfold tailWord_384826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3508939325962149973357583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9357171535899066595620221 3508939325962149973357583)
  ·
    refine ⟨5263408988943224960036375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3508939325962149973357583 5263408988943224960036375)
    ·
      refine ⟨7895113483414837440054563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263408988943224960036375 7895113483414837440054563)
      ·
        refine ⟨11842670225122256160081845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7895113483414837440054563 11842670225122256160081845)
        ·
          refine ⟨1110250333605211515007673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11842670225122256160081845 1110250333605211515007673)
          ·
            refine ⟨832687750203908636255755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110250333605211515007673 832687750203908636255755)
            ·
              refine ⟨1249031625305862954383633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832687750203908636255755 1249031625305862954383633)
              ·
                refine ⟨936773718979397215787725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249031625305862954383633 936773718979397215787725)
                ·
                  refine ⟨351290144617273955920397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936773718979397215787725 351290144617273955920397)
                  ·
                    refine ⟨131733804231477733470149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351290144617273955920397 131733804231477733470149)
                    ·
                      rfl

theorem cell22_384826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_384826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384826 prefixEnd_384826 := by exact prefixLift 384826
  have htrace : WordTrace (prefixWord ++ tailWord_384826) baseStart_384826 baseEnd_384826 := by
    simpa [prefixWord, tailWord_384826, baseEnd_384826] using wordTrace_append hprefix tailTrace_384826
  have hstable : (prefixWord ++ tailWord_384826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384826).length < 2 ^ (prefixWord ++ tailWord_384826).sum := by decide
  have hdescent : baseEnd_384826 < baseStart_384826 := by decide
  rcases family_descends (prefixWord ++ tailWord_384826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384837 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_384837 : Nat := 118140960795 + 384837 * 2 ^ 59
def prefixEnd_384837 : Nat := 4983230072969 + 3 ^ 40 * 384837 * 2
def baseEnd_384837 : Nat := 131737569756277371445115

theorem tailTrace_384837 : CollatzResearch.WordTrace tailWord_384837 prefixEnd_384837 131737569756277371445115 := by
  unfold tailWord_384837
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036158506808748772080765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9357439004539165848053843 14036158506808748772080765)
  ·
    refine ⟨5263559440053280789530287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14036158506808748772080765 5263559440053280789530287)
    ·
      refine ⟨7895339160079921184295431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263559440053280789530287 7895339160079921184295431)
      ·
        refine ⟨11843008740119881776443147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7895339160079921184295431 11843008740119881776443147)
        ·
          refine ⟨17764513110179822664664721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843008740119881776443147 17764513110179822664664721)
          ·
            refine ⟨13323384832634866998498541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17764513110179822664664721 13323384832634866998498541)
            ·
              refine ⟨4996269312238075124436953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13323384832634866998498541 4996269312238075124436953)
              ·
                refine ⟨3747201984178556343327715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4996269312238075124436953 3747201984178556343327715)
                ·
                  refine ⟨5620802976267834514991573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3747201984178556343327715 5620802976267834514991573)
                  ·
                    refine ⟨131737569756277371445115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5620802976267834514991573 131737569756277371445115)
                    ·
                      rfl

theorem cell22_384837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_384837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384837 prefixEnd_384837 := by exact prefixLift 384837
  have htrace : WordTrace (prefixWord ++ tailWord_384837) baseStart_384837 baseEnd_384837 := by
    simpa [prefixWord, tailWord_384837, baseEnd_384837] using wordTrace_append hprefix tailTrace_384837
  have hstable : (prefixWord ++ tailWord_384837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384837).length < 2 ^ (prefixWord ++ tailWord_384837).sum := by decide
  have hdescent : baseEnd_384837 < baseStart_384837 := by decide
  rcases family_descends (prefixWord ++ tailWord_384837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384991 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 5]
def baseStart_384991 : Nat := 118140960795 + 384991 * 2 ^ 59
def prefixEnd_384991 : Nat := 4983230072969 + 3 ^ 40 * 384991 * 2
def baseEnd_384991 : Nat := 43930095701157434364881

theorem tailTrace_384991 : CollatzResearch.WordTrace tailWord_384991 prefixEnd_384991 43930095701157434364881 := by
  unfold tailWord_384991
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041775348250833073186827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9361183565500555382124551 14041775348250833073186827)
  ·
    refine ⟨21062663022376249609780241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14041775348250833073186827 21062663022376249609780241)
    ·
      refine ⟨15796997266782187207335181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21062663022376249609780241 15796997266782187207335181)
      ·
        refine ⟨5923873975043320202750693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15796997266782187207335181 5923873975043320202750693)
        ·
          refine ⟨1110726370320622538015755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5923873975043320202750693 1110726370320622538015755)
          ·
            refine ⟨1666089555480933807023633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110726370320622538015755 1666089555480933807023633)
            ·
              refine ⟨1249567166610700355267725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666089555480933807023633 1249567166610700355267725)
              ·
                refine ⟨468587687479012633225397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1249567166610700355267725 468587687479012633225397)
                ·
                  refine ⟨43930095701157434364881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468587687479012633225397 43930095701157434364881)
                  ·
                    rfl

theorem cell22_384991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 5].length) (baseStart_384991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_384991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_384991 prefixEnd_384991 := by exact prefixLift 384991
  have htrace : WordTrace (prefixWord ++ tailWord_384991) baseStart_384991 baseEnd_384991 := by
    simpa [prefixWord, tailWord_384991, baseEnd_384991] using wordTrace_append hprefix tailTrace_384991
  have hstable : (prefixWord ++ tailWord_384991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384991).length < 2 ^ (prefixWord ++ tailWord_384991).sum := by decide
  have hdescent : baseEnd_384991 < baseStart_384991 := by decide
  rcases family_descends (prefixWord ++ tailWord_384991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385036 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_385036 : Nat := 118140960795 + 385036 * 2 ^ 59
def prefixEnd_385036 : Nat := 4983230072969 + 3 ^ 40 * 385036 * 2
def baseEnd_385036 : Nat := 43935230507702395239835

theorem tailTrace_385036 : CollatzResearch.WordTrace tailWord_385036 prefixEnd_385036 43935230507702395239835 := by
  unfold tailWord_385036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7021708316543902879287481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9362277755391870505716641 7021708316543902879287481)
  ·
    refine ⟨5266281237407927159465611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7021708316543902879287481 5266281237407927159465611)
    ·
      refine ⟨7899421856111890739198417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266281237407927159465611 7899421856111890739198417)
      ·
        refine ⟨5924566392083918054398813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7899421856111890739198417 5924566392083918054398813)
        ·
          refine ⟨2221712397031469270399555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5924566392083918054398813 2221712397031469270399555)
          ·
            refine ⟨3332568595547203905599333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221712397031469270399555 3332568595547203905599333)
            ·
              refine ⟨624856611665100732299875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3332568595547203905599333 624856611665100732299875)
              ·
                refine ⟨937284917497651098449813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624856611665100732299875 937284917497651098449813)
                ·
                  refine ⟨43935230507702395239835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 937284917497651098449813 43935230507702395239835)
                  ·
                    rfl

theorem cell22_385036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_385036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385036 prefixEnd_385036 := by exact prefixLift 385036
  have htrace : WordTrace (prefixWord ++ tailWord_385036) baseStart_385036 baseEnd_385036 := by
    simpa [prefixWord, tailWord_385036, baseEnd_385036] using wordTrace_append hprefix tailTrace_385036
  have hstable : (prefixWord ++ tailWord_385036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385036).length < 2 ^ (prefixWord ++ tailWord_385036).sum := by decide
  have hdescent : baseEnd_385036 < baseStart_385036 := by decide
  rcases family_descends (prefixWord ++ tailWord_385036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385070 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_385070 : Nat := 118140960795 + 385070 * 2 ^ 59
def prefixEnd_385070 : Nat := 4983230072969 + 3 ^ 40 * 385070 * 2
def baseEnd_385070 : Nat := 43939110139314143456467

theorem tailTrace_385070 : CollatzResearch.WordTrace tailWord_385070 prefixEnd_385070 43939110139314143456467 := by
  unfold tailWord_385070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755582089370578695664083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9363104476643086376875109 1755582089370578695664083)
  ·
    refine ⟨2633373134055868043496125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1755582089370578695664083 2633373134055868043496125)
    ·
      refine ⟨987514925270950516311047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2633373134055868043496125 987514925270950516311047)
      ·
        refine ⟨1481272387906425774466571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987514925270950516311047 1481272387906425774466571)
        ·
          refine ⟨2221908581859638661699857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1481272387906425774466571 2221908581859638661699857)
          ·
            refine ⟨1666431436394728996274893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2221908581859638661699857 1666431436394728996274893)
            ·
              refine ⟨624911788648023373603085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1666431436394728996274893 624911788648023373603085)
              ·
                refine ⟨234341920743008765101157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 624911788648023373603085 234341920743008765101157)
                ·
                  refine ⟨43939110139314143456467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 234341920743008765101157 43939110139314143456467)
                  ·
                    rfl

theorem cell22_385070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_385070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385070 prefixEnd_385070 := by exact prefixLift 385070
  have htrace : WordTrace (prefixWord ++ tailWord_385070) baseStart_385070 baseEnd_385070 := by
    simpa [prefixWord, tailWord_385070, baseEnd_385070] using wordTrace_append hprefix tailTrace_385070
  have hstable : (prefixWord ++ tailWord_385070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385070).length < 2 ^ (prefixWord ++ tailWord_385070).sum := by decide
  have hdescent : baseEnd_385070 < baseStart_385070 := by decide
  rcases family_descends (prefixWord ++ tailWord_385070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385102 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_385102 : Nat := 118140960795 + 385102 * 2 ^ 59
def prefixEnd_385102 : Nat := 4983230072969 + 3 ^ 40 * 385102 * 2
def baseEnd_385102 : Nat := 131828284671905013569303

theorem tailTrace_385102 : CollatzResearch.WordTrace tailWord_385102 prefixEnd_385102 131828284671905013569303 := by
  unfold tailWord_385102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1755727981356087378809695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9363882567232466020318373 1755727981356087378809695)
  ·
    refine ⟨2633591972034131068214543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1755727981356087378809695 2633591972034131068214543)
    ·
      refine ⟨3950387958051196602321815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2633591972034131068214543 3950387958051196602321815)
      ·
        refine ⟨5925581937076794903482723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950387958051196602321815 5925581937076794903482723)
        ·
          refine ⟨8888372905615192355224085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5925581937076794903482723 8888372905615192355224085)
          ·
            refine ⟨416642479950712141651129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8888372905615192355224085 416642479950712141651129)
            ·
              refine ⟨312481859963034106238347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416642479950712141651129 312481859963034106238347)
              ·
                refine ⟨468722789944551159357521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312481859963034106238347 468722789944551159357521)
                ·
                  refine ⟨351542092458413369518141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468722789944551159357521 351542092458413369518141)
                  ·
                    refine ⟨131828284671905013569303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351542092458413369518141 131828284671905013569303)
                    ·
                      rfl

theorem cell22_385102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_385102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385102 prefixEnd_385102 := by exact prefixLift 385102
  have htrace : WordTrace (prefixWord ++ tailWord_385102) baseStart_385102 baseEnd_385102 := by
    simpa [prefixWord, tailWord_385102, baseEnd_385102] using wordTrace_append hprefix tailTrace_385102
  have hstable : (prefixWord ++ tailWord_385102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385102).length < 2 ^ (prefixWord ++ tailWord_385102).sum := by decide
  have hdescent : baseEnd_385102 < baseStart_385102 := by decide
  rcases family_descends (prefixWord ++ tailWord_385102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385143 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 5]
def baseStart_385143 : Nat := 118140960795 + 385143 * 2 ^ 59
def prefixEnd_385143 : Nat := 4983230072969 + 3 ^ 40 * 385143 * 2
def baseEnd_385143 : Nat := 43947439936598191098059

theorem tailTrace_385143 : CollatzResearch.WordTrace tailWord_385143 prefixEnd_385143 43947439936598191098059 := by
  unfold tailWord_385143
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047319243700163032720083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9364879495800108688480055 14047319243700163032720083)
  ·
    refine ⟨21070978865550244549080125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14047319243700163032720083 21070978865550244549080125)
    ·
      refine ⟨7901617074581341705905047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21070978865550244549080125 7901617074581341705905047)
      ·
        refine ⟨11852425611872012558857571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7901617074581341705905047 11852425611872012558857571)
        ·
          refine ⟨17778638417808018838286357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11852425611872012558857571 17778638417808018838286357)
          ·
            refine ⟨833373675834750883044673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17778638417808018838286357 833373675834750883044673)
            ·
              refine ⟨625030256876063162283505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833373675834750883044673 625030256876063162283505)
              ·
                refine ⟨468772692657047371712629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625030256876063162283505 468772692657047371712629)
                ·
                  refine ⟨43947439936598191098059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468772692657047371712629 43947439936598191098059)
                  ·
                    rfl

theorem cell22_385143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 5].length) (baseStart_385143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385143 prefixEnd_385143 := by exact prefixLift 385143
  have htrace : WordTrace (prefixWord ++ tailWord_385143) baseStart_385143 baseEnd_385143 := by
    simpa [prefixWord, tailWord_385143, baseEnd_385143] using wordTrace_append hprefix tailTrace_385143
  have hstable : (prefixWord ++ tailWord_385143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385143).length < 2 ^ (prefixWord ++ tailWord_385143).sum := by decide
  have hdescent : baseEnd_385143 < baseStart_385143 := by decide
  rcases family_descends (prefixWord ++ tailWord_385143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385173 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_385173 : Nat := 118140960795 + 385173 * 2 ^ 59
def prefixEnd_385173 : Nat := 4983230072969 + 3 ^ 40 * 385173 * 2
def baseEnd_385173 : Nat := 131852589422884495044085

theorem tailTrace_385173 : CollatzResearch.WordTrace tailWord_385173 prefixEnd_385173 131852589422884495044085 := by
  unfold tailWord_385173
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048413433591478156312173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9365608955727652104208115 14048413433591478156312173)
  ·
    refine ⟨5268155037596804308617065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14048413433591478156312173 5268155037596804308617065)
    ·
      refine ⟨3951116278197603231462799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5268155037596804308617065 3951116278197603231462799)
      ·
        refine ⟨5926674417296404847194199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951116278197603231462799 5926674417296404847194199)
        ·
          refine ⟨8890011625944607270791299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926674417296404847194199 8890011625944607270791299)
          ·
            refine ⟨13335017438916910906186949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890011625944607270791299 13335017438916910906186949)
            ·
              refine ⟨2500315769796920794910053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13335017438916910906186949 2500315769796920794910053)
              ·
                refine ⟨468809206836922649045635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2500315769796920794910053 468809206836922649045635)
                ·
                  refine ⟨703213810255383973568453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468809206836922649045635 703213810255383973568453)
                  ·
                    refine ⟨131852589422884495044085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 703213810255383973568453 131852589422884495044085)
                    ·
                      rfl

theorem cell22_385173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_385173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385173 prefixEnd_385173 := by exact prefixLift 385173
  have htrace : WordTrace (prefixWord ++ tailWord_385173) baseStart_385173 baseEnd_385173 := by
    simpa [prefixWord, tailWord_385173, baseEnd_385173] using wordTrace_append hprefix tailTrace_385173
  have hstable : (prefixWord ++ tailWord_385173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385173).length < 2 ^ (prefixWord ++ tailWord_385173).sum := by decide
  have hdescent : baseEnd_385173 < baseStart_385173 := by decide
  rcases family_descends (prefixWord ++ tailWord_385173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385194 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 5]
def baseStart_385194 : Nat := 118140960795 + 385194 * 2 ^ 59
def prefixEnd_385194 : Nat := 4983230072969 + 3 ^ 40 * 385194 * 2
def baseEnd_385194 : Nat := 43953259384015813423007

theorem tailTrace_385194 : CollatzResearch.WordTrace tailWord_385194 prefixEnd_385194 43953259384015813423007 := by
  unfold tailWord_385194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512294841628849685706659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9366119577676932495217757 3512294841628849685706659)
  ·
    refine ⟨5268442262443274528559989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3512294841628849685706659 5268442262443274528559989)
    ·
      refine ⟨493916462104056987052499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5268442262443274528559989 493916462104056987052499)
      ·
        refine ⟨740874693156085480578749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493916462104056987052499 740874693156085480578749)
        ·
          refine ⟨277828009933532055217031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740874693156085480578749 277828009933532055217031)
          ·
            refine ⟨416742014900298082825547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277828009933532055217031 416742014900298082825547)
            ·
              refine ⟨625113022350447124238321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416742014900298082825547 625113022350447124238321)
              ·
                refine ⟨468834766762835343178741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625113022350447124238321 468834766762835343178741)
                ·
                  refine ⟨43953259384015813423007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 468834766762835343178741 43953259384015813423007)
                  ·
                    rfl

theorem cell22_385194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_385194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385194 prefixEnd_385194 := by exact prefixLift 385194
  have htrace : WordTrace (prefixWord ++ tailWord_385194) baseStart_385194 baseEnd_385194 := by
    simpa [prefixWord, tailWord_385194, baseEnd_385194] using wordTrace_append hprefix tailTrace_385194
  have hstable : (prefixWord ++ tailWord_385194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385194).length < 2 ^ (prefixWord ++ tailWord_385194).sum := by decide
  have hdescent : baseEnd_385194 < baseStart_385194 := by decide
  rcases family_descends (prefixWord ++ tailWord_385194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385220 : List Nat := [2, 3, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_385220 : Nat := 118140960795 + 385220 * 2 ^ 59
def prefixEnd_385220 : Nat := 4983230072969 + 3 ^ 40 * 385220 * 2
def baseEnd_385220 : Nat := 131868678483392039118941

theorem tailTrace_385220 : CollatzResearch.WordTrace tailWord_385220 prefixEnd_385220 131868678483392039118941 := by
  unfold tailWord_385220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025063832210602591636557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9366751776280803455515409 7025063832210602591636557)
  ·
    refine ⟨2634398937078975971863709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7025063832210602591636557 2634398937078975971863709)
    ·
      refine ⟨987899601404615989448891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2634398937078975971863709 987899601404615989448891)
      ·
        refine ⟨1481849402106923984173337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987899601404615989448891 1481849402106923984173337)
        ·
          refine ⟨1111387051580192988130003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481849402106923984173337 1111387051580192988130003)
          ·
            refine ⟨1667080577370289482195005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111387051580192988130003 1667080577370289482195005)
            ·
              refine ⟨625155216513858555823127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1667080577370289482195005 625155216513858555823127)
              ·
                refine ⟨937732824770787833734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625155216513858555823127 937732824770787833734691)
                ·
                  refine ⟨1406599237156181750602037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937732824770787833734691 1406599237156181750602037)
                  ·
                    refine ⟨131868678483392039118941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1406599237156181750602037 131868678483392039118941)
                    ·
                      rfl

theorem cell22_385220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_385220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385220 prefixEnd_385220 := by exact prefixLift 385220
  have htrace : WordTrace (prefixWord ++ tailWord_385220) baseStart_385220 baseEnd_385220 := by
    simpa [prefixWord, tailWord_385220, baseEnd_385220] using wordTrace_append hprefix tailTrace_385220
  have hstable : (prefixWord ++ tailWord_385220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385220).length < 2 ^ (prefixWord ++ tailWord_385220).sum := by decide
  have hdescent : baseEnd_385220 < baseStart_385220 := by decide
  rcases family_descends (prefixWord ++ tailWord_385220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385231 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_385231 : Nat := 118140960795 + 385231 * 2 ^ 59
def prefixEnd_385231 : Nat := 4983230072969 + 3 ^ 40 * 385231 * 2
def baseEnd_385231 : Nat := 131872444008191677093907

theorem tailTrace_385231 : CollatzResearch.WordTrace tailWord_385231 prefixEnd_385231 131872444008191677093907 := by
  unfold tailWord_385231
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050528867381354061923547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9367019244920902707949031 14050528867381354061923547)
  ·
    refine ⟨21075793301072031092885321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14050528867381354061923547 21075793301072031092885321)
    ·
      refine ⟨15806844975804023319663991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21075793301072031092885321 15806844975804023319663991)
      ·
        refine ⟨23710267463706034979495987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15806844975804023319663991 23710267463706034979495987)
        ·
          refine ⟨35565401195559052469243981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23710267463706034979495987 35565401195559052469243981)
          ·
            refine ⟨13337025448334644675966493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35565401195559052469243981 13337025448334644675966493)
            ·
              refine ⟨5001384543125491753487435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13337025448334644675966493 5001384543125491753487435)
              ·
                refine ⟨7502076814688237630231153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001384543125491753487435 7502076814688237630231153)
                ·
                  refine ⟨5626557611016178222673365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7502076814688237630231153 5626557611016178222673365)
                  ·
                    refine ⟨131872444008191677093907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5626557611016178222673365 131872444008191677093907)
                    ·
                      rfl

theorem cell22_385231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_385231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385231 prefixEnd_385231 := by exact prefixLift 385231
  have htrace : WordTrace (prefixWord ++ tailWord_385231) baseStart_385231 baseEnd_385231 := by
    simpa [prefixWord, tailWord_385231, baseEnd_385231] using wordTrace_append hprefix tailTrace_385231
  have hstable : (prefixWord ++ tailWord_385231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385231).length < 2 ^ (prefixWord ++ tailWord_385231).sum := by decide
  have hdescent : baseEnd_385231 < baseStart_385231 := by decide
  rcases family_descends (prefixWord ++ tailWord_385231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385233 : List Nat := [1, 2, 2, 1, 2, 2, 6, 6]
def baseStart_385233 : Nat := 118140960795 + 385233 * 2 ^ 59
def prefixEnd_385233 : Nat := 4983230072969 + 3 ^ 40 * 385233 * 2
def baseEnd_385233 : Nat := 14652569849896037615989

theorem tailTrace_385233 : CollatzResearch.WordTrace tailWord_385233 prefixEnd_385233 14652569849896037615989 := by
  unfold tailWord_385233
  simp only [CollatzResearch.WordTrace]
  refine ⟨14050601813374108403496353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9367067875582738935664235 14050601813374108403496353)
  ·
    refine ⟨10537951360030581302622265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14050601813374108403496353 10537951360030581302622265)
    ·
      refine ⟨7903463520022935976966699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10537951360030581302622265 7903463520022935976966699)
      ·
        refine ⟨11855195280034403965450049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903463520022935976966699 11855195280034403965450049)
        ·
          refine ⟨8891396460025802974087537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11855195280034403965450049 8891396460025802974087537)
          ·
            refine ⟨6668547345019352230565653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8891396460025802974087537 6668547345019352230565653)
            ·
              refine ⟨312588156797782135807765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6668547345019352230565653 312588156797782135807765)
              ·
                refine ⟨14652569849896037615989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 312588156797782135807765 14652569849896037615989)
                ·
                  rfl

theorem cell22_385233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 6].length) (baseStart_385233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385233 prefixEnd_385233 := by exact prefixLift 385233
  have htrace : WordTrace (prefixWord ++ tailWord_385233) baseStart_385233 baseEnd_385233 := by
    simpa [prefixWord, tailWord_385233, baseEnd_385233] using wordTrace_append hprefix tailTrace_385233
  have hstable : (prefixWord ++ tailWord_385233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385233).length < 2 ^ (prefixWord ++ tailWord_385233).sum := by decide
  have hdescent : baseEnd_385233 < baseStart_385233 := by decide
  rcases family_descends (prefixWord ++ tailWord_385233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385265 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_385265 : Nat := 118140960795 + 385265 * 2 ^ 59
def prefixEnd_385265 : Nat := 4983230072969 + 3 ^ 40 * 385265 * 2
def baseEnd_385265 : Nat := 131884082903026921743803

theorem tailTrace_385265 : CollatzResearch.WordTrace tailWord_385265 prefixEnd_385265 131884082903026921743803 := by
  unfold tailWord_385265
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051768949258177868661249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9367845966172118579107499 14051768949258177868661249)
  ·
    refine ⟨10538826711943633401495937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14051768949258177868661249 10538826711943633401495937)
    ·
      refine ⟨7904120033957725051121953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538826711943633401495937 7904120033957725051121953)
      ·
        refine ⟨5928090025468293788341465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904120033957725051121953 5928090025468293788341465)
        ·
          refine ⟨4446067519101220341256099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5928090025468293788341465 4446067519101220341256099)
          ·
            refine ⟨6669101278651830511884149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446067519101220341256099 6669101278651830511884149)
            ·
              refine ⟨625228244873609110489139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6669101278651830511884149 625228244873609110489139)
              ·
                refine ⟨937842367310413665733709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625228244873609110489139 937842367310413665733709)
                ·
                  refine ⟨351690887741405124650141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 937842367310413665733709 351690887741405124650141)
                  ·
                    refine ⟨131884082903026921743803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351690887741405124650141 131884082903026921743803)
                    ·
                      rfl

theorem cell22_385265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_385265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385265 prefixEnd_385265 := by exact prefixLift 385265
  have htrace : WordTrace (prefixWord ++ tailWord_385265) baseStart_385265 baseEnd_385265 := by
    simpa [prefixWord, tailWord_385265, baseEnd_385265] using wordTrace_append hprefix tailTrace_385265
  have hstable : (prefixWord ++ tailWord_385265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385265).length < 2 ^ (prefixWord ++ tailWord_385265).sum := by decide
  have hdescent : baseEnd_385265 < baseStart_385265 := by decide
  rcases family_descends (prefixWord ++ tailWord_385265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385316 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_385316 : Nat := 118140960795 + 385316 * 2 ^ 59
def prefixEnd_385316 : Nat := 4983230072969 + 3 ^ 40 * 385316 * 2
def baseEnd_385316 : Nat := 131901541245279788718647

theorem tailTrace_385316 : CollatzResearch.WordTrace tailWord_385316 prefixEnd_385316 131901541245279788718647 := by
  unfold tailWord_385316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026814536036706789383901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9369086048048942385845201 7026814536036706789383901)
  ·
    refine ⟨2635055451013765046018963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7026814536036706789383901 2635055451013765046018963)
    ·
      refine ⟨3952583176520647569028445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635055451013765046018963 3952583176520647569028445)
      ·
        refine ⟨1482218691195242838385667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3952583176520647569028445 1482218691195242838385667)
        ·
          refine ⟨2223328036792864257578501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482218691195242838385667 2223328036792864257578501)
          ·
            refine ⟨416874006898662048295969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2223328036792864257578501 416874006898662048295969)
            ·
              refine ⟨312655505173996536221977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416874006898662048295969 312655505173996536221977)
              ·
                refine ⟨234491628880497402166483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 312655505173996536221977 234491628880497402166483)
                ·
                  refine ⟨351737443320746103249725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234491628880497402166483 351737443320746103249725)
                  ·
                    refine ⟨131901541245279788718647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351737443320746103249725 131901541245279788718647)
                    ·
                      rfl

theorem cell22_385316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_385316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385316 prefixEnd_385316 := by exact prefixLift 385316
  have htrace : WordTrace (prefixWord ++ tailWord_385316) baseStart_385316 baseEnd_385316 := by
    simpa [prefixWord, tailWord_385316, baseEnd_385316] using wordTrace_append hprefix tailTrace_385316
  have hstable : (prefixWord ++ tailWord_385316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385316).length < 2 ^ (prefixWord ++ tailWord_385316).sum := by decide
  have hdescent : baseEnd_385316 < baseStart_385316 := by decide
  rcases family_descends (prefixWord ++ tailWord_385316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385389 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_385389 : Nat := 118140960795 + 385389 * 2 ^ 59
def prefixEnd_385389 : Nat := 4983230072969 + 3 ^ 40 * 385389 * 2
def baseEnd_385389 : Nat := 131926530637131931643423

theorem tailTrace_385389 : CollatzResearch.WordTrace tailWord_385389 prefixEnd_385389 131926530637131931643423 := by
  unfold tailWord_385389
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056291600808947046175221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9370861067205964697450147 14056291600808947046175221)
  ·
    refine ⟨1317777337575838785578927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14056291600808947046175221 1317777337575838785578927)
    ·
      refine ⟨1976666006363758178368391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317777337575838785578927 1976666006363758178368391)
      ·
        refine ⟨2964999009545637267552587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976666006363758178368391 2964999009545637267552587)
        ·
          refine ⟨4447498514318455901328881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964999009545637267552587 4447498514318455901328881)
          ·
            refine ⟨3335623885738841925996661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4447498514318455901328881 3335623885738841925996661)
            ·
              refine ⟨312714739288016430562187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3335623885738841925996661 312714739288016430562187)
              ·
                refine ⟨469072108932024645843281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312714739288016430562187 469072108932024645843281)
                ·
                  refine ⟨351804081699018484382461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469072108932024645843281 351804081699018484382461)
                  ·
                    refine ⟨131926530637131931643423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351804081699018484382461 131926530637131931643423)
                    ·
                      rfl

theorem cell22_385389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_385389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385389 prefixEnd_385389 := by exact prefixLift 385389
  have htrace : WordTrace (prefixWord ++ tailWord_385389) baseStart_385389 baseEnd_385389 := by
    simpa [prefixWord, tailWord_385389, baseEnd_385389] using wordTrace_append hprefix tailTrace_385389
  have hstable : (prefixWord ++ tailWord_385389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385389).length < 2 ^ (prefixWord ++ tailWord_385389).sum := by decide
  have hdescent : baseEnd_385389 < baseStart_385389 := by decide
  rcases family_descends (prefixWord ++ tailWord_385389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385434 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_385434 : Nat := 118140960795 + 385434 * 2 ^ 59
def prefixEnd_385434 : Nat := 4983230072969 + 3 ^ 40 * 385434 * 2
def baseEnd_385434 : Nat := 131941935056766814268285

theorem tailTrace_385434 : CollatzResearch.WordTrace tailWord_385434 prefixEnd_385434 131941935056766814268285 := by
  unfold tailWord_385434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514483221411479932890839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9371955257097279821042237 3514483221411479932890839)
  ·
    refine ⟨5271724832117219899336259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514483221411479932890839 5271724832117219899336259)
    ·
      refine ⟨7907587248175829849004389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5271724832117219899336259 7907587248175829849004389)
      ·
        refine ⟨1482672609032968096688323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7907587248175829849004389 1482672609032968096688323)
        ·
          refine ⟨2224008913549452145032485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482672609032968096688323 2224008913549452145032485)
          ·
            refine ⟨417001671290522277193591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2224008913549452145032485 417001671290522277193591)
            ·
              refine ⟨625502506935783415790387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417001671290522277193591 625502506935783415790387)
              ·
                refine ⟨938253760403675123685581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625502506935783415790387 938253760403675123685581)
                ·
                  refine ⟨351845160151378171382093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 938253760403675123685581 351845160151378171382093)
                  ·
                    refine ⟨131941935056766814268285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351845160151378171382093 131941935056766814268285)
                    ·
                      rfl

theorem cell22_385434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_385434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385434 prefixEnd_385434 := by exact prefixLift 385434
  have htrace : WordTrace (prefixWord ++ tailWord_385434) baseStart_385434 baseEnd_385434 := by
    simpa [prefixWord, tailWord_385434, baseEnd_385434] using wordTrace_append hprefix tailTrace_385434
  have hstable : (prefixWord ++ tailWord_385434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385434).length < 2 ^ (prefixWord ++ tailWord_385434).sum := by decide
  have hdescent : baseEnd_385434 < baseStart_385434 := by decide
  rcases family_descends (prefixWord ++ tailWord_385434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385447 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 5]
def baseStart_385447 : Nat := 118140960795 + 385447 * 2 ^ 59
def prefixEnd_385447 : Nat := 4983230072969 + 3 ^ 40 * 385447 * 2
def baseEnd_385447 : Nat := 43982128407479704564415

theorem tailTrace_385447 : CollatzResearch.WordTrace tailWord_385447 prefixEnd_385447 43982128407479704564415 := by
  unfold tailWord_385447
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058407034598822951786595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9372271356399215301191063 14058407034598822951786595)
  ·
    refine ⟨21087610551898234427679893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058407034598822951786595 21087610551898234427679893)
    ·
      refine ⟨988481744620229738797495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21087610551898234427679893 988481744620229738797495)
      ·
        refine ⟨1482722616930344608196243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988481744620229738797495 1482722616930344608196243)
        ·
          refine ⟨2224083925395516912294365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482722616930344608196243 2224083925395516912294365)
          ·
            refine ⟨834031472023318842110387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2224083925395516912294365 834031472023318842110387)
            ·
              refine ⟨1251047208034978263165581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834031472023318842110387 1251047208034978263165581)
              ·
                refine ⟨469142703013116848687093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1251047208034978263165581 469142703013116848687093)
                ·
                  refine ⟨43982128407479704564415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 469142703013116848687093 43982128407479704564415)
                  ·
                    rfl

theorem cell22_385447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 5].length) (baseStart_385447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385447 prefixEnd_385447 := by exact prefixLift 385447
  have htrace : WordTrace (prefixWord ++ tailWord_385447) baseStart_385447 baseEnd_385447 := by
    simpa [prefixWord, tailWord_385447, baseEnd_385447] using wordTrace_append hprefix tailTrace_385447
  have hstable : (prefixWord ++ tailWord_385447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385447).length < 2 ^ (prefixWord ++ tailWord_385447).sum := by decide
  have hdescent : baseEnd_385447 < baseStart_385447 := by decide
  rcases family_descends (prefixWord ++ tailWord_385447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385505 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_385505 : Nat := 118140960795 + 385505 * 2 ^ 59
def prefixEnd_385505 : Nat := 4983230072969 + 3 ^ 40 * 385505 * 2
def baseEnd_385505 : Nat := 131966239807746295743067

theorem tailTrace_385505 : CollatzResearch.WordTrace tailWord_385505 prefixEnd_385505 131966239807746295743067 := by
  unfold tailWord_385505
  simp only [CollatzResearch.WordTrace]
  refine ⟨14060522468388698857397969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9373681645592465904931979 14060522468388698857397969)
  ·
    refine ⟨10545391851291524143048477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14060522468388698857397969 10545391851291524143048477)
    ·
      refine ⟨3954521944234321553643179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10545391851291524143048477 3954521944234321553643179)
      ·
        refine ⟨5931782916351482330464769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954521944234321553643179 5931782916351482330464769)
        ·
          refine ⟨4448837187263611747848577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5931782916351482330464769 4448837187263611747848577)
          ·
            refine ⟨3336627890447708810886433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448837187263611747848577 3336627890447708810886433)
            ·
              refine ⟨2502470917835781608164825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336627890447708810886433 2502470917835781608164825)
              ·
                refine ⟨1876853188376836206123619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502470917835781608164825 1876853188376836206123619)
                ·
                  refine ⟨2815279782565254309185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876853188376836206123619 2815279782565254309185429)
                  ·
                    refine ⟨131966239807746295743067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2815279782565254309185429 131966239807746295743067)
                    ·
                      rfl

theorem cell22_385505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_385505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_385505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_385505 prefixEnd_385505 := by exact prefixLift 385505
  have htrace : WordTrace (prefixWord ++ tailWord_385505) baseStart_385505 baseEnd_385505 := by
    simpa [prefixWord, tailWord_385505, baseEnd_385505] using wordTrace_append hprefix tailTrace_385505
  have hstable : (prefixWord ++ tailWord_385505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385505).length < 2 ^ (prefixWord ++ tailWord_385505).sum := by decide
  have hdescent : baseEnd_385505 < baseStart_385505 := by decide
  rcases family_descends (prefixWord ++ tailWord_385505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
