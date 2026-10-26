import V185TrunkScan22Chunk048

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_438536 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_438536 : Nat := 118140960795 + 438536 * 2 ^ 59
def prefixEnd_438536 : Nat := 4983230072969 + 3 ^ 40 * 438536 * 2
def baseEnd_438536 : Nat := 150119834866800973055477

theorem tailTrace_438536 : CollatzResearch.WordTrace tailWord_438536 prefixEnd_438536 150119834866800973055477 := by
  unfold tailWord_438536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7997360969633221415567731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10663147959510961887423641 7997360969633221415567731)
  ·
    refine ⟨11996041454449832123351597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7997360969633221415567731 11996041454449832123351597)
    ·
      refine ⟨4498515545418687046256849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11996041454449832123351597 4498515545418687046256849)
      ·
        refine ⟨3373886659064015284692637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4498515545418687046256849 3373886659064015284692637)
        ·
          refine ⟨1265207497149005731759739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3373886659064015284692637 1265207497149005731759739)
          ·
            refine ⟨1897811245723508597639609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265207497149005731759739 1897811245723508597639609)
            ·
              refine ⟨1423358434292631448229707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1897811245723508597639609 1423358434292631448229707)
              ·
                refine ⟨2135037651438947172344561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423358434292631448229707 2135037651438947172344561)
                ·
                  refine ⟨1601278238579210379258421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2135037651438947172344561 1601278238579210379258421)
                  ·
                    refine ⟨150119834866800973055477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1601278238579210379258421 150119834866800973055477)
                    ·
                      rfl

theorem cell22_438536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_438536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438536 prefixEnd_438536 := by exact prefixLift 438536
  have htrace : WordTrace (prefixWord ++ tailWord_438536) baseStart_438536 baseEnd_438536 := by
    simpa [prefixWord, tailWord_438536, baseEnd_438536] using wordTrace_append hprefix tailTrace_438536
  have hstable : (prefixWord ++ tailWord_438536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438536).length < 2 ^ (prefixWord ++ tailWord_438536).sum := by decide
  have hdescent : baseEnd_438536 < baseStart_438536 := by decide
  rcases family_descends (prefixWord ++ tailWord_438536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438718 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_438718 : Nat := 118140960795 + 438718 * 2 ^ 59
def prefixEnd_438718 : Nat := 4983230072969 + 3 ^ 40 * 438718 * 2
def baseEnd_438718 : Nat := 50060712395404388334973

theorem tailTrace_438718 : CollatzResearch.WordTrace tailWord_438718 prefixEnd_438718 50060712395404388334973 := by
  unfold tailWord_438718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000170003075885989282601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10667573349738058609507205 2000170003075885989282601)
  ·
    refine ⟨1500127502306914491961951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000170003075885989282601 1500127502306914491961951)
    ·
      refine ⟨2250191253460371737942927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500127502306914491961951 2250191253460371737942927)
      ·
        refine ⟨3375286880190557606914391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250191253460371737942927 3375286880190557606914391)
        ·
          refine ⟨5062930320285836410371587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375286880190557606914391 5062930320285836410371587)
          ·
            refine ⟨7594395480428754615557381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062930320285836410371587 7594395480428754615557381)
            ·
              refine ⟨1423949152580391490417009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7594395480428754615557381 1423949152580391490417009)
              ·
                refine ⟨1067961864435293617812757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423949152580391490417009 1067961864435293617812757)
                ·
                  refine ⟨50060712395404388334973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1067961864435293617812757 50060712395404388334973)
                  ·
                    rfl

theorem cell22_438718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_438718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438718 prefixEnd_438718 := by exact prefixLift 438718
  have htrace : WordTrace (prefixWord ++ tailWord_438718) baseStart_438718 baseEnd_438718 := by
    simpa [prefixWord, tailWord_438718, baseEnd_438718] using wordTrace_append hprefix tailTrace_438718
  have hstable : (prefixWord ++ tailWord_438718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438718).length < 2 ^ (prefixWord ++ tailWord_438718).sum := by decide
  have hdescent : baseEnd_438718 < baseStart_438718 := by decide
  rcases family_descends (prefixWord ++ tailWord_438718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438761 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_438761 : Nat := 118140960795 + 438761 * 2 ^ 59
def prefixEnd_438761 : Nat := 4983230072969 + 3 ^ 40 * 438761 * 2
def baseEnd_438761 : Nat := 150196856964975386179787

theorem tailTrace_438761 : CollatzResearch.WordTrace tailWord_438761 prefixEnd_438761 150196856964975386179787 := by
  unfold tailWord_438761
  simp only [CollatzResearch.WordTrace]
  refine ⟨16002928363451306258076137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10668618908967537505384091 16002928363451306258076137)
  ·
    refine ⟨12002196272588479693557103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16002928363451306258076137 12002196272588479693557103)
    ·
      refine ⟨18003294408882719540335655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12002196272588479693557103 18003294408882719540335655)
      ·
        refine ⟨27004941613324079310503483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18003294408882719540335655 27004941613324079310503483)
        ·
          refine ⟨40507412419986118965755225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27004941613324079310503483 40507412419986118965755225)
          ·
            refine ⟨30380559314989589224316419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40507412419986118965755225 30380559314989589224316419)
            ·
              refine ⟨45570838972484383836474629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30380559314989589224316419 45570838972484383836474629)
              ·
                refine ⟨8544532307340821969338993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45570838972484383836474629 8544532307340821969338993)
                ·
                  refine ⟨6408399230505616477004245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8544532307340821969338993 6408399230505616477004245)
                  ·
                    refine ⟨150196856964975386179787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6408399230505616477004245 150196856964975386179787)
                    ·
                      rfl

theorem cell22_438761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_438761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438761 prefixEnd_438761 := by exact prefixLift 438761
  have htrace : WordTrace (prefixWord ++ tailWord_438761) baseStart_438761 baseEnd_438761 := by
    simpa [prefixWord, tailWord_438761, baseEnd_438761] using wordTrace_append hprefix tailTrace_438761
  have hstable : (prefixWord ++ tailWord_438761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438761).length < 2 ^ (prefixWord ++ tailWord_438761).sum := by decide
  have hdescent : baseEnd_438761 < baseStart_438761 := by decide
  rcases family_descends (prefixWord ++ tailWord_438761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438883 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_438883 : Nat := 118140960795 + 438883 * 2 ^ 59
def prefixEnd_438883 : Nat := 4983230072969 + 3 ^ 40 * 438883 * 2
def baseEnd_438883 : Nat := 150238620058207734629413

theorem tailTrace_438883 : CollatzResearch.WordTrace tailWord_438883 prefixEnd_438883 150238620058207734629413 := by
  unfold tailWord_438883
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007378069009321094017303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10671585379339547396011535 16007378069009321094017303)
  ·
    refine ⟨24011067103513981641025955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16007378069009321094017303 24011067103513981641025955)
    ·
      refine ⟨36016600655270972461538933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24011067103513981641025955 36016600655270972461538933)
      ·
        refine ⟨3376556311431653668269275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36016600655270972461538933 3376556311431653668269275)
        ·
          refine ⟨5064834467147480502403913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376556311431653668269275 5064834467147480502403913)
          ·
            refine ⟨3798625850360610376802935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5064834467147480502403913 3798625850360610376802935)
            ·
              refine ⟨5697938775540915565204403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798625850360610376802935 5697938775540915565204403)
              ·
                refine ⟨8546908163311373347806605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697938775540915565204403 8546908163311373347806605)
                ·
                  refine ⟨3205090561241765005427477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8546908163311373347806605 3205090561241765005427477)
                  ·
                    refine ⟨150238620058207734629413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3205090561241765005427477 150238620058207734629413)
                    ·
                      rfl

theorem cell22_438883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_438883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438883 prefixEnd_438883 := by exact prefixLift 438883
  have htrace : WordTrace (prefixWord ++ tailWord_438883) baseStart_438883 baseEnd_438883 := by
    simpa [prefixWord, tailWord_438883, baseEnd_438883] using wordTrace_append hprefix tailTrace_438883
  have hstable : (prefixWord ++ tailWord_438883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438883).length < 2 ^ (prefixWord ++ tailWord_438883).sum := by decide
  have hdescent : baseEnd_438883 < baseStart_438883 := by decide
  rcases family_descends (prefixWord ++ tailWord_438883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438932 : List Nat := [2, 4, 2, 2, 1, 2, 2, 7]
def baseStart_438932 : Nat := 118140960795 + 438932 * 2 ^ 59
def prefixEnd_438932 : Nat := 4983230072969 + 3 ^ 40 * 438932 * 2
def baseEnd_438932 : Nat := 16695043751065326683807

theorem tailTrace_438932 : CollatzResearch.WordTrace tailWord_438932 prefixEnd_438932 16695043751065326683807 := by
  unfold tailWord_438932
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004582622915901231275525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10672776830554534975034033 8004582622915901231275525)
  ·
    refine ⟨1500859241796731480864161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8004582622915901231275525 1500859241796731480864161)
    ·
      refine ⟨1125644431347548610648121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1500859241796731480864161 1125644431347548610648121)
      ·
        refine ⟨844233323510661457986091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1125644431347548610648121 844233323510661457986091)
        ·
          refine ⟨1266349985265992186979137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844233323510661457986091 1266349985265992186979137)
          ·
            refine ⟨949762488949494140234353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266349985265992186979137 949762488949494140234353)
            ·
              refine ⟨712321866712120605175765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949762488949494140234353 712321866712120605175765)
              ·
                refine ⟨16695043751065326683807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 712321866712120605175765 16695043751065326683807)
                ·
                  rfl

theorem cell22_438932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_438932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_438932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_438932 prefixEnd_438932 := by exact prefixLift 438932
  have htrace : WordTrace (prefixWord ++ tailWord_438932) baseStart_438932 baseEnd_438932 := by
    simpa [prefixWord, tailWord_438932, baseEnd_438932] using wordTrace_append hprefix tailTrace_438932
  have hstable : (prefixWord ++ tailWord_438932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438932).length < 2 ^ (prefixWord ++ tailWord_438932).sum := by decide
  have hdescent : baseEnd_438932 < baseStart_438932 := by decide
  rcases family_descends (prefixWord ++ tailWord_438932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439028 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 5]
def baseStart_439028 : Nat := 118140960795 + 439028 * 2 ^ 59
def prefixEnd_439028 : Nat := 4983230072969 + 3 ^ 40 * 439028 * 2
def baseEnd_439028 : Nat := 50096085507158563251323

theorem tailTrace_439028 : CollatzResearch.WordTrace tailWord_439028 prefixEnd_439028 50096085507158563251323 := by
  unfold tailWord_439028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006333326742005429022869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10675111102322673905363825 8006333326742005429022869)
  ·
    refine ⟨375296874691031504485447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8006333326742005429022869 375296874691031504485447)
    ·
      refine ⟨562945312036547256728171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375296874691031504485447 562945312036547256728171)
      ·
        refine ⟨844417968054820885092257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562945312036547256728171 844417968054820885092257)
        ·
          refine ⟨633313476041115663819193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 844417968054820885092257 633313476041115663819193)
          ·
            refine ⟨474985107030836747864395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633313476041115663819193 474985107030836747864395)
            ·
              refine ⟨712477660546255121796593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474985107030836747864395 712477660546255121796593)
              ·
                refine ⟨534358245409691341347445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712477660546255121796593 534358245409691341347445)
                ·
                  refine ⟨50096085507158563251323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534358245409691341347445 50096085507158563251323)
                  ·
                    rfl

theorem cell22_439028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_439028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439028 prefixEnd_439028 := by exact prefixLift 439028
  have htrace : WordTrace (prefixWord ++ tailWord_439028) baseStart_439028 baseEnd_439028 := by
    simpa [prefixWord, tailWord_439028, baseEnd_439028] using wordTrace_append hprefix tailTrace_439028
  have hstable : (prefixWord ++ tailWord_439028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439028).length < 2 ^ (prefixWord ++ tailWord_439028).sum := by decide
  have hdescent : baseEnd_439028 < baseStart_439028 := by decide
  rcases family_descends (prefixWord ++ tailWord_439028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439037 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_439037 : Nat := 118140960795 + 439037 * 2 ^ 59
def prefixEnd_439037 : Nat := 4983230072969 + 3 ^ 40 * 439037 * 2
def baseEnd_439037 : Nat := 150291337405402666278941

theorem tailTrace_439037 : CollatzResearch.WordTrace tailWord_439037 prefixEnd_439037 150291337405402666278941 := by
  unfold tailWord_439037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16012994910451405395123365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10675329940300936930082243 16012994910451405395123365)
  ·
    refine ⟨3002436545709638511585631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16012994910451405395123365 3002436545709638511585631)
    ·
      refine ⟨4503654818564457767378447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002436545709638511585631 4503654818564457767378447)
      ·
        refine ⟨6755482227846686651067671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503654818564457767378447 6755482227846686651067671)
        ·
          refine ⟨10133223341770029976601507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755482227846686651067671 10133223341770029976601507)
          ·
            refine ⟨15199835012655044964902261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133223341770029976601507 15199835012655044964902261)
            ·
              refine ⟨1424984532436410465459587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15199835012655044964902261 1424984532436410465459587)
              ·
                refine ⟨2137476798654615698189381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424984532436410465459587 2137476798654615698189381)
                ·
                  refine ⟨400776899747740443410509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137476798654615698189381 400776899747740443410509)
                  ·
                    refine ⟨150291337405402666278941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400776899747740443410509 150291337405402666278941)
                    ·
                      rfl

theorem cell22_439037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_439037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439037 prefixEnd_439037 := by exact prefixLift 439037
  have htrace : WordTrace (prefixWord ++ tailWord_439037) baseStart_439037 baseEnd_439037 := by
    simpa [prefixWord, tailWord_439037, baseEnd_439037] using wordTrace_append hprefix tailTrace_439037
  have hstable : (prefixWord ++ tailWord_439037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439037).length < 2 ^ (prefixWord ++ tailWord_439037).sum := by decide
  have hdescent : baseEnd_439037 < baseStart_439037 := by decide
  rcases family_descends (prefixWord ++ tailWord_439037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439050 : List Nat := [3, 1, 2, 2, 1, 2, 2, 9]
def baseStart_439050 : Nat := 118140960795 + 439050 * 2 ^ 59
def prefixEnd_439050 : Nat := 4983230072969 + 3 ^ 40 * 439050 * 2
def baseEnd_439050 : Nat := 16699531952341662855989

theorem tailTrace_439050 : CollatzResearch.WordTrace tailWord_439050 prefixEnd_439050 16699531952341662855989 := by
  unfold tailWord_439050
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003367264851077153836651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10675646039602872410231069 4003367264851077153836651)
  ·
    refine ⟨6005050897276615730754977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003367264851077153836651 6005050897276615730754977)
    ·
      refine ⟨4503788172957461798066233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6005050897276615730754977 4503788172957461798066233)
      ·
        refine ⟨3377841129718096348549675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4503788172957461798066233 3377841129718096348549675)
        ·
          refine ⟨5066761694577144522824513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377841129718096348549675 5066761694577144522824513)
          ·
            refine ⟨3800071270932858392118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5066761694577144522824513 3800071270932858392118385)
            ·
              refine ⟨2850053453199643794088789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800071270932858392118385 2850053453199643794088789)
              ·
                refine ⟨16699531952341662855989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2850053453199643794088789 16699531952341662855989)
                ·
                  rfl

theorem cell22_439050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_439050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439050 prefixEnd_439050 := by exact prefixLift 439050
  have htrace : WordTrace (prefixWord ++ tailWord_439050) baseStart_439050 baseEnd_439050 := by
    simpa [prefixWord, tailWord_439050, baseEnd_439050] using wordTrace_append hprefix tailTrace_439050
  have hstable : (prefixWord ++ tailWord_439050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439050).length < 2 ^ (prefixWord ++ tailWord_439050).sum := by decide
  have hdescent : baseEnd_439050 < baseStart_439050 := by decide
  rcases family_descends (prefixWord ++ tailWord_439050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439095 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 7]
def baseStart_439095 : Nat := 118140960795 + 439095 * 2 ^ 59
def prefixEnd_439095 : Nat := 4983230072969 + 3 ^ 40 * 439095 * 2
def baseEnd_439095 : Nat := 50103730663569949442921

theorem tailTrace_439095 : CollatzResearch.WordTrace tailWord_439095 prefixEnd_439095 50103730663569949442921 := by
  unfold tailWord_439095
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015110344241281300734739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10676740229494187533823159 16015110344241281300734739)
  ·
    refine ⟨24022665516361921951102109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16015110344241281300734739 24022665516361921951102109)
    ·
      refine ⟨9008499568635720731663291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24022665516361921951102109 9008499568635720731663291)
      ·
        refine ⟨13512749352953581097494937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9008499568635720731663291 13512749352953581097494937)
        ·
          refine ⟨10134562014715185823121203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13512749352953581097494937 10134562014715185823121203)
          ·
            refine ⟨15201843022072778734681805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10134562014715185823121203 15201843022072778734681805)
            ·
              refine ⟨5700691133277292025505677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15201843022072778734681805 5700691133277292025505677)
              ·
                refine ⟨2137759174978984509564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5700691133277292025505677 2137759174978984509564629)
                ·
                  refine ⟨50103730663569949442921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2137759174978984509564629 50103730663569949442921)
                  ·
                    rfl

theorem cell22_439095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_439095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439095 prefixEnd_439095 := by exact prefixLift 439095
  have htrace : WordTrace (prefixWord ++ tailWord_439095) baseStart_439095 baseEnd_439095 := by
    simpa [prefixWord, tailWord_439095, baseEnd_439095] using wordTrace_append hprefix tailTrace_439095
  have hstable : (prefixWord ++ tailWord_439095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439095).length < 2 ^ (prefixWord ++ tailWord_439095).sum := by decide
  have hdescent : baseEnd_439095 < baseStart_439095 := by decide
  rcases family_descends (prefixWord ++ tailWord_439095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439105 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_439105 : Nat := 118140960795 + 439105 * 2 ^ 59
def prefixEnd_439105 : Nat := 4983230072969 + 3 ^ 40 * 439105 * 2
def baseEnd_439105 : Nat := 150314615195073155578733

theorem tailTrace_439105 : CollatzResearch.WordTrace tailWord_439105 prefixEnd_439105 150314615195073155578733 := by
  unfold tailWord_439105
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015475074205053008598769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10676983382803368672399179 16015475074205053008598769)
  ·
    refine ⟨12011606305653789756449077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16015475074205053008598769 12011606305653789756449077)
    ·
      refine ⟨1126088091155042789667101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12011606305653789756449077 1126088091155042789667101)
      ·
        refine ⟨422283034183141046125163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1126088091155042789667101 422283034183141046125163)
        ·
          refine ⟨633424551274711569187745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422283034183141046125163 633424551274711569187745)
          ·
            refine ⟨475068413456033676890809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633424551274711569187745 475068413456033676890809)
            ·
              refine ⟨356301310092025257668107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475068413456033676890809 356301310092025257668107)
              ·
                refine ⟨534451965138037886502161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356301310092025257668107 534451965138037886502161)
                ·
                  refine ⟨400838973853528414876621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534451965138037886502161 400838973853528414876621)
                  ·
                    refine ⟨150314615195073155578733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 400838973853528414876621 150314615195073155578733)
                    ·
                      rfl

theorem cell22_439105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_439105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439105 prefixEnd_439105 := by exact prefixLift 439105
  have htrace : WordTrace (prefixWord ++ tailWord_439105) baseStart_439105 baseEnd_439105 := by
    simpa [prefixWord, tailWord_439105, baseEnd_439105] using wordTrace_append hprefix tailTrace_439105
  have hstable : (prefixWord ++ tailWord_439105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439105).length < 2 ^ (prefixWord ++ tailWord_439105).sum := by decide
  have hdescent : baseEnd_439105 < baseStart_439105 := by decide
  rcases family_descends (prefixWord ++ tailWord_439105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439112 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_439112 : Nat := 118140960795 + 439112 * 2 ^ 59
def prefixEnd_439112 : Nat := 4983230072969 + 3 ^ 40 * 439112 * 2
def baseEnd_439112 : Nat := 50105670479375823551237

theorem tailTrace_439112 : CollatzResearch.WordTrace tailWord_439112 prefixEnd_439112 50105670479375823551237 := by
  unfold tailWord_439112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007865192589846602051795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10677153590119795469402393 8007865192589846602051795)
  ·
    refine ⟨12011797788884769903077693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8007865192589846602051795 12011797788884769903077693)
    ·
      refine ⟨4504424170831788713654135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12011797788884769903077693 4504424170831788713654135)
      ·
        refine ⟨6756636256247683070481203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504424170831788713654135 6756636256247683070481203)
        ·
          refine ⟨10134954384371524605721805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6756636256247683070481203 10134954384371524605721805)
          ·
            refine ⟨3800607894139321727145677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10134954384371524605721805 3800607894139321727145677)
            ·
              refine ⟨1425227960302245647679629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3800607894139321727145677 1425227960302245647679629)
              ·
                refine ⟨534460485113342117879861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1425227960302245647679629 534460485113342117879861)
                ·
                  refine ⟨50105670479375823551237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534460485113342117879861 50105670479375823551237)
                  ·
                    rfl

theorem cell22_439112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_439112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439112 prefixEnd_439112 := by exact prefixLift 439112
  have htrace : WordTrace (prefixWord ++ tailWord_439112) baseStart_439112 baseEnd_439112 := by
    simpa [prefixWord, tailWord_439112, baseEnd_439112] using wordTrace_append hprefix tailTrace_439112
  have hstable : (prefixWord ++ tailWord_439112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439112).length < 2 ^ (prefixWord ++ tailWord_439112).sum := by decide
  have hdescent : baseEnd_439112 < baseStart_439112 := by decide
  rcases family_descends (prefixWord ++ tailWord_439112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439187 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_439187 : Nat := 118140960795 + 439187 * 2 ^ 59
def prefixEnd_439187 : Nat := 4983230072969 + 3 ^ 40 * 439187 * 2
def baseEnd_439187 : Nat := 150342685470852275028481

theorem tailTrace_439187 : CollatzResearch.WordTrace tailWord_439187 prefixEnd_439187 150342685470852275028481 := by
  unfold tailWord_439187
  simp only [CollatzResearch.WordTrace]
  refine ⟨16018465859907981013083815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10678977239938654008722543 16018465859907981013083815)
  ·
    refine ⟨24027698789861971519625723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16018465859907981013083815 24027698789861971519625723)
    ·
      refine ⟨36041548184792957279438585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24027698789861971519625723 36041548184792957279438585)
      ·
        refine ⟨27031161138594717959578939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36041548184792957279438585 27031161138594717959578939)
        ·
          refine ⟨40546741707892076939368409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27031161138594717959578939 40546741707892076939368409)
          ·
            refine ⟨30410056280919057704526307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40546741707892076939368409 30410056280919057704526307)
            ·
              refine ⟨45615084421378586556789461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30410056280919057704526307 45615084421378586556789461)
              ·
                refine ⟨1069103541126060622424753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45615084421378586556789461 1069103541126060622424753)
                ·
                  refine ⟨801827655844545466818565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069103541126060622424753 801827655844545466818565)
                  ·
                    refine ⟨150342685470852275028481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 801827655844545466818565 150342685470852275028481)
                    ·
                      rfl

theorem cell22_439187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_439187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439187 prefixEnd_439187 := by exact prefixLift 439187
  have htrace : WordTrace (prefixWord ++ tailWord_439187) baseStart_439187 baseEnd_439187 := by
    simpa [prefixWord, tailWord_439187, baseEnd_439187] using wordTrace_append hprefix tailTrace_439187
  have hstable : (prefixWord ++ tailWord_439187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439187).length < 2 ^ (prefixWord ++ tailWord_439187).sum := by decide
  have hdescent : baseEnd_439187 < baseStart_439187 := by decide
  rcases family_descends (prefixWord ++ tailWord_439187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439236 : List Nat := [2, 3, 3, 3, 1, 1, 1, 8]
def baseStart_439236 : Nat := 118140960795 + 439236 * 2 ^ 59
def prefixEnd_439236 : Nat := 4983230072969 + 3 ^ 40 * 439236 * 2
def baseEnd_439236 : Nat := 16706606574692497839259

theorem tailTrace_439236 : CollatzResearch.WordTrace tailWord_439236 prefixEnd_439236 16706606574692497839259 := by
  unfold tailWord_439236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010126518365231190808781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10680168691153641587745041 8010126518365231190808781)
  ·
    refine ⟨3003797444386961696553293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8010126518365231190808781 3003797444386961696553293)
    ·
      refine ⟨1126424041645110636207485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3003797444386961696553293 1126424041645110636207485)
      ·
        refine ⟨422409015616916488577807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1126424041645110636207485 422409015616916488577807)
        ·
          refine ⟨633613523425374732866711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422409015616916488577807 633613523425374732866711)
          ·
            refine ⟨950420285138062099300067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633613523425374732866711 950420285138062099300067)
            ·
              refine ⟨1425630427707093148950101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950420285138062099300067 1425630427707093148950101)
              ·
                refine ⟨16706606574692497839259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1425630427707093148950101 16706606574692497839259)
                ·
                  rfl

theorem cell22_439236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_439236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439236 prefixEnd_439236 := by exact prefixLift 439236
  have htrace : WordTrace (prefixWord ++ tailWord_439236) baseStart_439236 baseEnd_439236 := by
    simpa [prefixWord, tailWord_439236, baseEnd_439236] using wordTrace_append hprefix tailTrace_439236
  have hstable : (prefixWord ++ tailWord_439236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439236).length < 2 ^ (prefixWord ++ tailWord_439236).sum := by decide
  have hdescent : baseEnd_439236 < baseStart_439236 := by decide
  rcases family_descends (prefixWord ++ tailWord_439236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439247 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 7]
def baseStart_439247 : Nat := 118140960795 + 439247 * 2 ^ 59
def prefixEnd_439247 : Nat := 4983230072969 + 3 ^ 40 * 439247 * 2
def baseEnd_439247 : Nat := 50121074899010706176099

theorem tailTrace_439247 : CollatzResearch.WordTrace tailWord_439247 prefixEnd_439247 50121074899010706176099 := by
  unfold tailWord_439247
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020654239690611260267995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10680436159793740840178663 16020654239690611260267995)
  ·
    refine ⟨24030981359535916890401993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020654239690611260267995 24030981359535916890401993)
    ·
      refine ⟨18023236019651937667801495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24030981359535916890401993 18023236019651937667801495)
      ·
        refine ⟨27034854029477906501702243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18023236019651937667801495 27034854029477906501702243)
        ·
          refine ⟨40552281044216859752553365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27034854029477906501702243 40552281044216859752553365)
          ·
            refine ⟨1900888173947665300900939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40552281044216859752553365 1900888173947665300900939)
            ·
              refine ⟨2851332260921497951351409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900888173947665300900939 2851332260921497951351409)
              ·
                refine ⟨2138499195691123463513557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851332260921497951351409 2138499195691123463513557)
                ·
                  refine ⟨50121074899010706176099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2138499195691123463513557 50121074899010706176099)
                  ·
                    rfl

theorem cell22_439247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_439247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439247 prefixEnd_439247 := by exact prefixLift 439247
  have htrace : WordTrace (prefixWord ++ tailWord_439247) baseStart_439247 baseEnd_439247 := by
    simpa [prefixWord, tailWord_439247, baseEnd_439247] using wordTrace_append hprefix tailTrace_439247
  have hstable : (prefixWord ++ tailWord_439247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439247).length < 2 ^ (prefixWord ++ tailWord_439247).sum := by decide
  have hdescent : baseEnd_439247 < baseStart_439247 := by decide
  rcases family_descends (prefixWord ++ tailWord_439247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439281 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 5]
def baseStart_439281 : Nat := 118140960795 + 439281 * 2 ^ 59
def prefixEnd_439281 : Nat := 4983230072969 + 3 ^ 40 * 439281 * 2
def baseEnd_439281 : Nat := 50124954530622454392731

theorem tailTrace_439281 : CollatzResearch.WordTrace tailWord_439281 prefixEnd_439281 50124954530622454392731 := by
  unfold tailWord_439281
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021894321567435067005697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10681262881044956711337131 16021894321567435067005697)
  ·
    refine ⟨12016420741175576300254273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16021894321567435067005697 12016420741175576300254273)
    ·
      refine ⟨9012315555881682225190705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12016420741175576300254273 9012315555881682225190705)
      ·
        refine ⟨6759236666911261668893029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9012315555881682225190705 6759236666911261668893029)
        ·
          refine ⟨1267356875045861562917443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6759236666911261668893029 1267356875045861562917443)
          ·
            refine ⟨1901035312568792344376165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267356875045861562917443 1901035312568792344376165)
            ·
              refine ⟨356444121106648564570531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1901035312568792344376165 356444121106648564570531)
              ·
                refine ⟨534666181659972846855797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356444121106648564570531 534666181659972846855797)
                ·
                  refine ⟨50124954530622454392731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534666181659972846855797 50124954530622454392731)
                  ·
                    rfl

theorem cell22_439281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_439281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439281 prefixEnd_439281 := by exact prefixLift 439281
  have htrace : WordTrace (prefixWord ++ tailWord_439281) baseStart_439281 baseEnd_439281 := by
    simpa [prefixWord, tailWord_439281, baseEnd_439281] using wordTrace_append hprefix tailTrace_439281
  have hstable : (prefixWord ++ tailWord_439281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439281).length < 2 ^ (prefixWord ++ tailWord_439281).sum := by decide
  have hdescent : baseEnd_439281 < baseStart_439281 := by decide
  rcases family_descends (prefixWord ++ tailWord_439281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439356 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_439356 : Nat := 118140960795 + 439356 * 2 ^ 59
def prefixEnd_439356 : Nat := 4983230072969 + 3 ^ 40 * 439356 * 2
def baseEnd_439356 : Nat := 150400537624592167552963

theorem tailTrace_439356 : CollatzResearch.WordTrace tailWord_439356 prefixEnd_439356 150400537624592167552963 := by
  unfold tailWord_439356
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012314898147861437992961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10683086530863815250657281 8012314898147861437992961)
  ·
    refine ⟨6009236173610896078494721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8012314898147861437992961 6009236173610896078494721)
    ·
      refine ⟨4506927130208172058871041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6009236173610896078494721 4506927130208172058871041)
      ·
        refine ⟨3380195347656129044153281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4506927130208172058871041 3380195347656129044153281)
        ·
          refine ⟨2535146510742096783114961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3380195347656129044153281 2535146510742096783114961)
          ·
            refine ⟨1901359883056572587336221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535146510742096783114961 1901359883056572587336221)
            ·
              refine ⟨713009956146214720251083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901359883056572587336221 713009956146214720251083)
              ·
                refine ⟨1069514934219322080376625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713009956146214720251083 1069514934219322080376625)
                ·
                  refine ⟨802136200664491560282469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069514934219322080376625 802136200664491560282469)
                  ·
                    refine ⟨150400537624592167552963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802136200664491560282469 150400537624592167552963)
                    ·
                      rfl

theorem cell22_439356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_439356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439356 prefixEnd_439356 := by exact prefixLift 439356
  have htrace : WordTrace (prefixWord ++ tailWord_439356) baseStart_439356 baseEnd_439356 := by
    simpa [prefixWord, tailWord_439356, baseEnd_439356] using wordTrace_append hprefix tailTrace_439356
  have hstable : (prefixWord ++ tailWord_439356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439356).length < 2 ^ (prefixWord ++ tailWord_439356).sum := by decide
  have hdescent : baseEnd_439356 < baseStart_439356 := by decide
  rcases family_descends (prefixWord ++ tailWord_439356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439422 : List Nat := [4, 2, 4, 1, 2, 1, 8]
def baseStart_439422 : Nat := 118140960795 + 439422 * 2 ^ 59
def prefixEnd_439422 : Nat := 4983230072969 + 3 ^ 40 * 439422 * 2
def baseEnd_439422 : Nat := 5571227065681110940843

theorem tailTrace_439422 : CollatzResearch.WordTrace tailWord_439422 prefixEnd_439422 5571227065681110940843 := by
  unfold tailWord_439422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003379626757077018486065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10684691342704410765259013 2003379626757077018486065)
  ·
    refine ⟨1502534720067807763864549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2003379626757077018486065 1502534720067807763864549)
    ·
      refine ⟨281725260012713955724603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1502534720067807763864549 281725260012713955724603)
      ·
        refine ⟨422587890019070933586905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281725260012713955724603 422587890019070933586905)
        ·
          refine ⟨316940917514303200190179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422587890019070933586905 316940917514303200190179)
          ·
            refine ⟨475411376271454800285269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316940917514303200190179 475411376271454800285269)
            ·
              refine ⟨5571227065681110940843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 475411376271454800285269 5571227065681110940843)
              ·
                rfl

theorem cell22_439422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 8].length) (baseStart_439422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439422 prefixEnd_439422 := by exact prefixLift 439422
  have htrace : WordTrace (prefixWord ++ tailWord_439422) baseStart_439422 baseEnd_439422 := by
    simpa [prefixWord, tailWord_439422, baseEnd_439422] using wordTrace_append hprefix tailTrace_439422
  have hstable : (prefixWord ++ tailWord_439422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439422).length < 2 ^ (prefixWord ++ tailWord_439422).sum := by decide
  have hdescent : baseEnd_439422 < baseStart_439422 := by decide
  rcases family_descends (prefixWord ++ tailWord_439422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439450 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_439450 : Nat := 118140960795 + 439450 * 2 ^ 59
def prefixEnd_439450 : Nat := 4983230072969 + 3 ^ 40 * 439450 * 2
def baseEnd_439450 : Nat := 50144238581869085234225

theorem tailTrace_439450 : CollatzResearch.WordTrace tailWord_439450 prefixEnd_439450 50144238581869085234225 := by
  unfold tailWord_439450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007014564488794232476951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10685372171970117953271869 4007014564488794232476951)
  ·
    refine ⟨6010521846733191348715427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4007014564488794232476951 6010521846733191348715427)
    ·
      refine ⟨9015782770099787023073141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6010521846733191348715427 9015782770099787023073141)
      ·
        refine ⟨845229634696855033413107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9015782770099787023073141 845229634696855033413107)
        ·
          refine ⟨1267844452045282550119661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845229634696855033413107 1267844452045282550119661)
          ·
            refine ⟨475441669516980956294873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1267844452045282550119661 475441669516980956294873)
            ·
              refine ⟨356581252137735717221155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475441669516980956294873 356581252137735717221155)
              ·
                refine ⟨534871878206603575831733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356581252137735717221155 534871878206603575831733)
                ·
                  refine ⟨50144238581869085234225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 534871878206603575831733 50144238581869085234225)
                  ·
                    rfl

theorem cell22_439450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_439450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439450 prefixEnd_439450 := by exact prefixLift 439450
  have htrace : WordTrace (prefixWord ++ tailWord_439450) baseStart_439450 baseEnd_439450 := by
    simpa [prefixWord, tailWord_439450, baseEnd_439450] using wordTrace_append hprefix tailTrace_439450
  have hstable : (prefixWord ++ tailWord_439450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439450).length < 2 ^ (prefixWord ++ tailWord_439450).sum := by decide
  have hdescent : baseEnd_439450 < baseStart_439450 := by decide
  rcases family_descends (prefixWord ++ tailWord_439450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439459 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_439459 : Nat := 118140960795 + 439459 * 2 ^ 59
def prefixEnd_439459 : Nat := 4983230072969 + 3 ^ 40 * 439459 * 2
def baseEnd_439459 : Nat := 150435796629534232227647

theorem tailTrace_439459 : CollatzResearch.WordTrace tailWord_439459 prefixEnd_439459 150435796629534232227647 := by
  unfold tailWord_439459
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028386514922571466985431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10685591009948380977990287 16028386514922571466985431)
  ·
    refine ⟨24042579772383857200478147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16028386514922571466985431 24042579772383857200478147)
    ·
      refine ⟨36063869658575785800717221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24042579772383857200478147 36063869658575785800717221)
      ·
        refine ⟨6761975560982959837634479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36063869658575785800717221 6761975560982959837634479)
        ·
          refine ⟨10142963341474439756451719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761975560982959837634479 10142963341474439756451719)
          ·
            refine ⟨15214445012211659634677579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142963341474439756451719 15214445012211659634677579)
            ·
              refine ⟨22821667518317489452016369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15214445012211659634677579 22821667518317489452016369)
              ·
                refine ⟨17116250638738117089012277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22821667518317489452016369 17116250638738117089012277)
                ·
                  refine ⟨1604648497381698477094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17116250638738117089012277 1604648497381698477094901)
                  ·
                    refine ⟨150435796629534232227647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1604648497381698477094901 150435796629534232227647)
                    ·
                      rfl

theorem cell22_439459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_439459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439459 prefixEnd_439459 := by exact prefixLift 439459
  have htrace : WordTrace (prefixWord ++ tailWord_439459) baseStart_439459 baseEnd_439459 := by
    simpa [prefixWord, tailWord_439459, baseEnd_439459] using wordTrace_append hprefix tailTrace_439459
  have hstable : (prefixWord ++ tailWord_439459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439459).length < 2 ^ (prefixWord ++ tailWord_439459).sum := by decide
  have hdescent : baseEnd_439459 < baseStart_439459 := by decide
  rcases family_descends (prefixWord ++ tailWord_439459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439463 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_439463 : Nat := 118140960795 + 439463 * 2 ^ 59
def prefixEnd_439463 : Nat := 4983230072969 + 3 ^ 40 * 439463 * 2
def baseEnd_439463 : Nat := 150437165911279555127635

theorem tailTrace_439463 : CollatzResearch.WordTrace tailWord_439463 prefixEnd_439463 150437165911279555127635 := by
  unfold tailWord_439463
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028532406908080150131043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10685688271272053433420695 16028532406908080150131043)
  ·
    refine ⟨24042798610362120225196565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16028532406908080150131043 24042798610362120225196565)
    ·
      refine ⟨1127006184860724385556089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24042798610362120225196565 1127006184860724385556089)
      ·
        refine ⟨845254638645543289167067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127006184860724385556089 845254638645543289167067)
        ·
          refine ⟨1267881957968314933750601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845254638645543289167067 1267881957968314933750601)
          ·
            refine ⟨950911468476236200312951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267881957968314933750601 950911468476236200312951)
            ·
              refine ⟨1426367202714354300469427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950911468476236200312951 1426367202714354300469427)
              ·
                refine ⟨2139550804071531450704141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426367202714354300469427 2139550804071531450704141)
                ·
                  refine ⟨802331551526824294014053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2139550804071531450704141 802331551526824294014053)
                  ·
                    refine ⟨150437165911279555127635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802331551526824294014053 150437165911279555127635)
                    ·
                      rfl

theorem cell22_439463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_439463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439463 prefixEnd_439463 := by exact prefixLift 439463
  have htrace : WordTrace (prefixWord ++ tailWord_439463) baseStart_439463 baseEnd_439463 := by
    simpa [prefixWord, tailWord_439463, baseEnd_439463] using wordTrace_append hprefix tailTrace_439463
  have hstable : (prefixWord ++ tailWord_439463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439463).length < 2 ^ (prefixWord ++ tailWord_439463).sum := by decide
  have hdescent : baseEnd_439463 < baseStart_439463 := by decide
  rcases family_descends (prefixWord ++ tailWord_439463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439525 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_439525 : Nat := 118140960795 + 439525 * 2 ^ 59
def prefixEnd_439525 : Nat := 4983230072969 + 3 ^ 40 * 439525 * 2
def baseEnd_439525 : Nat := 150458389778332060077445

theorem tailTrace_439525 : CollatzResearch.WordTrace tailWord_439525 prefixEnd_439525 150458389778332060077445 := by
  unfold tailWord_439525
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030793732683464738888029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10687195821788976492592019 16030793732683464738888029)
  ·
    refine ⟨6011547649756299277083011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16030793732683464738888029 6011547649756299277083011)
    ·
      refine ⟨9017321474634448915624517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6011547649756299277083011 9017321474634448915624517)
      ·
        refine ⟨1690747776493959171679597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9017321474634448915624517 1690747776493959171679597)
        ·
          refine ⟨634030416185234689379849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1690747776493959171679597 634030416185234689379849)
          ·
            refine ⟨475522812138926017034887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634030416185234689379849 475522812138926017034887)
            ·
              refine ⟨713284218208389025552331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475522812138926017034887 713284218208389025552331)
              ·
                refine ⟨1069926327312583538328497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713284218208389025552331 1069926327312583538328497)
                ·
                  refine ⟨802444745484437653746373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1069926327312583538328497 802444745484437653746373)
                  ·
                    refine ⟨150458389778332060077445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802444745484437653746373 150458389778332060077445)
                    ·
                      rfl

theorem cell22_439525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_439525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439525 prefixEnd_439525 := by exact prefixLift 439525
  have htrace : WordTrace (prefixWord ++ tailWord_439525) baseStart_439525 baseEnd_439525 := by
    simpa [prefixWord, tailWord_439525, baseEnd_439525] using wordTrace_append hprefix tailTrace_439525
  have hstable : (prefixWord ++ tailWord_439525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439525).length < 2 ^ (prefixWord ++ tailWord_439525).sum := by decide
  have hdescent : baseEnd_439525 < baseStart_439525 := by decide
  rcases family_descends (prefixWord ++ tailWord_439525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439551 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 7]
def baseStart_439551 : Nat := 118140960795 + 439551 * 2 ^ 59
def prefixEnd_439551 : Nat := 4983230072969 + 3 ^ 40 * 439551 * 2
def baseEnd_439551 : Nat := 50155763369892219642455

theorem tailTrace_439551 : CollatzResearch.WordTrace tailWord_439551 prefixEnd_439551 50155763369892219642455 := by
  unfold tailWord_439551
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031742030589271179334507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10687828020392847452889671 16031742030589271179334507)
  ·
    refine ⟨24047613045883906769001761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16031742030589271179334507 24047613045883906769001761)
    ·
      refine ⟨18035709784412930076751321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24047613045883906769001761 18035709784412930076751321)
      ·
        refine ⟨13526782338309697557563491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18035709784412930076751321 13526782338309697557563491)
        ·
          refine ⟨20290173507464546336345237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13526782338309697557563491 20290173507464546336345237)
          ·
            refine ⟨951101883162400609516183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20290173507464546336345237 951101883162400609516183)
            ·
              refine ⟨1426652824743600914274275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951101883162400609516183 1426652824743600914274275)
              ·
                refine ⟨2139979237115401371411413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426652824743600914274275 2139979237115401371411413)
                ·
                  refine ⟨50155763369892219642455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2139979237115401371411413 50155763369892219642455)
                  ·
                    rfl

theorem cell22_439551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_439551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439551 prefixEnd_439551 := by exact prefixLift 439551
  have htrace : WordTrace (prefixWord ++ tailWord_439551) baseStart_439551 baseEnd_439551 := by
    simpa [prefixWord, tailWord_439551, baseEnd_439551] using wordTrace_append hprefix tailTrace_439551
  have hstable : (prefixWord ++ tailWord_439551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439551).length < 2 ^ (prefixWord ++ tailWord_439551).sum := by decide
  have hdescent : baseEnd_439551 < baseStart_439551 := by decide
  rcases family_descends (prefixWord ++ tailWord_439551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439555 : List Nat := [1, 1, 1, 3, 2, 4, 2, 4, 1, 3]
def baseStart_439555 : Nat := 118140960795 + 439555 * 2 ^ 59
def prefixEnd_439555 : Nat := 4983230072969 + 3 ^ 40 * 439555 * 2
def baseEnd_439555 : Nat := 150468659391421981827353

theorem tailTrace_439555 : CollatzResearch.WordTrace tailWord_439555 prefixEnd_439555 150468659391421981827353 := by
  unfold tailWord_439555
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031887922574779862480119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10687925281716519908320079 16031887922574779862480119)
  ·
    refine ⟨24047831883862169793720179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16031887922574779862480119 24047831883862169793720179)
    ·
      refine ⟨36071747825793254690580269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24047831883862169793720179 36071747825793254690580269)
      ·
        refine ⟨13526905434672470508967601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36071747825793254690580269 13526905434672470508967601)
        ·
          refine ⟨10145179076004352881725701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13526905434672470508967601 10145179076004352881725701)
          ·
            refine ⟨1902221076750816165323569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10145179076004352881725701 1902221076750816165323569)
            ·
              refine ⟨1426665807563112123992677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902221076750816165323569 1426665807563112123992677)
              ·
                refine ⟨267499838918083523248627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1426665807563112123992677 267499838918083523248627)
                ·
                  refine ⟨401249758377125284872941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267499838918083523248627 401249758377125284872941)
                  ·
                    refine ⟨150468659391421981827353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 401249758377125284872941 150468659391421981827353)
                    ·
                      rfl

theorem cell22_439555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 1, 3].length) (baseStart_439555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439555 prefixEnd_439555 := by exact prefixLift 439555
  have htrace : WordTrace (prefixWord ++ tailWord_439555) baseStart_439555 baseEnd_439555 := by
    simpa [prefixWord, tailWord_439555, baseEnd_439555] using wordTrace_append hprefix tailTrace_439555
  have hstable : (prefixWord ++ tailWord_439555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439555).length < 2 ^ (prefixWord ++ tailWord_439555).sum := by decide
  have hdescent : baseEnd_439555 < baseStart_439555 := by decide
  rcases family_descends (prefixWord ++ tailWord_439555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439606 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_439606 : Nat := 118140960795 + 439606 * 2 ^ 59
def prefixEnd_439606 : Nat := 4983230072969 + 3 ^ 40 * 439606 * 2
def baseEnd_439606 : Nat := 150486117733674848802197

theorem tailTrace_439606 : CollatzResearch.WordTrace tailWord_439606 prefixEnd_439606 150486117733674848802197 := by
  unfold tailWord_439606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002109252836875973286667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10689165363593343715057781 1002109252836875973286667)
  ·
    refine ⟨1503163879255313959930001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1002109252836875973286667 1503163879255313959930001)
    ·
      refine ⟨1127372909441485469947501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1503163879255313959930001 1127372909441485469947501)
      ·
        refine ⟨422764841040557051230313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1127372909441485469947501 422764841040557051230313)
        ·
          refine ⟨317073630780417788422735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422764841040557051230313 317073630780417788422735)
          ·
            refine ⟨475610446170626682634103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317073630780417788422735 475610446170626682634103)
            ·
              refine ⟨713415669255940023951155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475610446170626682634103 713415669255940023951155)
              ·
                refine ⟨1070123503883910035926733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713415669255940023951155 1070123503883910035926733)
                ·
                  refine ⟨401296313956466263472525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070123503883910035926733 401296313956466263472525)
                  ·
                    refine ⟨150486117733674848802197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 401296313956466263472525 150486117733674848802197)
                    ·
                      rfl

theorem cell22_439606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_439606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439606 prefixEnd_439606 := by exact prefixLift 439606
  have htrace : WordTrace (prefixWord ++ tailWord_439606) baseStart_439606 baseEnd_439606 := by
    simpa [prefixWord, tailWord_439606, baseEnd_439606] using wordTrace_append hprefix tailTrace_439606
  have hstable : (prefixWord ++ tailWord_439606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439606).length < 2 ^ (prefixWord ++ tailWord_439606).sum := by decide
  have hdescent : baseEnd_439606 < baseStart_439606 := by decide
  rcases family_descends (prefixWord ++ tailWord_439606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439626 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_439626 : Nat := 118140960795 + 439626 * 2 ^ 59
def prefixEnd_439626 : Nat := 4983230072969 + 3 ^ 40 * 439626 * 2
def baseEnd_439626 : Nat := 150492964142401463302135

theorem tailTrace_439626 : CollatzResearch.WordTrace tailWord_439626 prefixEnd_439626 150492964142401463302135 := by
  unfold tailWord_439626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008619376329389747078683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10689651670211705992209821 4008619376329389747078683)
  ·
    refine ⟨6012929064494084620618025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4008619376329389747078683 6012929064494084620618025)
    ·
      refine ⟨4509696798370563465463519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6012929064494084620618025 4509696798370563465463519)
      ·
        refine ⟨6764545197555845198195279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4509696798370563465463519 6764545197555845198195279)
        ·
          refine ⟨10146817796333767797292919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764545197555845198195279 10146817796333767797292919)
          ·
            refine ⟨15220226694500651695939379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10146817796333767797292919 15220226694500651695939379)
            ·
              refine ⟨22830340041750977543909069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15220226694500651695939379 22830340041750977543909069)
              ·
                refine ⟨8561377515656616578965901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22830340041750977543909069 8561377515656616578965901)
                ·
                  refine ⟨3210516568371231217112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8561377515656616578965901 3210516568371231217112213)
                  ·
                    refine ⟨150492964142401463302135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3210516568371231217112213 150492964142401463302135)
                    ·
                      rfl

theorem cell22_439626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_439626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439626 prefixEnd_439626 := by exact prefixLift 439626
  have htrace : WordTrace (prefixWord ++ tailWord_439626) baseStart_439626 baseEnd_439626 := by
    simpa [prefixWord, tailWord_439626, baseEnd_439626] using wordTrace_append hprefix tailTrace_439626
  have hstable : (prefixWord ++ tailWord_439626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439626).length < 2 ^ (prefixWord ++ tailWord_439626).sum := by decide
  have hdescent : baseEnd_439626 < baseStart_439626 := by decide
  rcases family_descends (prefixWord ++ tailWord_439626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439641 : List Nat := [1, 2, 1, 2, 2, 2, 4, 8]
def baseStart_439641 : Nat := 118140960795 + 439641 * 2 ^ 59
def prefixEnd_439641 : Nat := 4983230072969 + 3 ^ 40 * 439641 * 2
def baseEnd_439641 : Nat := 16722010994327380464121

theorem tailTrace_439641 : CollatzResearch.WordTrace tailWord_439641 prefixEnd_439641 16722010994327380464121 := by
  unfold tailWord_439641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16035024600263216550110777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10690016400175477700073851 16035024600263216550110777)
  ·
    refine ⟨12026268450197412412583083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16035024600263216550110777 12026268450197412412583083)
    ·
      refine ⟨18039402675296118618874625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12026268450197412412583083 18039402675296118618874625)
      ·
        refine ⟨13529552006472088964155969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18039402675296118618874625 13529552006472088964155969)
        ·
          refine ⟨10147164004854066723116977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13529552006472088964155969 10147164004854066723116977)
          ·
            refine ⟨7610373003640550042337733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10147164004854066723116977 7610373003640550042337733)
            ·
              refine ⟨1426944938182603132938325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7610373003640550042337733 1426944938182603132938325)
              ·
                refine ⟨16722010994327380464121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1426944938182603132938325 16722010994327380464121)
                ·
                  rfl

theorem cell22_439641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 8].length) (baseStart_439641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439641 prefixEnd_439641 := by exact prefixLift 439641
  have htrace : WordTrace (prefixWord ++ tailWord_439641) baseStart_439641 baseEnd_439641 := by
    simpa [prefixWord, tailWord_439641, baseEnd_439641] using wordTrace_append hprefix tailTrace_439641
  have hstable : (prefixWord ++ tailWord_439641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439641).length < 2 ^ (prefixWord ++ tailWord_439641).sum := by decide
  have hdescent : baseEnd_439641 < baseStart_439641 := by decide
  rcases family_descends (prefixWord ++ tailWord_439641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439658 : List Nat := [3, 1, 3, 3, 2, 10]
def baseStart_439658 : Nat := 118140960795 + 439658 * 2 ^ 59
def prefixEnd_439658 : Nat := 4983230072969 + 3 ^ 40 * 439658 * 2
def baseEnd_439658 : Nat := 1858073066621778351877

theorem tailTrace_439658 : CollatzResearch.WordTrace tailWord_439658 prefixEnd_439658 1858073066621778351877 := by
  unfold tailWord_439658
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008911160300407113369907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10690429760801085635653085 4008911160300407113369907)
  ·
    refine ⟨6013366740450610670054861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4008911160300407113369907 6013366740450610670054861)
    ·
      refine ⟨2255012527668979001270573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6013366740450610670054861 2255012527668979001270573)
      ·
        refine ⟨845629697875867125476465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2255012527668979001270573 845629697875867125476465)
        ·
          refine ⟨634222273406900344107349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845629697875867125476465 634222273406900344107349)
          ·
            refine ⟨1858073066621778351877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 634222273406900344107349 1858073066621778351877)
            ·
              rfl

theorem cell22_439658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 10].length) (baseStart_439658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439658 prefixEnd_439658 := by exact prefixLift 439658
  have htrace : WordTrace (prefixWord ++ tailWord_439658) baseStart_439658 baseEnd_439658 := by
    simpa [prefixWord, tailWord_439658, baseEnd_439658] using wordTrace_append hprefix tailTrace_439658
  have hstable : (prefixWord ++ tailWord_439658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439658).length < 2 ^ (prefixWord ++ tailWord_439658).sum := by decide
  have hdescent : baseEnd_439658 < baseStart_439658 := by decide
  rcases family_descends (prefixWord ++ tailWord_439658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439671 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_439671 : Nat := 118140960795 + 439671 * 2 ^ 59
def prefixEnd_439671 : Nat := 4983230072969 + 3 ^ 40 * 439671 * 2
def baseEnd_439671 : Nat := 150508368562036345926997

theorem tailTrace_439671 : CollatzResearch.WordTrace tailWord_439671 prefixEnd_439671 150508368562036345926997 := by
  unfold tailWord_439671
  simp only [CollatzResearch.WordTrace]
  refine ⟨16036118790154531673702867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10690745860103021115801911 16036118790154531673702867)
  ·
    refine ⟨24054178185231797510554301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16036118790154531673702867 24054178185231797510554301)
    ·
      refine ⟨9020316819461924066457863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24054178185231797510554301 9020316819461924066457863)
      ·
        refine ⟨13530475229192886099686795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020316819461924066457863 13530475229192886099686795)
        ·
          refine ⟨20295712843789329149530193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13530475229192886099686795 20295712843789329149530193)
          ·
            refine ⟨15221784632841996862147645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20295712843789329149530193 15221784632841996862147645)
            ·
              refine ⟨5708169237315748823305367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15221784632841996862147645 5708169237315748823305367)
              ·
                refine ⟨8562253855973623234958051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708169237315748823305367 8562253855973623234958051)
                ·
                  refine ⟨12843380783960434852437077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8562253855973623234958051 12843380783960434852437077)
                  ·
                    refine ⟨150508368562036345926997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12843380783960434852437077 150508368562036345926997)
                    ·
                      rfl

theorem cell22_439671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_439671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439671 prefixEnd_439671 := by exact prefixLift 439671
  have htrace : WordTrace (prefixWord ++ tailWord_439671) baseStart_439671 baseEnd_439671 := by
    simpa [prefixWord, tailWord_439671, baseEnd_439671] using wordTrace_append hprefix tailTrace_439671
  have hstable : (prefixWord ++ tailWord_439671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439671).length < 2 ^ (prefixWord ++ tailWord_439671).sum := by decide
  have hdescent : baseEnd_439671 < baseStart_439671 := by decide
  rcases family_descends (prefixWord ++ tailWord_439671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439694 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_439694 : Nat := 118140960795 + 439694 * 2 ^ 59
def prefixEnd_439694 : Nat := 4983230072969 + 3 ^ 40 * 439694 * 2
def baseEnd_439694 : Nat := 150516241932071952601927

theorem tailTrace_439694 : CollatzResearch.WordTrace tailWord_439694 prefixEnd_439694 150516241932071952601927 := by
  unfold tailWord_439694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004619708633900825223767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10691305112714137734526757 2004619708633900825223767)
  ·
    refine ⟨3006929562950851237835651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004619708633900825223767 3006929562950851237835651)
    ·
      refine ⟨4510394344426276856753477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3006929562950851237835651 4510394344426276856753477)
      ·
        refine ⟨845698939579926910641277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4510394344426276856753477 845698939579926910641277)
        ·
          refine ⟨317137102342472591490479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 845698939579926910641277 317137102342472591490479)
          ·
            refine ⟨475705653513708887235719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317137102342472591490479 475705653513708887235719)
            ·
              refine ⟨713558480270563330853579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475705653513708887235719 713558480270563330853579)
              ·
                refine ⟨1070337720405844996280369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713558480270563330853579 1070337720405844996280369)
                ·
                  refine ⟨802753290304383747210277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1070337720405844996280369 802753290304383747210277)
                  ·
                    refine ⟨150516241932071952601927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 802753290304383747210277 150516241932071952601927)
                    ·
                      rfl

theorem cell22_439694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_439694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439694 prefixEnd_439694 := by exact prefixLift 439694
  have htrace : WordTrace (prefixWord ++ tailWord_439694) baseStart_439694 baseEnd_439694 := by
    simpa [prefixWord, tailWord_439694, baseEnd_439694] using wordTrace_append hprefix tailTrace_439694
  have hstable : (prefixWord ++ tailWord_439694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439694).length < 2 ^ (prefixWord ++ tailWord_439694).sum := by decide
  have hdescent : baseEnd_439694 < baseStart_439694 := by decide
  rcases family_descends (prefixWord ++ tailWord_439694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439737 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 5]
def baseStart_439737 : Nat := 118140960795 + 439737 * 2 ^ 59
def prefixEnd_439737 : Nat := 4983230072969 + 3 ^ 40 * 439737 * 2
def baseEnd_439737 : Nat := 50176987236944724592265

theorem tailTrace_439737 : CollatzResearch.WordTrace tailWord_439737 prefixEnd_439737 50176987236944724592265 := by
  unfold tailWord_439737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038526007915424945605465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10692350671943616630403643 16038526007915424945605465)
  ·
    refine ⟨12028894505936568709204099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16038526007915424945605465 12028894505936568709204099)
    ·
      refine ⟨18043341758904853063806149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12028894505936568709204099 18043341758904853063806149)
      ·
        refine ⟨3383126579794659949463653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18043341758904853063806149 3383126579794659949463653)
        ·
          refine ⟨634336233711498740524435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3383126579794659949463653 634336233711498740524435)
          ·
            refine ⟨951504350567248110786653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634336233711498740524435 951504350567248110786653)
            ·
              refine ⟨356814131462718041544995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 951504350567248110786653 356814131462718041544995)
              ·
                refine ⟨535221197194077062317493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356814131462718041544995 535221197194077062317493)
                ·
                  refine ⟨50176987236944724592265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535221197194077062317493 50176987236944724592265)
                  ·
                    rfl

theorem cell22_439737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_439737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439737 prefixEnd_439737 := by exact prefixLift 439737
  have htrace : WordTrace (prefixWord ++ tailWord_439737) baseStart_439737 baseEnd_439737 := by
    simpa [prefixWord, tailWord_439737, baseEnd_439737] using wordTrace_append hprefix tailTrace_439737
  have hstable : (prefixWord ++ tailWord_439737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439737).length < 2 ^ (prefixWord ++ tailWord_439737).sum := by decide
  have hdescent : baseEnd_439737 < baseStart_439737 := by decide
  rcases family_descends (prefixWord ++ tailWord_439737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439793 : List Nat := [1, 2, 2, 2, 3, 2, 1, 9]
def baseStart_439793 : Nat := 118140960795 + 439793 * 2 ^ 59
def prefixEnd_439793 : Nat := 4983230072969 + 3 ^ 40 * 439793 * 2
def baseEnd_439793 : Nat := 16727792406140966041847

theorem tailTrace_439793 : CollatzResearch.WordTrace tailWord_439793 prefixEnd_439793 16727792406140966041847 := by
  unfold tailWord_439793
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040568495712546509644033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10693712330475031006429355 16040568495712546509644033)
  ·
    refine ⟨12030426371784409882233025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16040568495712546509644033 12030426371784409882233025)
    ·
      refine ⟨9022819778838307411674769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12030426371784409882233025 9022819778838307411674769)
      ·
        refine ⟨6767114834128730558756077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9022819778838307411674769 6767114834128730558756077)
        ·
          refine ⟨2537668062798273959533529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6767114834128730558756077 2537668062798273959533529)
          ·
            refine ⟨1903251047098705469650147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537668062798273959533529 1903251047098705469650147)
            ·
              refine ⟨2854876570648058204475221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903251047098705469650147 2854876570648058204475221)
              ·
                refine ⟨16727792406140966041847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2854876570648058204475221 16727792406140966041847)
                ·
                  rfl

theorem cell22_439793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 9].length) (baseStart_439793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439793 prefixEnd_439793 := by exact prefixLift 439793
  have htrace : WordTrace (prefixWord ++ tailWord_439793) baseStart_439793 baseEnd_439793 := by
    simpa [prefixWord, tailWord_439793, baseEnd_439793] using wordTrace_append hprefix tailTrace_439793
  have hstable : (prefixWord ++ tailWord_439793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439793).length < 2 ^ (prefixWord ++ tailWord_439793).sum := by decide
  have hdescent : baseEnd_439793 < baseStart_439793 := by decide
  rcases family_descends (prefixWord ++ tailWord_439793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439840 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_439840 : Nat := 118140960795 + 439840 * 2 ^ 59
def prefixEnd_439840 : Nat := 4983230072969 + 3 ^ 40 * 439840 * 2
def baseEnd_439840 : Nat := 150566220715776238451479

theorem tailTrace_439840 : CollatzResearch.WordTrace tailWord_439840 prefixEnd_439840 150566220715776238451479 := by
  unfold tailWord_439840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021141363271136768302487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10694855151028182357736649 8021141363271136768302487)
  ·
    refine ⟨12031712044906705152453731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8021141363271136768302487 12031712044906705152453731)
    ·
      refine ⟨18047568067360057728680597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031712044906705152453731 18047568067360057728680597)
      ·
        refine ⟨845979753157502706031903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18047568067360057728680597 845979753157502706031903)
        ·
          refine ⟨1268969629736254059047855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845979753157502706031903 1268969629736254059047855)
          ·
            refine ⟨1903454444604381088571783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268969629736254059047855 1903454444604381088571783)
            ·
              refine ⟨2855181666906571632857675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903454444604381088571783 2855181666906571632857675)
              ·
                refine ⟨4282772500359857449286513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855181666906571632857675 4282772500359857449286513)
                ·
                  refine ⟨3212079375269893086964885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282772500359857449286513 3212079375269893086964885)
                  ·
                    refine ⟨150566220715776238451479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3212079375269893086964885 150566220715776238451479)
                    ·
                      rfl

theorem cell22_439840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_439840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439840 prefixEnd_439840 := by exact prefixLift 439840
  have htrace : WordTrace (prefixWord ++ tailWord_439840) baseStart_439840 baseEnd_439840 := by
    simpa [prefixWord, tailWord_439840, baseEnd_439840] using wordTrace_append hprefix tailTrace_439840
  have hstable : (prefixWord ++ tailWord_439840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439840).length < 2 ^ (prefixWord ++ tailWord_439840).sum := by decide
  have hdescent : baseEnd_439840 < baseStart_439840 := by decide
  rcases family_descends (prefixWord ++ tailWord_439840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439883 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 10]
def baseStart_439883 : Nat := 118140960795 + 439883 * 2 ^ 59
def prefixEnd_439883 : Nat := 4983230072969 + 3 ^ 40 * 439883 * 2
def baseEnd_439883 : Nat := 50193646831512819875449

theorem tailTrace_439883 : CollatzResearch.WordTrace tailWord_439883 prefixEnd_439883 50193646831512819875449 := by
  unfold tailWord_439883
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043851065386491880420303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10695900710257661253613535 16043851065386491880420303)
  ·
    refine ⟨24065776598079737820630455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16043851065386491880420303 24065776598079737820630455)
    ·
      refine ⟨36098664897119606730945683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24065776598079737820630455 36098664897119606730945683)
      ·
        refine ⟨54147997345679410096418525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36098664897119606730945683 54147997345679410096418525)
        ·
          refine ⟨20305499004629778786156947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54147997345679410096418525 20305499004629778786156947)
          ·
            refine ⟨30458248506944668179235421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20305499004629778786156947 30458248506944668179235421)
            ·
              refine ⟨11421843190104250567213283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30458248506944668179235421 11421843190104250567213283)
              ·
                refine ⟨17132764785156375850819925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421843190104250567213283 17132764785156375850819925)
                ·
                  refine ⟨50193646831512819875449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17132764785156375850819925 50193646831512819875449)
                  ·
                    rfl

theorem cell22_439883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_439883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439883 prefixEnd_439883 := by exact prefixLift 439883
  have htrace : WordTrace (prefixWord ++ tailWord_439883) baseStart_439883 baseEnd_439883 := by
    simpa [prefixWord, tailWord_439883, baseEnd_439883] using wordTrace_append hprefix tailTrace_439883
  have hstable : (prefixWord ++ tailWord_439883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439883).length < 2 ^ (prefixWord ++ tailWord_439883).sum := by decide
  have hdescent : baseEnd_439883 < baseStart_439883 := by decide
  rcases family_descends (prefixWord ++ tailWord_439883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439966 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_439966 : Nat := 118140960795 + 439966 * 2 ^ 59
def prefixEnd_439966 : Nat := 4983230072969 + 3 ^ 40 * 439966 * 2
def baseEnd_439966 : Nat := 150609353090753909801093

theorem tailTrace_439966 : CollatzResearch.WordTrace tailWord_439966 prefixEnd_439966 150609353090753909801093 := by
  unfold tailWord_439966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005859790510724631961469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10697918882723864703794501 2005859790510724631961469)
  ·
    refine ⟨752197421441521736985551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2005859790510724631961469 752197421441521736985551)
    ·
      refine ⟨1128296132162282605478327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752197421441521736985551 1128296132162282605478327)
      ·
        refine ⟨1692444198243423908217491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128296132162282605478327 1692444198243423908217491)
        ·
          refine ⟨2538666297365135862326237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692444198243423908217491 2538666297365135862326237)
          ·
            refine ⟨951999861511925948372339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2538666297365135862326237 951999861511925948372339)
            ·
              refine ⟨1427999792267888922558509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951999861511925948372339 1427999792267888922558509)
              ·
                refine ⟨535499922100458345959441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1427999792267888922558509 535499922100458345959441)
                ·
                  refine ⟨401624941575343759469581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535499922100458345959441 401624941575343759469581)
                  ·
                    refine ⟨150609353090753909801093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 401624941575343759469581 150609353090753909801093)
                    ·
                      rfl

theorem cell22_439966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_439966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_439966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_439966 prefixEnd_439966 := by exact prefixLift 439966
  have htrace : WordTrace (prefixWord ++ tailWord_439966) baseStart_439966 baseEnd_439966 := by
    simpa [prefixWord, tailWord_439966, baseEnd_439966] using wordTrace_append hprefix tailTrace_439966
  have hstable : (prefixWord ++ tailWord_439966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439966).length < 2 ^ (prefixWord ++ tailWord_439966).sum := by decide
  have hdescent : baseEnd_439966 < baseStart_439966 := by decide
  rcases family_descends (prefixWord ++ tailWord_439966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440002 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_440002 : Nat := 118140960795 + 440002 * 2 ^ 59
def prefixEnd_440002 : Nat := 4983230072969 + 3 ^ 40 * 440002 * 2
def baseEnd_440002 : Nat := 50207225542153938633661

theorem tailTrace_440002 : CollatzResearch.WordTrace tailWord_440002 prefixEnd_440002 50207225542153938633661 := by
  unfold tailWord_440002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012047837988843801000565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10698794234636916802668173 4012047837988843801000565)
  ·
    refine ⟨376129484811454106343803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4012047837988843801000565 376129484811454106343803)
    ·
      refine ⟨564194227217181159515705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376129484811454106343803 564194227217181159515705)
      ·
        refine ⟨423145670412885869636779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564194227217181159515705 423145670412885869636779)
        ·
          refine ⟨634718505619328804455169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423145670412885869636779 634718505619328804455169)
          ·
            refine ⟨476038879214496603341377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634718505619328804455169 476038879214496603341377)
            ·
              refine ⟨357029159410872452506033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476038879214496603341377 357029159410872452506033)
              ·
                refine ⟨267771869558154339379525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357029159410872452506033 267771869558154339379525)
                ·
                  refine ⟨50207225542153938633661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267771869558154339379525 50207225542153938633661)
                  ·
                    rfl

theorem cell22_440002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_440002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440002 prefixEnd_440002 := by exact prefixLift 440002
  have htrace : WordTrace (prefixWord ++ tailWord_440002) baseStart_440002 baseEnd_440002 := by
    simpa [prefixWord, tailWord_440002, baseEnd_440002] using wordTrace_append hprefix tailTrace_440002
  have hstable : (prefixWord ++ tailWord_440002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440002).length < 2 ^ (prefixWord ++ tailWord_440002).sum := by decide
  have hdescent : baseEnd_440002 < baseStart_440002 := by decide
  rcases family_descends (prefixWord ++ tailWord_440002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440005 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_440005 : Nat := 118140960795 + 440005 * 2 ^ 59
def prefixEnd_440005 : Nat := 4983230072969 + 3 ^ 40 * 440005 * 2
def baseEnd_440005 : Nat := 150622703587770808075973

theorem tailTrace_440005 : CollatzResearch.WordTrace tailWord_440005 prefixEnd_440005 150622703587770808075973 := by
  unfold tailWord_440005
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048300770944506716361469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10698867180629671144240979 16048300770944506716361469)
  ·
    refine ⟨6018112789104190018635551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16048300770944506716361469 6018112789104190018635551)
    ·
      refine ⟨9027169183656285027953327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6018112789104190018635551 9027169183656285027953327)
      ·
        refine ⟨13540753775484427541929991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027169183656285027953327 13540753775484427541929991)
        ·
          refine ⟨20311130663226641312894987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13540753775484427541929991 20311130663226641312894987)
          ·
            refine ⟨30466695994839961969342481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20311130663226641312894987 30466695994839961969342481)
            ·
              refine ⟨22850021996129971477006861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30466695994839961969342481 22850021996129971477006861)
              ·
                refine ⟨8568758248548739303877573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22850021996129971477006861 8568758248548739303877573)
                ·
                  refine ⟨1606642171602888619477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8568758248548739303877573 1606642171602888619477045)
                  ·
                    refine ⟨150622703587770808075973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1606642171602888619477045 150622703587770808075973)
                    ·
                      rfl

theorem cell22_440005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_440005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440005 prefixEnd_440005 := by exact prefixLift 440005
  have htrace : WordTrace (prefixWord ++ tailWord_440005) baseStart_440005 baseEnd_440005 := by
    simpa [prefixWord, tailWord_440005, baseEnd_440005] using wordTrace_append hprefix tailTrace_440005
  have hstable : (prefixWord ++ tailWord_440005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440005).length < 2 ^ (prefixWord ++ tailWord_440005).sum := by decide
  have hdescent : baseEnd_440005 < baseStart_440005 := by decide
  rcases family_descends (prefixWord ++ tailWord_440005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440007 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 5]
def baseStart_440007 : Nat := 118140960795 + 440007 * 2 ^ 59
def prefixEnd_440007 : Nat := 4983230072969 + 3 ^ 40 * 440007 * 2
def baseEnd_440007 : Nat := 50207796076214489841989

theorem tailTrace_440007 : CollatzResearch.WordTrace tailWord_440007 prefixEnd_440007 50207796076214489841989 := by
  unfold tailWord_440007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048373716937261057934275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10698915811291507371956183 16048373716937261057934275)
  ·
    refine ⟨24072560575405891586901413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16048373716937261057934275 24072560575405891586901413)
    ·
      refine ⟨4513605107888604672544015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24072560575405891586901413 4513605107888604672544015)
      ·
        refine ⟨6770407661832907008816023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513605107888604672544015 6770407661832907008816023)
        ·
          refine ⟨10155611492749360513224035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770407661832907008816023 10155611492749360513224035)
          ·
            refine ⟨15233417239124040769836053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10155611492749360513224035 15233417239124040769836053)
            ·
              refine ⟨714066433083939411086065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15233417239124040769836053 714066433083939411086065)
              ·
                refine ⟨535549824812954558314549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714066433083939411086065 535549824812954558314549)
                ·
                  refine ⟨50207796076214489841989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 535549824812954558314549 50207796076214489841989)
                  ·
                    rfl

theorem cell22_440007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 5].length) (baseStart_440007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440007 prefixEnd_440007 := by exact prefixLift 440007
  have htrace : WordTrace (prefixWord ++ tailWord_440007) baseStart_440007 baseEnd_440007 := by
    simpa [prefixWord, tailWord_440007, baseEnd_440007] using wordTrace_append hprefix tailTrace_440007
  have hstable : (prefixWord ++ tailWord_440007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440007).length < 2 ^ (prefixWord ++ tailWord_440007).sum := by decide
  have hdescent : baseEnd_440007 < baseStart_440007 := by decide
  rcases family_descends (prefixWord ++ tailWord_440007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440037 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_440037 : Nat := 118140960795 + 440037 * 2 ^ 59
def prefixEnd_440037 : Nat := 4983230072969 + 3 ^ 40 * 440037 * 2
def baseEnd_440037 : Nat := 150633657841733391275875

theorem tailTrace_440037 : CollatzResearch.WordTrace tailWord_440037 prefixEnd_440037 150633657841733391275875 := by
  unfold tailWord_440037
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049467906828576181526365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10699645271219050787684243 16049467906828576181526365)
  ·
    refine ⟨6018550465060716068072387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16049467906828576181526365 6018550465060716068072387)
    ·
      refine ⟨9027825697591074102108581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6018550465060716068072387 9027825697591074102108581)
      ·
        refine ⟨1692717318298326394145359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9027825697591074102108581 1692717318298326394145359)
        ·
          refine ⟨2539075977447489591218039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692717318298326394145359 2539075977447489591218039)
          ·
            refine ⟨3808613966171234386827059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539075977447489591218039 3808613966171234386827059)
            ·
              refine ⟨5712920949256851580240589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808613966171234386827059 5712920949256851580240589)
              ·
                refine ⟨2142345355971319342590221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5712920949256851580240589 2142345355971319342590221)
                ·
                  refine ⟨803379508489244753471333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2142345355971319342590221 803379508489244753471333)
                  ·
                    refine ⟨150633657841733391275875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 803379508489244753471333 150633657841733391275875)
                    ·
                      rfl

theorem cell22_440037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_440037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440037 prefixEnd_440037 := by exact prefixLift 440037
  have htrace : WordTrace (prefixWord ++ tailWord_440037) baseStart_440037 baseEnd_440037 := by
    simpa [prefixWord, tailWord_440037, baseEnd_440037] using wordTrace_append hprefix tailTrace_440037
  have hstable : (prefixWord ++ tailWord_440037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440037).length < 2 ^ (prefixWord ++ tailWord_440037).sum := by decide
  have hdescent : baseEnd_440037 < baseStart_440037 := by decide
  rcases family_descends (prefixWord ++ tailWord_440037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440097 : List Nat := [1, 2, 3, 2, 1, 4, 1, 8]
def baseStart_440097 : Nat := 118140960795 + 440097 * 2 ^ 59
def prefixEnd_440097 : Nat := 4983230072969 + 3 ^ 40 * 440097 * 2
def baseEnd_440097 : Nat := 16739355229768137197299

theorem tailTrace_440097 : CollatzResearch.WordTrace tailWord_440097 prefixEnd_440097 16739355229768137197299 := by
  unfold tailWord_440097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16051656286611206428710545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10701104191074137619140363 16051656286611206428710545)
  ·
    refine ⟨12038742214958404821532909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16051656286611206428710545 12038742214958404821532909)
    ·
      refine ⟨4514528330609401808074841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12038742214958404821532909 4514528330609401808074841)
      ·
        refine ⟨3385896247957051356056131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4514528330609401808074841 3385896247957051356056131)
        ·
          refine ⟨5078844371935577034084197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385896247957051356056131 5078844371935577034084197)
          ·
            refine ⟨952283319737920693890787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5078844371935577034084197 952283319737920693890787)
            ·
              refine ⟨1428424979606881040836181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952283319737920693890787 1428424979606881040836181)
              ·
                refine ⟨16739355229768137197299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1428424979606881040836181 16739355229768137197299)
                ·
                  rfl

theorem cell22_440097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 8].length) (baseStart_440097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440097 prefixEnd_440097 := by exact prefixLift 440097
  have htrace : WordTrace (prefixWord ++ tailWord_440097) baseStart_440097 baseEnd_440097 := by
    simpa [prefixWord, tailWord_440097, baseEnd_440097] using wordTrace_append hprefix tailTrace_440097
  have hstable : (prefixWord ++ tailWord_440097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440097).length < 2 ^ (prefixWord ++ tailWord_440097).sum := by decide
  have hdescent : baseEnd_440097 < baseStart_440097 := by decide
  rcases family_descends (prefixWord ++ tailWord_440097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440116 : List Nat := [2, 5, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_440116 : Nat := 118140960795 + 440116 * 2 ^ 59
def prefixEnd_440116 : Nat := 4983230072969 + 3 ^ 40 * 440116 * 2
def baseEnd_440116 : Nat := 150660701156203518550633

theorem tailTrace_440116 : CollatzResearch.WordTrace tailWord_440116 prefixEnd_440116 150660701156203518550633 := by
  unfold tailWord_440116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026174636771186336826101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10701566182361581782434801 8026174636771186336826101)
  ·
    refine ⟨752453872197298719077447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8026174636771186336826101 752453872197298719077447)
    ·
      refine ⟨1128680808295948078616171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752453872197298719077447 1128680808295948078616171)
      ·
        refine ⟨1693021212443922117924257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128680808295948078616171 1693021212443922117924257)
        ·
          refine ⟨1269765909332941588443193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693021212443922117924257 1269765909332941588443193)
          ·
            refine ⟨952324431999706191332395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269765909332941588443193 952324431999706191332395)
            ·
              refine ⟨1428486647999559286998593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952324431999706191332395 1428486647999559286998593)
              ·
                refine ⟨1071364985999669465248945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428486647999559286998593 1071364985999669465248945)
                ·
                  refine ⟨803523739499752098936709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1071364985999669465248945 803523739499752098936709)
                  ·
                    refine ⟨150660701156203518550633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 803523739499752098936709 150660701156203518550633)
                    ·
                      rfl

theorem cell22_440116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_440116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440116 prefixEnd_440116 := by exact prefixLift 440116
  have htrace : WordTrace (prefixWord ++ tailWord_440116) baseStart_440116 baseEnd_440116 := by
    simpa [prefixWord, tailWord_440116, baseEnd_440116] using wordTrace_append hprefix tailTrace_440116
  have hstable : (prefixWord ++ tailWord_440116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440116).length < 2 ^ (prefixWord ++ tailWord_440116).sum := by decide
  have hdescent : baseEnd_440116 < baseStart_440116 := by decide
  rcases family_descends (prefixWord ++ tailWord_440116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440187 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 6]
def baseStart_440187 : Nat := 118140960795 + 440187 * 2 ^ 59
def prefixEnd_440187 : Nat := 4983230072969 + 3 ^ 40 * 440187 * 2
def baseEnd_440187 : Nat := 50228335302394333341805

theorem tailTrace_440187 : CollatzResearch.WordTrace tailWord_440187 prefixEnd_440187 50228335302394333341805 := by
  unfold tailWord_440187
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054938856285151799486815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10703292570856767866324543 16054938856285151799486815)
  ·
    refine ⟨24082408284427727699230223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16054938856285151799486815 24082408284427727699230223)
    ·
      refine ⟨36123612426641591548845335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24082408284427727699230223 36123612426641591548845335)
      ·
        refine ⟨54185418639962387323268003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36123612426641591548845335 54185418639962387323268003)
        ·
          refine ⟨81278127959943580984902005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54185418639962387323268003 81278127959943580984902005)
          ·
            refine ⟨7619824496244710717334563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81278127959943580984902005 7619824496244710717334563)
            ·
              refine ⟨11429736744367066076001845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619824496244710717334563 11429736744367066076001845)
              ·
                refine ⟨1071537819784412444625173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11429736744367066076001845 1071537819784412444625173)
                ·
                  refine ⟨50228335302394333341805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1071537819784412444625173 50228335302394333341805)
                  ·
                    rfl

theorem cell22_440187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_440187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440187 prefixEnd_440187 := by exact prefixLift 440187
  have htrace : WordTrace (prefixWord ++ tailWord_440187) baseStart_440187 baseEnd_440187 := by
    simpa [prefixWord, tailWord_440187, baseEnd_440187] using wordTrace_append hprefix tailTrace_440187
  have hstable : (prefixWord ++ tailWord_440187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440187).length < 2 ^ (prefixWord ++ tailWord_440187).sum := by decide
  have hdescent : baseEnd_440187 < baseStart_440187 := by decide
  rcases family_descends (prefixWord ++ tailWord_440187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440214 : List Nat := [5, 3, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_440214 : Nat := 118140960795 + 440214 * 2 ^ 59
def prefixEnd_440214 : Nat := 4983230072969 + 3 ^ 40 * 440214 * 2
def baseEnd_440214 : Nat := 150694248558963929600333

theorem tailTrace_440214 : CollatzResearch.WordTrace tailWord_440214 prefixEnd_440214 150694248558963929600333 := by
  unfold tailWord_440214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003495226699208463169981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10703949084791556940479797 1003495226699208463169981)
  ·
    refine ⟨376310710012203173688743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1003495226699208463169981 376310710012203173688743)
    ·
      refine ⟨564466065018304760533115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376310710012203173688743 564466065018304760533115)
      ·
        refine ⟨846699097527457140799673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564466065018304760533115 846699097527457140799673)
        ·
          refine ⟨635024323145592855599755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846699097527457140799673 635024323145592855599755)
          ·
            refine ⟨952536484718389283399633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635024323145592855599755 952536484718389283399633)
            ·
              refine ⟨714402363538791962549725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952536484718389283399633 714402363538791962549725)
              ·
                refine ⟨267900886327046985956147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 714402363538791962549725 267900886327046985956147)
                ·
                  refine ⟨401851329490570478934221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267900886327046985956147 401851329490570478934221)
                  ·
                    refine ⟨150694248558963929600333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 401851329490570478934221 150694248558963929600333)
                    ·
                      rfl

theorem cell22_440214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_440214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440214 prefixEnd_440214 := by exact prefixLift 440214
  have htrace : WordTrace (prefixWord ++ tailWord_440214) baseStart_440214 baseEnd_440214 := by
    simpa [prefixWord, tailWord_440214, baseEnd_440214] using wordTrace_append hprefix tailTrace_440214
  have hstable : (prefixWord ++ tailWord_440214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440214).length < 2 ^ (prefixWord ++ tailWord_440214).sum := by decide
  have hdescent : baseEnd_440214 < baseStart_440214 := by decide
  rcases family_descends (prefixWord ++ tailWord_440214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440221 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 4]
def baseStart_440221 : Nat := 118140960795 + 440221 * 2 ^ 59
def prefixEnd_440221 : Nat := 4983230072969 + 3 ^ 40 * 440221 * 2
def baseEnd_440221 : Nat := 50232214934006081558437

theorem tailTrace_440221 : CollatzResearch.WordTrace tailWord_440221 prefixEnd_440221 50232214934006081558437 := by
  unfold tailWord_440221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056178938161975606224517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10704119292107983737483011 16056178938161975606224517)
  ·
    refine ⟨3010533550905370426167097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16056178938161975606224517 3010533550905370426167097)
    ·
      refine ⟨2257900163179027819625323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3010533550905370426167097 2257900163179027819625323)
      ·
        refine ⟨3386850244768541729437985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257900163179027819625323 3386850244768541729437985)
        ·
          refine ⟨2540137683576406297078489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386850244768541729437985 2540137683576406297078489)
          ·
            refine ⟨1905103262682304722808867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2540137683576406297078489 1905103262682304722808867)
            ·
              refine ⟨2857654894023457084213301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905103262682304722808867 2857654894023457084213301)
              ·
                refine ⟨267905146314699101644997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2857654894023457084213301 267905146314699101644997)
                ·
                  refine ⟨50232214934006081558437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 267905146314699101644997 50232214934006081558437)
                  ·
                    rfl

theorem cell22_440221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_440221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440221 prefixEnd_440221 := by exact prefixLift 440221
  have htrace : WordTrace (prefixWord ++ tailWord_440221) baseStart_440221 baseEnd_440221 := by
    simpa [prefixWord, tailWord_440221, baseEnd_440221] using wordTrace_append hprefix tailTrace_440221
  have hstable : (prefixWord ++ tailWord_440221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440221).length < 2 ^ (prefixWord ++ tailWord_440221).sum := by decide
  have hdescent : baseEnd_440221 < baseStart_440221 := by decide
  rcases family_descends (prefixWord ++ tailWord_440221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440405 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 2, 3]
def baseStart_440405 : Nat := 118140960795 + 440405 * 2 ^ 59
def prefixEnd_440405 : Nat := 4983230072969 + 3 ^ 40 * 440405 * 2
def baseEnd_440405 : Nat := 150759631762303098074747

theorem tailTrace_440405 : CollatzResearch.WordTrace tailWord_440405 prefixEnd_440405 150759631762303098074747 := by
  unfold tailWord_440405
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062889969495375030922669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10708593312996916687281779 16062889969495375030922669)
  ·
    refine ⟨6023583738560765636596001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16062889969495375030922669 6023583738560765636596001)
    ·
      refine ⟨4517687803920574227447001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6023583738560765636596001 4517687803920574227447001)
      ·
        refine ⟨3388265852940430670585251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517687803920574227447001 3388265852940430670585251)
        ·
          refine ⟨5082398779410646005877877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388265852940430670585251 5082398779410646005877877)
          ·
            refine ⟨476474885569748063051051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5082398779410646005877877 476474885569748063051051)
            ·
              refine ⟨714712328354622094576577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476474885569748063051051 714712328354622094576577)
              ·
                refine ⟨536034246265966570932433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714712328354622094576577 536034246265966570932433)
                ·
                  refine ⟨402025684699474928199325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536034246265966570932433 402025684699474928199325)
                  ·
                    refine ⟨150759631762303098074747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402025684699474928199325 150759631762303098074747)
                    ·
                      rfl

theorem cell22_440405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_440405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440405 prefixEnd_440405 := by exact prefixLift 440405
  have htrace : WordTrace (prefixWord ++ tailWord_440405) baseStart_440405 baseEnd_440405 := by
    simpa [prefixWord, tailWord_440405, baseEnd_440405] using wordTrace_append hprefix tailTrace_440405
  have hstable : (prefixWord ++ tailWord_440405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440405).length < 2 ^ (prefixWord ++ tailWord_440405).sum := by decide
  have hdescent : baseEnd_440405 < baseStart_440405 := by decide
  rcases family_descends (prefixWord ++ tailWord_440405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440480 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 5]
def baseStart_440480 : Nat := 118140960795 + 440480 * 2 ^ 59
def prefixEnd_440480 : Nat := 4983230072969 + 3 ^ 40 * 440480 * 2
def baseEnd_440480 : Nat := 50261768598342634149839

theorem tailTrace_440480 : CollatzResearch.WordTrace tailWord_440480 prefixEnd_440480 50261768598342634149839 := by
  unfold tailWord_440480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032812722111831419951447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10710416962815775226601929 8032812722111831419951447)
  ·
    refine ⟨12049219083167747129927171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8032812722111831419951447 12049219083167747129927171)
    ·
      refine ⟨18073828624751620694890757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12049219083167747129927171 18073828624751620694890757)
      ·
        refine ⟨3388842867140928880292017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18073828624751620694890757 3388842867140928880292017)
        ·
          refine ⟨2541632150355696660219013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388842867140928880292017 2541632150355696660219013)
          ·
            refine ⟨476556028191693123791065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2541632150355696660219013 476556028191693123791065)
            ·
              refine ⟨357417021143769842843299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476556028191693123791065 357417021143769842843299)
              ·
                refine ⟨536125531715654764264949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357417021143769842843299 536125531715654764264949)
                ·
                  refine ⟨50261768598342634149839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 536125531715654764264949 50261768598342634149839)
                  ·
                    rfl

theorem cell22_440480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 5].length) (baseStart_440480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440480 prefixEnd_440480 := by exact prefixLift 440480
  have htrace : WordTrace (prefixWord ++ tailWord_440480) baseStart_440480 baseEnd_440480 := by
    simpa [prefixWord, tailWord_440480, baseEnd_440480] using wordTrace_append hprefix tailTrace_440480
  have hstable : (prefixWord ++ tailWord_440480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440480).length < 2 ^ (prefixWord ++ tailWord_440480).sum := by decide
  have hdescent : baseEnd_440480 < baseStart_440480 := by decide
  rcases family_descends (prefixWord ++ tailWord_440480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440506 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_440506 : Nat := 118140960795 + 440506 * 2 ^ 59
def prefixEnd_440506 : Nat := 4983230072969 + 3 ^ 40 * 440506 * 2
def baseEnd_440506 : Nat := 150794206126372501299437

theorem tailTrace_440506 : CollatzResearch.WordTrace tailWord_440506 prefixEnd_440506 150794206126372501299437 := by
  unfold tailWord_440506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016643435532367320087343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10711049161419646186899581 4016643435532367320087343)
  ·
    refine ⟨6024965153298550980131015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4016643435532367320087343 6024965153298550980131015)
    ·
      refine ⟨9037447729947826470196523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6024965153298550980131015 9037447729947826470196523)
      ·
        refine ⟨13556171594921739705294785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9037447729947826470196523 13556171594921739705294785)
        ·
          refine ⟨10167128696191304778971089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13556171594921739705294785 10167128696191304778971089)
          ·
            refine ⟨7625346522143478584228317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10167128696191304778971089 7625346522143478584228317)
            ·
              refine ⟨2859504945803804469085619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7625346522143478584228317 2859504945803804469085619)
              ·
                refine ⟨4289257418705706703628429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859504945803804469085619 4289257418705706703628429)
                ·
                  refine ⟨1608471532014640013860661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4289257418705706703628429 1608471532014640013860661)
                  ·
                    refine ⟨150794206126372501299437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1608471532014640013860661 150794206126372501299437)
                    ·
                      rfl

theorem cell22_440506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_440506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440506 prefixEnd_440506 := by exact prefixLift 440506
  have htrace : WordTrace (prefixWord ++ tailWord_440506) baseStart_440506 baseEnd_440506 := by
    simpa [prefixWord, tailWord_440506, baseEnd_440506] using wordTrace_append hprefix tailTrace_440506
  have hstable : (prefixWord ++ tailWord_440506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440506).length < 2 ^ (prefixWord ++ tailWord_440506).sum := by decide
  have hdescent : baseEnd_440506 < baseStart_440506 := by decide
  rcases family_descends (prefixWord ++ tailWord_440506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_440521 : Nat := 118140960795 + 440521 * 2 ^ 59
def prefixEnd_440521 : Nat := 4983230072969 + 3 ^ 40 * 440521 * 2
def baseEnd_440521 : Nat := 150799340932917462174391

theorem tailTrace_440521 : CollatzResearch.WordTrace tailWord_440521 prefixEnd_440521 150799340932917462174391 := by
  unfold tailWord_440521
  simp only [CollatzResearch.WordTrace]
  refine ⟨16067120837075126842145417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10711413891383417894763611 16067120837075126842145417)
  ·
    refine ⟨12050340627806345131609063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16067120837075126842145417 12050340627806345131609063)
    ·
      refine ⟨18075510941709517697413595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12050340627806345131609063 18075510941709517697413595)
      ·
        refine ⟨27113266412564276546120393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18075510941709517697413595 27113266412564276546120393)
        ·
          refine ⟨20334949809423207409590295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27113266412564276546120393 20334949809423207409590295)
          ·
            refine ⟨30502424714134811114385443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20334949809423207409590295 30502424714134811114385443)
            ·
              refine ⟨45753637071202216671578165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30502424714134811114385443 45753637071202216671578165)
              ·
                refine ⟨4289403475425207812960453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45753637071202216671578165 4289403475425207812960453)
                ·
                  refine ⟨804263151642226464930085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4289403475425207812960453 804263151642226464930085)
                  ·
                    refine ⟨150799340932917462174391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804263151642226464930085 150799340932917462174391)
                    ·
                      rfl

theorem cell22_440521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_440521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440521 prefixEnd_440521 := by exact prefixLift 440521
  have htrace : WordTrace (prefixWord ++ tailWord_440521) baseStart_440521 baseEnd_440521 := by
    simpa [prefixWord, tailWord_440521, baseEnd_440521] using wordTrace_append hprefix tailTrace_440521
  have hstable : (prefixWord ++ tailWord_440521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440521).length < 2 ^ (prefixWord ++ tailWord_440521).sum := by decide
  have hdescent : baseEnd_440521 < baseStart_440521 := by decide
  rcases family_descends (prefixWord ++ tailWord_440521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440585 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 3, 3]
def baseStart_440585 : Nat := 118140960795 + 440585 * 2 ^ 59
def prefixEnd_440585 : Nat := 4983230072969 + 3 ^ 40 * 440585 * 2
def baseEnd_440585 : Nat := 150821249440842628574195

theorem tailTrace_440585 : CollatzResearch.WordTrace tailWord_440585 prefixEnd_440585 150821249440842628574195 := by
  unfold tailWord_440585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069455108843265772475209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10712970072562177181650139 16069455108843265772475209)
  ·
    refine ⟨12052091331632449329356407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16069455108843265772475209 12052091331632449329356407)
    ·
      refine ⟨18078136997448673994034611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12052091331632449329356407 18078136997448673994034611)
      ·
        refine ⟨27117205496173010991051917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18078136997448673994034611 27117205496173010991051917)
        ·
          refine ⟨10168952061064879121644469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27117205496173010991051917 10168952061064879121644469)
          ·
            refine ⟨953339255724832417654169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10168952061064879121644469 953339255724832417654169)
            ·
              refine ⟨715004441793624313240627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953339255724832417654169 715004441793624313240627)
              ·
                refine ⟨1072506662690436469860941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715004441793624313240627 1072506662690436469860941)
                ·
                  refine ⟨402189998508913676197853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072506662690436469860941 402189998508913676197853)
                  ·
                    refine ⟨150821249440842628574195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402189998508913676197853 150821249440842628574195)
                    ·
                      rfl

theorem cell22_440585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3, 3].length) (baseStart_440585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440585 prefixEnd_440585 := by exact prefixLift 440585
  have htrace : WordTrace (prefixWord ++ tailWord_440585) baseStart_440585 baseEnd_440585 := by
    simpa [prefixWord, tailWord_440585, baseEnd_440585] using wordTrace_append hprefix tailTrace_440585
  have hstable : (prefixWord ++ tailWord_440585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440585).length < 2 ^ (prefixWord ++ tailWord_440585).sum := by decide
  have hdescent : baseEnd_440585 < baseStart_440585 := by decide
  rcases family_descends (prefixWord ++ tailWord_440585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440643 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 6]
def baseStart_440643 : Nat := 118140960795 + 440643 * 2 ^ 59
def prefixEnd_440643 : Nat := 4983230072969 + 3 ^ 40 * 440643 * 2
def baseEnd_440643 : Nat := 50280368008716603541339

theorem tailTrace_440643 : CollatzResearch.WordTrace tailWord_440643 prefixEnd_440643 50280368008716603541339 := by
  unfold tailWord_440643
  simp only [CollatzResearch.WordTrace]
  refine ⟨16071570542633141678086583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10714380361755427785391055 16071570542633141678086583)
  ·
    refine ⟨24107355813949712517129875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16071570542633141678086583 24107355813949712517129875)
    ·
      refine ⟨36161033720924568775694813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24107355813949712517129875 36161033720924568775694813)
      ·
        refine ⟨13560387645346713290885555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36161033720924568775694813 13560387645346713290885555)
        ·
          refine ⟨20340581468020069936328333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13560387645346713290885555 20340581468020069936328333)
          ·
            refine ⟨7627718050507526226123125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20340581468020069936328333 7627718050507526226123125)
            ·
              refine ⟨715098567235080583699043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7627718050507526226123125 715098567235080583699043)
              ·
                refine ⟨1072647850852620875548565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715098567235080583699043 1072647850852620875548565)
                ·
                  refine ⟨50280368008716603541339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1072647850852620875548565 50280368008716603541339)
                  ·
                    rfl

theorem cell22_440643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 6].length) (baseStart_440643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440643 prefixEnd_440643 := by exact prefixLift 440643
  have htrace : WordTrace (prefixWord ++ tailWord_440643) baseStart_440643 baseEnd_440643 := by
    simpa [prefixWord, tailWord_440643, baseEnd_440643] using wordTrace_append hprefix tailTrace_440643
  have hstable : (prefixWord ++ tailWord_440643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440643).length < 2 ^ (prefixWord ++ tailWord_440643).sum := by decide
  have hdescent : baseEnd_440643 < baseStart_440643 := by decide
  rcases family_descends (prefixWord ++ tailWord_440643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440690 : List Nat := [3, 2, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_440690 : Nat := 118140960795 + 440690 * 2 ^ 59
def prefixEnd_440690 : Nat := 4983230072969 + 3 ^ 40 * 440690 * 2
def baseEnd_440690 : Nat := 150857193086657354698873

theorem tailTrace_440690 : CollatzResearch.WordTrace tailWord_440690 prefixEnd_440690 150857193086657354698873 := by
  unfold tailWord_440690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018321193365717176261881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10715523182308579136698349 4018321193365717176261881)
  ·
    refine ⟨3013740895024287882196411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4018321193365717176261881 3013740895024287882196411)
    ·
      refine ⟨4520611342536431823294617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3013740895024287882196411 4520611342536431823294617)
      ·
        refine ⟨3390458506902323867470963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4520611342536431823294617 3390458506902323867470963)
        ·
          refine ⟨5085687760353485801206445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390458506902323867470963 5085687760353485801206445)
          ·
            refine ⟨1907132910132557175452417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5085687760353485801206445 1907132910132557175452417)
            ·
              refine ⟨1430349682599417881589313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907132910132557175452417 1430349682599417881589313)
              ·
                refine ⟨1072762261949563411191985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430349682599417881589313 1072762261949563411191985)
                ·
                  refine ⟨804571696462172558393989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072762261949563411191985 804571696462172558393989)
                  ·
                    refine ⟨150857193086657354698873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804571696462172558393989 150857193086657354698873)
                    ·
                      rfl

theorem cell22_440690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_440690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440690 prefixEnd_440690 := by exact prefixLift 440690
  have htrace : WordTrace (prefixWord ++ tailWord_440690) baseStart_440690 baseEnd_440690 := by
    simpa [prefixWord, tailWord_440690, baseEnd_440690] using wordTrace_append hprefix tailTrace_440690
  have hstable : (prefixWord ++ tailWord_440690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440690).length < 2 ^ (prefixWord ++ tailWord_440690).sum := by decide
  have hdescent : baseEnd_440690 < baseStart_440690 := by decide
  rcases family_descends (prefixWord ++ tailWord_440690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440705 : List Nat := [1, 2, 4, 3, 1, 1, 3, 7]
def baseStart_440705 : Nat := 118140960795 + 440705 * 2 ^ 59
def prefixEnd_440705 : Nat := 4983230072969 + 3 ^ 40 * 440705 * 2
def baseEnd_440705 : Nat := 16762480877022479508203

theorem tailTrace_440705 : CollatzResearch.WordTrace tailWord_440705 prefixEnd_440705 16762480877022479508203 := by
  unfold tailWord_440705
  simp only [CollatzResearch.WordTrace]
  refine ⟨16073831868408526266843569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10715887912272350844562379 16073831868408526266843569)
  ·
    refine ⟨12055373901306394700132677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16073831868408526266843569 12055373901306394700132677)
    ·
      refine ⟨2260382606494949006274877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12055373901306394700132677 2260382606494949006274877)
      ·
        refine ⟨847643477435605877353079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2260382606494949006274877 847643477435605877353079)
        ·
          refine ⟨1271465216153408816029619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847643477435605877353079 1271465216153408816029619)
          ·
            refine ⟨1907197824230113224044429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271465216153408816029619 1907197824230113224044429)
            ·
              refine ⟨715199184086292459016661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1907197824230113224044429 715199184086292459016661)
              ·
                refine ⟨16762480877022479508203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 715199184086292459016661 16762480877022479508203)
                ·
                  rfl

theorem cell22_440705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 7].length) (baseStart_440705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440705 prefixEnd_440705 := by exact prefixLift 440705
  have htrace : WordTrace (prefixWord ++ tailWord_440705) baseStart_440705 baseEnd_440705 := by
    simpa [prefixWord, tailWord_440705, baseEnd_440705] using wordTrace_append hprefix tailTrace_440705
  have hstable : (prefixWord ++ tailWord_440705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440705).length < 2 ^ (prefixWord ++ tailWord_440705).sum := by decide
  have hdescent : baseEnd_440705 < baseStart_440705 := by decide
  rcases family_descends (prefixWord ++ tailWord_440705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440724 : List Nat := [2, 4, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_440724 : Nat := 118140960795 + 440724 * 2 ^ 59
def prefixEnd_440724 : Nat := 4983230072969 + 3 ^ 40 * 440724 * 2
def baseEnd_440724 : Nat := 150868831981492599348769

theorem tailTrace_440724 : CollatzResearch.WordTrace tailWord_440724 prefixEnd_440724 150868831981492599348769 := by
  unfold tailWord_440724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037262427669846255892613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10716349903559795007856817 8037262427669846255892613)
  ·
    refine ⟨1506986705188096172979865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8037262427669846255892613 1506986705188096172979865)
    ·
      refine ⟨1130240028891072129734899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1506986705188096172979865 1130240028891072129734899)
      ·
        refine ⟨1695360043336608194602349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130240028891072129734899 1695360043336608194602349)
        ·
          refine ⟨635760016251228072975881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1695360043336608194602349 635760016251228072975881)
          ·
            refine ⟨476820012188421054731911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635760016251228072975881 476820012188421054731911)
            ·
              refine ⟨715230018282631582097867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476820012188421054731911 715230018282631582097867)
              ·
                refine ⟨1072845027423947373146801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715230018282631582097867 1072845027423947373146801)
                ·
                  refine ⟨804633770567960529860101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1072845027423947373146801 804633770567960529860101)
                  ·
                    refine ⟨150868831981492599348769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804633770567960529860101 150868831981492599348769)
                    ·
                      rfl

theorem cell22_440724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_440724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440724 prefixEnd_440724 := by exact prefixLift 440724
  have htrace : WordTrace (prefixWord ++ tailWord_440724) baseStart_440724 baseEnd_440724 := by
    simpa [prefixWord, tailWord_440724, baseEnd_440724] using wordTrace_append hprefix tailTrace_440724
  have hstable : (prefixWord ++ tailWord_440724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440724).length < 2 ^ (prefixWord ++ tailWord_440724).sum := by decide
  have hdescent : baseEnd_440724 < baseStart_440724 := by decide
  rcases family_descends (prefixWord ++ tailWord_440724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440765 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_440765 : Nat := 118140960795 + 440765 * 2 ^ 59
def prefixEnd_440765 : Nat := 4983230072969 + 3 ^ 40 * 440765 * 2
def baseEnd_440765 : Nat := 150882867119382159073643

theorem tailTrace_440765 : CollatzResearch.WordTrace tailWord_440765 prefixEnd_440765 150882867119382159073643 := by
  unfold tailWord_440765
  simp only [CollatzResearch.WordTrace]
  refine ⟨16076020248191156514027749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10717346832127437676018499 16076020248191156514027749)
  ·
    refine ⟨3014253796535841846380203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16076020248191156514027749 3014253796535841846380203)
    ·
      refine ⟨4521380694803762769570305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014253796535841846380203 4521380694803762769570305)
      ·
        refine ⟨3391035521102822077177729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4521380694803762769570305 3391035521102822077177729)
        ·
          refine ⟨2543276640827116557883297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391035521102822077177729 2543276640827116557883297)
          ·
            refine ⟨1907457480620337418412473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543276640827116557883297 1907457480620337418412473)
            ·
              refine ⟨1430593110465253063809355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907457480620337418412473 1430593110465253063809355)
              ·
                refine ⟨2145889665697879595714033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430593110465253063809355 2145889665697879595714033)
                ·
                  refine ⟨1609417249273409696785525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2145889665697879595714033 1609417249273409696785525)
                  ·
                    refine ⟨150882867119382159073643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1609417249273409696785525 150882867119382159073643)
                    ·
                      rfl

theorem cell22_440765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_440765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440765 prefixEnd_440765 := by exact prefixLift 440765
  have htrace : WordTrace (prefixWord ++ tailWord_440765) baseStart_440765 baseEnd_440765 := by
    simpa [prefixWord, tailWord_440765, baseEnd_440765] using wordTrace_append hprefix tailTrace_440765
  have hstable : (prefixWord ++ tailWord_440765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440765).length < 2 ^ (prefixWord ++ tailWord_440765).sum := by decide
  have hdescent : baseEnd_440765 < baseStart_440765 := by decide
  rcases family_descends (prefixWord ++ tailWord_440765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440797 : List Nat := [1, 4, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_440797 : Nat := 118140960795 + 440797 * 2 ^ 59
def prefixEnd_440797 : Nat := 4983230072969 + 3 ^ 40 * 440797 * 2
def baseEnd_440797 : Nat := 150893821373344742273545

theorem tailTrace_440797 : CollatzResearch.WordTrace tailWord_440797 prefixEnd_440797 150893821373344742273545 := by
  unfold tailWord_440797
  simp only [CollatzResearch.WordTrace]
  refine ⟨16077187384075225979192645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10718124922716817319461763 16077187384075225979192645)
  ·
    refine ⟨3014472634514104871098621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16077187384075225979192645 3014472634514104871098621)
    ·
      refine ⟨1130427237942789326661983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3014472634514104871098621 1130427237942789326661983)
      ·
        refine ⟨1695640856914183989992975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130427237942789326661983 1695640856914183989992975)
        ·
          refine ⟨2543461285371275984989463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695640856914183989992975 2543461285371275984989463)
          ·
            refine ⟨3815191928056913977484195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543461285371275984989463 3815191928056913977484195)
            ·
              refine ⟨5722787892085370966226293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815191928056913977484195 5722787892085370966226293)
              ·
                refine ⟨536511364883003528083715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5722787892085370966226293 536511364883003528083715)
                ·
                  refine ⟨804767047324505292125573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536511364883003528083715 804767047324505292125573)
                  ·
                    refine ⟨150893821373344742273545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804767047324505292125573 150893821373344742273545)
                    ·
                      rfl

theorem cell22_440797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_440797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440797 prefixEnd_440797 := by exact prefixLift 440797
  have htrace : WordTrace (prefixWord ++ tailWord_440797) baseStart_440797 baseEnd_440797 := by
    simpa [prefixWord, tailWord_440797, baseEnd_440797] using wordTrace_append hprefix tailTrace_440797
  have hstable : (prefixWord ++ tailWord_440797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440797).length < 2 ^ (prefixWord ++ tailWord_440797).sum := by decide
  have hdescent : baseEnd_440797 < baseStart_440797 := by decide
  rcases family_descends (prefixWord ++ tailWord_440797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440842 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_440842 : Nat := 118140960795 + 440842 * 2 ^ 59
def prefixEnd_440842 : Nat := 4983230072969 + 3 ^ 40 * 440842 * 2
def baseEnd_440842 : Nat := 150909225792979624898407

theorem tailTrace_440842 : CollatzResearch.WordTrace tailWord_440842 prefixEnd_440842 150909225792979624898407 := by
  unfold tailWord_440842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019707167228049666145195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10719219112608132443053853 4019707167228049666145195)
  ·
    refine ⟨6029560750842074499217793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019707167228049666145195 6029560750842074499217793)
    ·
      refine ⟨4522170563131555874413345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6029560750842074499217793 4522170563131555874413345)
      ·
        refine ⟨3391627922348666905810009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4522170563131555874413345 3391627922348666905810009)
        ·
          refine ⟨2543720941761500179357507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391627922348666905810009 2543720941761500179357507)
          ·
            refine ⟨3815581412642250269036261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543720941761500179357507 3815581412642250269036261)
            ·
              refine ⟨715421514870421925444299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3815581412642250269036261 715421514870421925444299)
              ·
                refine ⟨1073132272305632888166449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715421514870421925444299 1073132272305632888166449)
                ·
                  refine ⟨804849204229224666124837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1073132272305632888166449 804849204229224666124837)
                  ·
                    refine ⟨150909225792979624898407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 804849204229224666124837 150909225792979624898407)
                    ·
                      rfl

theorem cell22_440842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_440842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440842 prefixEnd_440842 := by exact prefixLift 440842
  have htrace : WordTrace (prefixWord ++ tailWord_440842) baseStart_440842 baseEnd_440842 := by
    simpa [prefixWord, tailWord_440842, baseEnd_440842] using wordTrace_append hprefix tailTrace_440842
  have hstable : (prefixWord ++ tailWord_440842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440842).length < 2 ^ (prefixWord ++ tailWord_440842).sum := by decide
  have hdescent : baseEnd_440842 < baseStart_440842 := by decide
  rcases family_descends (prefixWord ++ tailWord_440842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440906 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 1, 3]
def baseStart_440906 : Nat := 118140960795 + 440906 * 2 ^ 59
def prefixEnd_440906 : Nat := 4983230072969 + 3 ^ 40 * 440906 * 2
def baseEnd_440906 : Nat := 150931134300904791298211

theorem tailTrace_440906 : CollatzResearch.WordTrace tailWord_440906 prefixEnd_440906 150931134300904791298211 := by
  unfold tailWord_440906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020290735170084398727643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10720775293786891729940381 4020290735170084398727643)
  ·
    refine ⟨6030436102755126598091465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020290735170084398727643 6030436102755126598091465)
    ·
      refine ⟨4522827077066344948568599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6030436102755126598091465 4522827077066344948568599)
      ·
        refine ⟨6784240615599517422852899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522827077066344948568599 6784240615599517422852899)
        ·
          refine ⟨10176360923399276134279349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784240615599517422852899 10176360923399276134279349)
          ·
            refine ⟨954033836568682137588689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10176360923399276134279349 954033836568682137588689)
            ·
              refine ⟨715525377426511603191517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954033836568682137588689 715525377426511603191517)
              ·
                refine ⟨268322016534941851196819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715525377426511603191517 268322016534941851196819)
                ·
                  refine ⟨402483024802412776795229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268322016534941851196819 402483024802412776795229)
                  ·
                    refine ⟨150931134300904791298211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402483024802412776795229 150931134300904791298211)
                    ·
                      rfl

theorem cell22_440906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_440906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440906 prefixEnd_440906 := by exact prefixLift 440906
  have htrace : WordTrace (prefixWord ++ tailWord_440906) baseStart_440906 baseEnd_440906 := by
    simpa [prefixWord, tailWord_440906, baseEnd_440906] using wordTrace_append hprefix tailTrace_440906
  have hstable : (prefixWord ++ tailWord_440906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440906).length < 2 ^ (prefixWord ++ tailWord_440906).sum := by decide
  have hdescent : baseEnd_440906 < baseStart_440906 := by decide
  rcases family_descends (prefixWord ++ tailWord_440906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440936 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 5]
def baseStart_440936 : Nat := 118140960795 + 440936 * 2 ^ 59
def prefixEnd_440936 : Nat := 4983230072969 + 3 ^ 40 * 440936 * 2
def baseEnd_440936 : Nat := 50313801304664904349373

theorem tailTrace_440936 : CollatzResearch.WordTrace tailWord_440936 prefixEnd_440936 50313801304664904349373 := by
  unfold tailWord_440936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041128565285826359251331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10721504753714435145668441 8041128565285826359251331)
  ·
    refine ⟨12061692847928739538876997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8041128565285826359251331 12061692847928739538876997)
    ·
      refine ⟨2261567408986638663539437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12061692847928739538876997 2261567408986638663539437)
      ·
        refine ⟨848087778369989498827289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2261567408986638663539437 848087778369989498827289)
        ·
          refine ⟨636065833777492124120467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848087778369989498827289 636065833777492124120467)
          ·
            refine ⟨954098750666238186180701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636065833777492124120467 954098750666238186180701)
            ·
              refine ⟨357787031499839319817763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954098750666238186180701 357787031499839319817763)
              ·
                refine ⟨536680547249758979726645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357787031499839319817763 536680547249758979726645)
                ·
                  refine ⟨50313801304664904349373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 536680547249758979726645 50313801304664904349373)
                  ·
                    rfl

theorem cell22_440936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 5].length) (baseStart_440936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_440936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_440936 prefixEnd_440936 := by exact prefixLift 440936
  have htrace : WordTrace (prefixWord ++ tailWord_440936) baseStart_440936 baseEnd_440936 := by
    simpa [prefixWord, tailWord_440936, baseEnd_440936] using wordTrace_append hprefix tailTrace_440936
  have hstable : (prefixWord ++ tailWord_440936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440936).length < 2 ^ (prefixWord ++ tailWord_440936).sum := by decide
  have hdescent : baseEnd_440936 < baseStart_440936 := by decide
  rcases family_descends (prefixWord ++ tailWord_440936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441041 : List Nat := [1, 2, 2, 1, 2, 3, 3, 4, 1, 3]
def baseStart_441041 : Nat := 118140960795 + 441041 * 2 ^ 59
def prefixEnd_441041 : Nat := 4983230072969 + 3 ^ 40 * 441041 * 2
def baseEnd_441041 : Nat := 150977347559809439172797

theorem tailTrace_441041 : CollatzResearch.WordTrace tailWord_441041 prefixEnd_441041 150977347559809439172797 := by
  unfold tailWord_441041
  simp only [CollatzResearch.WordTrace]
  refine ⟨16086086795191255651074977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10724057863460837100716651 16086086795191255651074977)
  ·
    refine ⟨12064565096393441738306233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16086086795191255651074977 12064565096393441738306233)
    ·
      refine ⟨9048423822295081303729675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12064565096393441738306233 9048423822295081303729675)
      ·
        refine ⟨13572635733442621955594513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9048423822295081303729675 13572635733442621955594513)
        ·
          refine ⟨10179476800081966466695885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13572635733442621955594513 10179476800081966466695885)
          ·
            refine ⟨3817303800030737425010957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10179476800081966466695885 3817303800030737425010957)
            ·
              refine ⟨1431488925011526534379109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3817303800030737425010957 1431488925011526534379109)
              ·
                refine ⟨268404173439661225196083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1431488925011526534379109 268404173439661225196083)
                ·
                  refine ⟨402606260159491837794125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268404173439661225196083 402606260159491837794125)
                  ·
                    refine ⟨150977347559809439172797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402606260159491837794125 150977347559809439172797)
                    ·
                      rfl

theorem cell22_441041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_441041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441041 prefixEnd_441041 := by exact prefixLift 441041
  have htrace : WordTrace (prefixWord ++ tailWord_441041) baseStart_441041 baseEnd_441041 := by
    simpa [prefixWord, tailWord_441041, baseEnd_441041] using wordTrace_append hprefix tailTrace_441041
  have hstable : (prefixWord ++ tailWord_441041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441041).length < 2 ^ (prefixWord ++ tailWord_441041).sum := by decide
  have hdescent : baseEnd_441041 < baseStart_441041 := by decide
  rcases family_descends (prefixWord ++ tailWord_441041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441097 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_441097 : Nat := 118140960795 + 441097 * 2 ^ 59
def prefixEnd_441097 : Nat := 4983230072969 + 3 ^ 40 * 441097 * 2
def baseEnd_441097 : Nat := 150996517504243959772625

theorem tailTrace_441097 : CollatzResearch.WordTrace tailWord_441097 prefixEnd_441097 150996517504243959772625 := by
  unfold tailWord_441097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16088129282988377215113545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10725419521992251476742363 16088129282988377215113545)
  ·
    refine ⟨12066096962241282911335159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16088129282988377215113545 12066096962241282911335159)
    ·
      refine ⟨18099145443361924367002739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12066096962241282911335159 18099145443361924367002739)
      ·
        refine ⟨27148718165042886550504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18099145443361924367002739 27148718165042886550504109)
        ·
          refine ⟨10180769311891082456439041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27148718165042886550504109 10180769311891082456439041)
          ·
            refine ⟨7635576983918311842329281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10180769311891082456439041 7635576983918311842329281)
            ·
              refine ⟨5726682737938733881746961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7635576983918311842329281 5726682737938733881746961)
              ·
                refine ⟨4295012053454050411310221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5726682737938733881746961 4295012053454050411310221)
                ·
                  refine ⟨1610629520045268904241333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4295012053454050411310221 1610629520045268904241333)
                  ·
                    refine ⟨150996517504243959772625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1610629520045268904241333 150996517504243959772625)
                    ·
                      rfl

theorem cell22_441097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_441097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441097 prefixEnd_441097 := by exact prefixLift 441097
  have htrace : WordTrace (prefixWord ++ tailWord_441097) baseStart_441097 baseEnd_441097 := by
    simpa [prefixWord, tailWord_441097, baseEnd_441097] using wordTrace_append hprefix tailTrace_441097
  have hstable : (prefixWord ++ tailWord_441097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441097).length < 2 ^ (prefixWord ++ tailWord_441097).sum := by decide
  have hdescent : baseEnd_441097 < baseStart_441097 := by decide
  rcases family_descends (prefixWord ++ tailWord_441097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441146 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_441146 : Nat := 118140960795 + 441146 * 2 ^ 59
def prefixEnd_441146 : Nat := 4983230072969 + 3 ^ 40 * 441146 * 2
def baseEnd_441146 : Nat := 151013291205624165297475

theorem tailTrace_441146 : CollatzResearch.WordTrace tailWord_441146 prefixEnd_441146 151013291205624165297475 := by
  unfold tailWord_441146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022479114952714645911823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10726610973207239055764861 4022479114952714645911823)
  ·
    refine ⟨6033718672429071968867735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4022479114952714645911823 6033718672429071968867735)
    ·
      refine ⟨9050578008643607953301603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033718672429071968867735 9050578008643607953301603)
      ·
        refine ⟨13575867012965411929952405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9050578008643607953301603 13575867012965411929952405)
        ·
          refine ⟨636368766232753684216519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13575867012965411929952405 636368766232753684216519)
          ·
            refine ⟨954553149349130526324779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636368766232753684216519 954553149349130526324779)
            ·
              refine ⟨1431829724023695789487169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954553149349130526324779 1431829724023695789487169)
              ·
                refine ⟨1073872293017771842115377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431829724023695789487169 1073872293017771842115377)
                ·
                  refine ⟨805404219763328881586533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1073872293017771842115377 805404219763328881586533)
                  ·
                    refine ⟨151013291205624165297475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 805404219763328881586533 151013291205624165297475)
                    ·
                      rfl

theorem cell22_441146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_441146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441146 prefixEnd_441146 := by exact prefixLift 441146
  have htrace : WordTrace (prefixWord ++ tailWord_441146) baseStart_441146 baseEnd_441146 := by
    simpa [prefixWord, tailWord_441146, baseEnd_441146] using wordTrace_append hprefix tailTrace_441146
  have hstable : (prefixWord ++ tailWord_441146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441146).length < 2 ^ (prefixWord ++ tailWord_441146).sum := by decide
  have hdescent : baseEnd_441146 < baseStart_441146 := by decide
  rcases family_descends (prefixWord ++ tailWord_441146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441150 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_441150 : Nat := 118140960795 + 441150 * 2 ^ 59
def prefixEnd_441150 : Nat := 4983230072969 + 3 ^ 40 * 441150 * 2
def baseEnd_441150 : Nat := 50338220162456496065821

theorem tailTrace_441150 : CollatzResearch.WordTrace tailWord_441150 prefixEnd_441150 50338220162456496065821 := by
  unfold tailWord_441150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011257793974545908349113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10726708234530911511195269 2011257793974545908349113)
  ·
    refine ⟨1508443345480909431261835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011257793974545908349113 1508443345480909431261835)
    ·
      refine ⟨2262665018221364146892753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508443345480909431261835 2262665018221364146892753)
      ·
        refine ⟨1696998763666023110169565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2262665018221364146892753 1696998763666023110169565)
        ·
          refine ⟨636374536374758666313587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696998763666023110169565 636374536374758666313587)
          ·
            refine ⟨954561804562137999470381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636374536374758666313587 954561804562137999470381)
            ·
              refine ⟨357960676710801749801393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 954561804562137999470381 357960676710801749801393)
              ·
                refine ⟨268470507533101312351045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357960676710801749801393 268470507533101312351045)
                ·
                  refine ⟨50338220162456496065821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268470507533101312351045 50338220162456496065821)
                  ·
                    rfl

theorem cell22_441150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_441150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441150 prefixEnd_441150 := by exact prefixLift 441150
  have htrace : WordTrace (prefixWord ++ tailWord_441150) baseStart_441150 baseEnd_441150 := by
    simpa [prefixWord, tailWord_441150, baseEnd_441150] using wordTrace_append hprefix tailTrace_441150
  have hstable : (prefixWord ++ tailWord_441150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441150).length < 2 ^ (prefixWord ++ tailWord_441150).sum := by decide
  have hdescent : baseEnd_441150 < baseStart_441150 := by decide
  rcases family_descends (prefixWord ++ tailWord_441150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441165 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_441165 : Nat := 118140960795 + 441165 * 2 ^ 59
def prefixEnd_441165 : Nat := 4983230072969 + 3 ^ 40 * 441165 * 2
def baseEnd_441165 : Nat := 151019795293914449072417

theorem tailTrace_441165 : CollatzResearch.WordTrace tailWord_441165 prefixEnd_441165 151019795293914449072417 := by
  unfold tailWord_441165
  simp only [CollatzResearch.WordTrace]
  refine ⟨16090609446742024828588949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10727072964494683219059299 16090609446742024828588949)
  ·
    refine ⟨754247317816032413840107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16090609446742024828588949 754247317816032413840107)
    ·
      refine ⟨1131370976724048620760161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754247317816032413840107 1131370976724048620760161)
      ·
        refine ⟨848528232543036465570121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131370976724048620760161 848528232543036465570121)
        ·
          refine ⟨636396174407277349177591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848528232543036465570121 636396174407277349177591)
          ·
            refine ⟨954594261610916023766387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636396174407277349177591 954594261610916023766387)
            ·
              refine ⟨1431891392416374035649581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954594261610916023766387 1431891392416374035649581)
              ·
                refine ⟨536959272156140263368593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431891392416374035649581 536959272156140263368593)
                ·
                  refine ⟨402719454117105197526445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536959272156140263368593 402719454117105197526445)
                  ·
                    refine ⟨151019795293914449072417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402719454117105197526445 151019795293914449072417)
                    ·
                      rfl

theorem cell22_441165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_441165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441165 prefixEnd_441165 := by exact prefixLift 441165
  have htrace : WordTrace (prefixWord ++ tailWord_441165) baseStart_441165 baseEnd_441165 := by
    simpa [prefixWord, tailWord_441165, baseEnd_441165] using wordTrace_append hprefix tailTrace_441165
  have hstable : (prefixWord ++ tailWord_441165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441165).length < 2 ^ (prefixWord ++ tailWord_441165).sum := by decide
  have hdescent : baseEnd_441165 < baseStart_441165 := by decide
  rcases family_descends (prefixWord ++ tailWord_441165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441219 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_441219 : Nat := 118140960795 + 441219 * 2 ^ 59
def prefixEnd_441219 : Nat := 4983230072969 + 3 ^ 40 * 441219 * 2
def baseEnd_441219 : Nat := 151038280597476308222251

theorem tailTrace_441219 : CollatzResearch.WordTrace tailWord_441219 prefixEnd_441219 151038280597476308222251 := by
  unfold tailWord_441219
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092578988546392051054711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10728385992364261367369807 16092578988546392051054711)
  ·
    refine ⟨24138868482819588076582067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16092578988546392051054711 24138868482819588076582067)
    ·
      refine ⟨36208302724229382114873101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24138868482819588076582067 36208302724229382114873101)
      ·
        refine ⟨13578113521586018293077413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36208302724229382114873101 13578113521586018293077413)
        ·
          refine ⟨2545896285297378429952015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13578113521586018293077413 2545896285297378429952015)
          ·
            refine ⟨3818844427946067644928023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545896285297378429952015 3818844427946067644928023)
            ·
              refine ⟨5728266641919101467392035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818844427946067644928023 5728266641919101467392035)
              ·
                refine ⟨8592399962878652201088053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728266641919101467392035 8592399962878652201088053)
                ·
                  refine ⟨805537496519873643852005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8592399962878652201088053 805537496519873643852005)
                  ·
                    refine ⟨151038280597476308222251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 805537496519873643852005 151038280597476308222251)
                    ·
                      rfl

theorem cell22_441219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_441219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441219 prefixEnd_441219 := by exact prefixLift 441219
  have htrace : WordTrace (prefixWord ++ tailWord_441219) baseStart_441219 baseEnd_441219 := by
    simpa [prefixWord, tailWord_441219, baseEnd_441219] using wordTrace_append hprefix tailTrace_441219
  have hstable : (prefixWord ++ tailWord_441219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441219).length < 2 ^ (prefixWord ++ tailWord_441219).sum := by decide
  have hdescent : baseEnd_441219 < baseStart_441219 := by decide
  rcases family_descends (prefixWord ++ tailWord_441219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441236 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_441236 : Nat := 118140960795 + 441236 * 2 ^ 59
def prefixEnd_441236 : Nat := 4983230072969 + 3 ^ 40 * 441236 * 2
def baseEnd_441236 : Nat := 151044100044893930547199

theorem tailTrace_441236 : CollatzResearch.WordTrace tailWord_441236 prefixEnd_441236 151044100044893930547199 := by
  unfold tailWord_441236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046599514742401977211781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10728799352989869302949041 8046599514742401977211781)
  ·
    refine ⟨1508737409014200370727209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8046599514742401977211781 1508737409014200370727209)
    ·
      refine ⟨1131553056760650278045407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508737409014200370727209 1131553056760650278045407)
      ·
        refine ⟨1697329585140975417068111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131553056760650278045407 1697329585140975417068111)
        ·
          refine ⟨2545994377711463125602167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697329585140975417068111 2545994377711463125602167)
          ·
            refine ⟨3818991566567194688403251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545994377711463125602167 3818991566567194688403251)
            ·
              refine ⟨5728487349850792032604877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818991566567194688403251 5728487349850792032604877)
              ·
                refine ⟨2148182756194047012226829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5728487349850792032604877 2148182756194047012226829)
                ·
                  refine ⟨805568533572767629585061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2148182756194047012226829 805568533572767629585061)
                  ·
                    refine ⟨151044100044893930547199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 805568533572767629585061 151044100044893930547199)
                    ·
                      rfl

theorem cell22_441236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_441236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441236 prefixEnd_441236 := by exact prefixLift 441236
  have htrace : WordTrace (prefixWord ++ tailWord_441236) baseStart_441236 baseEnd_441236 := by
    simpa [prefixWord, tailWord_441236, baseEnd_441236] using wordTrace_append hprefix tailTrace_441236
  have hstable : (prefixWord ++ tailWord_441236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441236).length < 2 ^ (prefixWord ++ tailWord_441236).sum := by decide
  have hdescent : baseEnd_441236 < baseStart_441236 := by decide
  rcases family_descends (prefixWord ++ tailWord_441236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441251 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 4]
def baseStart_441251 : Nat := 118140960795 + 441251 * 2 ^ 59
def prefixEnd_441251 : Nat := 4983230072969 + 3 ^ 40 * 441251 * 2
def baseEnd_441251 : Nat := 50349744950479630474051

theorem tailTrace_441251 : CollatzResearch.WordTrace tailWord_441251 prefixEnd_441251 50349744950479630474051 := by
  unfold tailWord_441251
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093746124430461516219607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10729164082953641010813071 16093746124430461516219607)
  ·
    refine ⟨24140619186645692274329411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16093746124430461516219607 24140619186645692274329411)
    ·
      refine ⟨36210928779968538411494117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24140619186645692274329411 36210928779968538411494117)
      ·
        refine ⟨6789549146244100952155147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36210928779968538411494117 6789549146244100952155147)
        ·
          refine ⟨10184323719366151428232721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789549146244100952155147 10184323719366151428232721)
          ·
            refine ⟨7638242789524613571174541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10184323719366151428232721 7638242789524613571174541)
            ·
              refine ⟨2864341046071730089190453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7638242789524613571174541 2864341046071730089190453)
              ·
                refine ⟨268531973069224695861605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2864341046071730089190453 268531973069224695861605)
                ·
                  refine ⟨50349744950479630474051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268531973069224695861605 50349744950479630474051)
                  ·
                    rfl

theorem cell22_441251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 4].length) (baseStart_441251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441251 prefixEnd_441251 := by exact prefixLift 441251
  have htrace : WordTrace (prefixWord ++ tailWord_441251) baseStart_441251 baseEnd_441251 := by
    simpa [prefixWord, tailWord_441251, baseEnd_441251] using wordTrace_append hprefix tailTrace_441251
  have hstable : (prefixWord ++ tailWord_441251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441251).length < 2 ^ (prefixWord ++ tailWord_441251).sum := by decide
  have hdescent : baseEnd_441251 < baseStart_441251 := by decide
  rcases family_descends (prefixWord ++ tailWord_441251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441268 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_441268 : Nat := 118140960795 + 441268 * 2 ^ 59
def prefixEnd_441268 : Nat := 4983230072969 + 3 ^ 40 * 441268 * 2
def baseEnd_441268 : Nat := 50351684766285504582367

theorem tailTrace_441268 : CollatzResearch.WordTrace tailWord_441268 prefixEnd_441268 50351684766285504582367 := by
  unfold tailWord_441268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047183082684436709794229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10729577443579248946392305 8047183082684436709794229)
  ·
    refine ⟨754423414001665941543209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8047183082684436709794229 754423414001665941543209)
    ·
      refine ⟨565817560501249456157407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754423414001665941543209 565817560501249456157407)
      ·
        refine ⟨848726340751874184236111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565817560501249456157407 848726340751874184236111)
        ·
          refine ⟨1273089511127811276354167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848726340751874184236111 1273089511127811276354167)
          ·
            refine ⟨1909634266691716914531251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273089511127811276354167 1909634266691716914531251)
            ·
              refine ⟨2864451400037575371796877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909634266691716914531251 2864451400037575371796877)
              ·
                refine ⟨1074169275014090764423829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2864451400037575371796877 1074169275014090764423829)
                ·
                  refine ⟨50351684766285504582367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1074169275014090764423829 50351684766285504582367)
                  ·
                    rfl

theorem cell22_441268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_441268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441268 prefixEnd_441268 := by exact prefixLift 441268
  have htrace : WordTrace (prefixWord ++ tailWord_441268) baseStart_441268 baseEnd_441268 := by
    simpa [prefixWord, tailWord_441268, baseEnd_441268] using wordTrace_append hprefix tailTrace_441268
  have hstable : (prefixWord ++ tailWord_441268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441268).length < 2 ^ (prefixWord ++ tailWord_441268).sum := by decide
  have hdescent : baseEnd_441268 < baseStart_441268 := by decide
  rcases family_descends (prefixWord ++ tailWord_441268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441302 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_441302 : Nat := 118140960795 + 441302 * 2 ^ 59
def prefixEnd_441302 : Nat := 4983230072969 + 3 ^ 40 * 441302 * 2
def baseEnd_441302 : Nat := 50355564397897252798999

theorem tailTrace_441302 : CollatzResearch.WordTrace tailWord_441302 prefixEnd_441302 50355564397897252798999 := by
  unfold tailWord_441302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005975390452856076645385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10730404164830464817550773 1005975390452856076645385)
  ·
    refine ⟨754481542839642057484039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1005975390452856076645385 754481542839642057484039)
    ·
      refine ⟨1131722314259463086226059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754481542839642057484039 1131722314259463086226059)
      ·
        refine ⟨1697583471389194629339089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131722314259463086226059 1697583471389194629339089)
        ·
          refine ⟨1273187603541895972004317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697583471389194629339089 1273187603541895972004317)
          ·
            refine ⟨477445351328210989501619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1273187603541895972004317 477445351328210989501619)
            ·
              refine ⟨716168026992316484252429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477445351328210989501619 716168026992316484252429)
              ·
                refine ⟨268563010122118681594661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716168026992316484252429 268563010122118681594661)
                ·
                  refine ⟨50355564397897252798999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268563010122118681594661 50355564397897252798999)
                  ·
                    rfl

theorem cell22_441302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_441302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441302 prefixEnd_441302 := by exact prefixLift 441302
  have htrace : WordTrace (prefixWord ++ tailWord_441302) baseStart_441302 baseEnd_441302 := by
    simpa [prefixWord, tailWord_441302, baseEnd_441302] using wordTrace_append hprefix tailTrace_441302
  have hstable : (prefixWord ++ tailWord_441302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441302).length < 2 ^ (prefixWord ++ tailWord_441302).sum := by decide
  have hdescent : baseEnd_441302 < baseStart_441302 := by decide
  rcases family_descends (prefixWord ++ tailWord_441302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441339 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_441339 : Nat := 118140960795 + 441339 * 2 ^ 59
def prefixEnd_441339 : Nat := 4983230072969 + 3 ^ 40 * 441339 * 2
def baseEnd_441339 : Nat := 151079359049835995221883

theorem tailTrace_441339 : CollatzResearch.WordTrace tailWord_441339 prefixEnd_441339 151079359049835995221883 := by
  unfold tailWord_441339
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096955748111652545423071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10731303832074435030282047 16096955748111652545423071)
  ·
    refine ⟨24145433622167478818134607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16096955748111652545423071 24145433622167478818134607)
    ·
      refine ⟨36218150433251218227201911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24145433622167478818134607 36218150433251218227201911)
      ·
        refine ⟨54327225649876827340802867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36218150433251218227201911 54327225649876827340802867)
        ·
          refine ⟨81490838474815241011204301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54327225649876827340802867 81490838474815241011204301)
          ·
            refine ⟨30559064428055715379201613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81490838474815241011204301 30559064428055715379201613)
            ·
              refine ⟨11459649160520893267200605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30559064428055715379201613 11459649160520893267200605)
              ·
                refine ⟨4297368435195334975200227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11459649160520893267200605 4297368435195334975200227)
                ·
                  refine ⟨6446052652793002462800341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297368435195334975200227 6446052652793002462800341)
                  ·
                    refine ⟨151079359049835995221883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6446052652793002462800341 151079359049835995221883)
                    ·
                      rfl

theorem cell22_441339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_441339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441339 prefixEnd_441339 := by exact prefixLift 441339
  have htrace : WordTrace (prefixWord ++ tailWord_441339) baseStart_441339 baseEnd_441339 := by
    simpa [prefixWord, tailWord_441339, baseEnd_441339] using wordTrace_append hprefix tailTrace_441339
  have hstable : (prefixWord ++ tailWord_441339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441339).length < 2 ^ (prefixWord ++ tailWord_441339).sum := by decide
  have hdescent : baseEnd_441339 < baseStart_441339 := by decide
  rcases family_descends (prefixWord ++ tailWord_441339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441416 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_441416 : Nat := 118140960795 + 441416 * 2 ^ 59
def prefixEnd_441416 : Nat := 4983230072969 + 3 ^ 40 * 441416 * 2
def baseEnd_441416 : Nat := 151105717723433461046647

theorem tailTrace_441416 : CollatzResearch.WordTrace tailWord_441416 prefixEnd_441416 151105717723433461046647 := by
  unfold tailWord_441416
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049882084416347347988051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10733176112555129797317401 8049882084416347347988051)
  ·
    refine ⟨12074823126624521021982077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8049882084416347347988051 12074823126624521021982077)
    ·
      refine ⟨4528058672484195383243279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12074823126624521021982077 4528058672484195383243279)
      ·
        refine ⟨6792088008726293074864919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528058672484195383243279 6792088008726293074864919)
        ·
          refine ⟨10188132013089439612297379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792088008726293074864919 10188132013089439612297379)
          ·
            refine ⟨15282198019634159418446069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10188132013089439612297379 15282198019634159418446069)
            ·
              refine ⟨1432706064340702445479319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15282198019634159418446069 1432706064340702445479319)
              ·
                refine ⟨2149059096511053668218979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432706064340702445479319 2149059096511053668218979)
                ·
                  refine ⟨3223588644766580502328469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149059096511053668218979 3223588644766580502328469)
                  ·
                    refine ⟨151105717723433461046647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3223588644766580502328469 151105717723433461046647)
                    ·
                      rfl

theorem cell22_441416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_441416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441416 prefixEnd_441416 := by exact prefixLift 441416
  have htrace : WordTrace (prefixWord ++ tailWord_441416) baseStart_441416 baseEnd_441416 := by
    simpa [prefixWord, tailWord_441416, baseEnd_441416] using wordTrace_append hprefix tailTrace_441416
  have hstable : (prefixWord ++ tailWord_441416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441416).length < 2 ^ (prefixWord ++ tailWord_441416).sum := by decide
  have hdescent : baseEnd_441416 < baseStart_441416 := by decide
  rcases family_descends (prefixWord ++ tailWord_441416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441463 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 3, 3]
def baseStart_441463 : Nat := 118140960795 + 441463 * 2 ^ 59
def prefixEnd_441463 : Nat := 4983230072969 + 3 ^ 40 * 441463 * 2
def baseEnd_441463 : Nat := 151121806783941005121503

theorem tailTrace_441463 : CollatzResearch.WordTrace tailWord_441463 prefixEnd_441463 151121806783941005121503 := by
  unfold tailWord_441463
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101478399662421722937043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10734318933108281148624695 16101478399662421722937043)
  ·
    refine ⟨24152217599493632584405565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16101478399662421722937043 24152217599493632584405565)
    ·
      refine ⟨9057081599810112219152087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24152217599493632584405565 9057081599810112219152087)
      ·
        refine ⟨13585622399715168328728131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9057081599810112219152087 13585622399715168328728131)
        ·
          refine ⟨20378433599572752493092197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13585622399715168328728131 20378433599572752493092197)
          ·
            refine ⟨3820956299919891092454787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20378433599572752493092197 3820956299919891092454787)
            ·
              refine ⟨5731434449879836638682181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820956299919891092454787 5731434449879836638682181)
              ·
                refine ⟨1074643959352469369752909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5731434449879836638682181 1074643959352469369752909)
                ·
                  refine ⟨402991484757176013657341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074643959352469369752909 402991484757176013657341)
                  ·
                    refine ⟨151121806783941005121503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 402991484757176013657341 151121806783941005121503)
                    ·
                      rfl

theorem cell22_441463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_441463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441463 prefixEnd_441463 := by exact prefixLift 441463
  have htrace : WordTrace (prefixWord ++ tailWord_441463) baseStart_441463 baseEnd_441463 := by
    simpa [prefixWord, tailWord_441463, baseEnd_441463] using wordTrace_append hprefix tailTrace_441463
  have hstable : (prefixWord ++ tailWord_441463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441463).length < 2 ^ (prefixWord ++ tailWord_441463).sum := by decide
  have hdescent : baseEnd_441463 < baseStart_441463 := by decide
  rcases family_descends (prefixWord ++ tailWord_441463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441465 : List Nat := [1, 2, 1, 3, 5, 2, 2, 6]
def baseStart_441465 : Nat := 118140960795 + 441465 * 2 ^ 59
def prefixEnd_441465 : Nat := 4983230072969 + 3 ^ 40 * 441465 * 2
def baseEnd_441465 : Nat := 16791387936090407396833

theorem tailTrace_441465 : CollatzResearch.WordTrace tailWord_441465 prefixEnd_441465 16791387936090407396833 := by
  unfold tailWord_441465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16101551345655176064509849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10734367563770117376339899 16101551345655176064509849)
  ·
    refine ⟨12076163509241382048382387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16101551345655176064509849 12076163509241382048382387)
    ·
      refine ⟨18114245263862073072573581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12076163509241382048382387 18114245263862073072573581)
      ·
        refine ⟨6792841973948277402215093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18114245263862073072573581 6792841973948277402215093)
        ·
          refine ⟨636828935057651006457665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6792841973948277402215093 636828935057651006457665)
          ·
            refine ⟨477621701293238254843249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636828935057651006457665 477621701293238254843249)
            ·
              refine ⟨358216275969928691132437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477621701293238254843249 358216275969928691132437)
              ·
                refine ⟨16791387936090407396833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358216275969928691132437 16791387936090407396833)
                ·
                  rfl

theorem cell22_441465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 6].length) (baseStart_441465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441465 prefixEnd_441465 := by exact prefixLift 441465
  have htrace : WordTrace (prefixWord ++ tailWord_441465) baseStart_441465 baseEnd_441465 := by
    simpa [prefixWord, tailWord_441465, baseEnd_441465] using wordTrace_append hprefix tailTrace_441465
  have hstable : (prefixWord ++ tailWord_441465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441465).length < 2 ^ (prefixWord ++ tailWord_441465).sum := by decide
  have hdescent : baseEnd_441465 < baseStart_441465 := by decide
  rcases family_descends (prefixWord ++ tailWord_441465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441491 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_441491 : Nat := 118140960795 + 441491 * 2 ^ 59
def prefixEnd_441491 : Nat := 4983230072969 + 3 ^ 40 * 441491 * 2
def baseEnd_441491 : Nat := 151131391756158265421417

theorem tailTrace_441491 : CollatzResearch.WordTrace tailWord_441491 prefixEnd_441491 151131391756158265421417 := by
  unfold tailWord_441491
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102499643560982504956327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10734999762373988336637551 16102499643560982504956327)
  ·
    refine ⟨24153749465341473757434491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16102499643560982504956327 24153749465341473757434491)
    ·
      refine ⟨36230624198012210636151737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24153749465341473757434491 36230624198012210636151737)
      ·
        refine ⟨27172968148509157977113803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36230624198012210636151737 27172968148509157977113803)
        ·
          refine ⟨40759452222763736965670705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27172968148509157977113803 40759452222763736965670705)
          ·
            refine ⟨30569589167072802724253029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40759452222763736965670705 30569589167072802724253029)
            ·
              refine ⟨5731797968826150510797443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30569589167072802724253029 5731797968826150510797443)
              ·
                refine ⟨8597696953239225766196165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731797968826150510797443 8597696953239225766196165)
                ·
                  refine ⟨1612068178732354831161781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8597696953239225766196165 1612068178732354831161781)
                  ·
                    refine ⟨151131391756158265421417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1612068178732354831161781 151131391756158265421417)
                    ·
                      rfl

theorem cell22_441491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_441491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441491 prefixEnd_441491 := by exact prefixLift 441491
  have htrace : WordTrace (prefixWord ++ tailWord_441491) baseStart_441491 baseEnd_441491 := by
    simpa [prefixWord, tailWord_441491, baseEnd_441491] using wordTrace_append hprefix tailTrace_441491
  have hstable : (prefixWord ++ tailWord_441491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441491).length < 2 ^ (prefixWord ++ tailWord_441491).sum := by decide
  have hdescent : baseEnd_441491 < baseStart_441491 := by decide
  rcases family_descends (prefixWord ++ tailWord_441491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441604 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 2, 3]
def baseStart_441604 : Nat := 118140960795 + 441604 * 2 ^ 59
def prefixEnd_441604 : Nat := 4983230072969 + 3 ^ 40 * 441604 * 2
def baseEnd_441604 : Nat := 151170073965463637346071

theorem tailTrace_441604 : CollatzResearch.WordTrace tailWord_441604 prefixEnd_441604 151170073965463637346071 := by
  unfold tailWord_441604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053310546075801401909933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10737747394767735202546577 8053310546075801401909933)
  ·
    refine ⟨3019991454778425525716225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8053310546075801401909933 3019991454778425525716225)
    ·
      refine ⟨2264993591083819144287169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3019991454778425525716225 2264993591083819144287169)
      ·
        refine ⟨1698745193312864358215377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2264993591083819144287169 1698745193312864358215377)
        ·
          refine ⟨1274058894984648268661533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1698745193312864358215377 1274058894984648268661533)
          ·
            refine ⟨477772085619243100748075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274058894984648268661533 477772085619243100748075)
            ·
              refine ⟨716658128428864651122113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477772085619243100748075 716658128428864651122113)
              ·
                refine ⟨537493596321648488341585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716658128428864651122113 537493596321648488341585)
                ·
                  refine ⟨403120197241236366256189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537493596321648488341585 403120197241236366256189)
                  ·
                    refine ⟨151170073965463637346071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403120197241236366256189 151170073965463637346071)
                    ·
                      rfl

theorem cell22_441604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_441604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441604 prefixEnd_441604 := by exact prefixLift 441604
  have htrace : WordTrace (prefixWord ++ tailWord_441604) baseStart_441604 baseEnd_441604 := by
    simpa [prefixWord, tailWord_441604, baseEnd_441604] using wordTrace_append hprefix tailTrace_441604
  have hstable : (prefixWord ++ tailWord_441604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441604).length < 2 ^ (prefixWord ++ tailWord_441604).sum := by decide
  have hdescent : baseEnd_441604 < baseStart_441604 := by decide
  rcases family_descends (prefixWord ++ tailWord_441604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441634 : List Nat := [3, 3, 1, 1, 5, 1, 2, 6]
def baseStart_441634 : Nat := 118140960795 + 441634 * 2 ^ 59
def prefixEnd_441634 : Nat := 4983230072969 + 3 ^ 40 * 441634 * 2
def baseEnd_441634 : Nat := 16797815953172617677331

theorem tailTrace_441634 : CollatzResearch.WordTrace tailWord_441634 prefixEnd_441634 16797815953172617677331 := by
  unfold tailWord_441634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026928820510729481852989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10738476854695278618274637 4026928820510729481852989)
  ·
    refine ⟨1510098307691523555694871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4026928820510729481852989 1510098307691523555694871)
    ·
      refine ⟨2265147461537285333542307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510098307691523555694871 2265147461537285333542307)
      ·
        refine ⟨3397721192305928000313461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265147461537285333542307 3397721192305928000313461)
        ·
          refine ⟨318536361778680750029387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3397721192305928000313461 318536361778680750029387)
          ·
            refine ⟨477804542668021125044081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318536361778680750029387 477804542668021125044081)
            ·
              refine ⟨358353407001015843783061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477804542668021125044081 358353407001015843783061)
              ·
                refine ⟨16797815953172617677331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 358353407001015843783061 16797815953172617677331)
                ·
                  rfl

theorem cell22_441634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_441634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441634 prefixEnd_441634 := by exact prefixLift 441634
  have htrace : WordTrace (prefixWord ++ tailWord_441634) baseStart_441634 baseEnd_441634 := by
    simpa [prefixWord, tailWord_441634, baseEnd_441634] using wordTrace_append hprefix tailTrace_441634
  have hstable : (prefixWord ++ tailWord_441634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441634).length < 2 ^ (prefixWord ++ tailWord_441634).sum := by decide
  have hdescent : baseEnd_441634 < baseStart_441634 := by decide
  rcases family_descends (prefixWord ++ tailWord_441634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441649 : List Nat := [1, 2, 2, 3, 3, 1, 3, 3, 1, 3]
def baseStart_441649 : Nat := 118140960795 + 441649 * 2 ^ 59
def prefixEnd_441649 : Nat := 4983230072969 + 3 ^ 40 * 441649 * 2
def baseEnd_441649 : Nat := 151185478385098519970933

theorem tailTrace_441649 : CollatzResearch.WordTrace tailWord_441649 prefixEnd_441649 151185478385098519970933 := by
  unfold tailWord_441649
  simp only [CollatzResearch.WordTrace]
  refine ⟨16108262376988575489208001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10738841584659050326138667 16108262376988575489208001)
  ·
    refine ⟨12081196782741431616906001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16108262376988575489208001 12081196782741431616906001)
    ·
      refine ⟨9060897587056073712679501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12081196782741431616906001 9060897587056073712679501)
      ·
        refine ⟨3397836595146027642254813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9060897587056073712679501 3397836595146027642254813)
        ·
          refine ⟨1274188723179760365845555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3397836595146027642254813 1274188723179760365845555)
          ·
            refine ⟨1911283084769640548768333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1274188723179760365845555 1911283084769640548768333)
            ·
              refine ⟨716731156788615205788125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911283084769640548768333 716731156788615205788125)
              ·
                refine ⟨268774183795730702170547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 716731156788615205788125 268774183795730702170547)
                ·
                  refine ⟨403161275693596053255821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268774183795730702170547 403161275693596053255821)
                  ·
                    refine ⟨151185478385098519970933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403161275693596053255821 151185478385098519970933)
                    ·
                      rfl

theorem cell22_441649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_441649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441649 prefixEnd_441649 := by exact prefixLift 441649
  have htrace : WordTrace (prefixWord ++ tailWord_441649) baseStart_441649 baseEnd_441649 := by
    simpa [prefixWord, tailWord_441649, baseEnd_441649] using wordTrace_append hprefix tailTrace_441649
  have hstable : (prefixWord ++ tailWord_441649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441649).length < 2 ^ (prefixWord ++ tailWord_441649).sum := by decide
  have hdescent : baseEnd_441649 < baseStart_441649 := by decide
  rcases family_descends (prefixWord ++ tailWord_441649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441705 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_441705 : Nat := 118140960795 + 441705 * 2 ^ 59
def prefixEnd_441705 : Nat := 4983230072969 + 3 ^ 40 * 441705 * 2
def baseEnd_441705 : Nat := 151204648329533040570761

theorem tailTrace_441705 : CollatzResearch.WordTrace tailWord_441705 prefixEnd_441705 151204648329533040570761 := by
  unfold tailWord_441705
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110304864785697053246569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740203243190464702164379 16110304864785697053246569)
  ·
    refine ⟨12082728648589272789934927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16110304864785697053246569 12082728648589272789934927)
    ·
      refine ⟨18124092972883909184902391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12082728648589272789934927 18124092972883909184902391)
      ·
        refine ⟨27186139459325863777353587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18124092972883909184902391 27186139459325863777353587)
        ·
          refine ⟨40779209188988795666030381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27186139459325863777353587 40779209188988795666030381)
          ·
            refine ⟨15292203445870798374761393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40779209188988795666030381 15292203445870798374761393)
            ·
              refine ⟨11469152584403098781071045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15292203445870798374761393 11469152584403098781071045)
              ·
                refine ⟨2150466109575581021450821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11469152584403098781071045 2150466109575581021450821)
                ·
                  refine ⟨403212395545421441522029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150466109575581021450821 403212395545421441522029)
                  ·
                    refine ⟨151204648329533040570761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403212395545421441522029 151204648329533040570761)
                    ·
                      rfl

theorem cell22_441705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_441705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441705 prefixEnd_441705 := by exact prefixLift 441705
  have htrace : WordTrace (prefixWord ++ tailWord_441705) baseStart_441705 baseEnd_441705 := by
    simpa [prefixWord, tailWord_441705, baseEnd_441705] using wordTrace_append hprefix tailTrace_441705
  have hstable : (prefixWord ++ tailWord_441705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441705).length < 2 ^ (prefixWord ++ tailWord_441705).sum := by decide
  have hdescent : baseEnd_441705 < baseStart_441705 := by decide
  rcases family_descends (prefixWord ++ tailWord_441705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441709 : List Nat := [1, 5, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_441709 : Nat := 118140960795 + 441709 * 2 ^ 59
def prefixEnd_441709 : Nat := 4983230072969 + 3 ^ 40 * 441709 * 2
def baseEnd_441709 : Nat := 151206017611278363470749

theorem tailTrace_441709 : CollatzResearch.WordTrace tailWord_441709 prefixEnd_441709 151206017611278363470749 := by
  unfold tailWord_441709
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110450756771205736392181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740300504514137157594787 16110450756771205736392181)
  ·
    refine ⟨1510354758447300537786767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16110450756771205736392181 1510354758447300537786767)
    ·
      refine ⟨2265532137670950806680151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510354758447300537786767 2265532137670950806680151)
      ·
        refine ⟨3398298206506426210020227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265532137670950806680151 3398298206506426210020227)
        ·
          refine ⟨5097447309759639315030341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398298206506426210020227 5097447309759639315030341)
          ·
            refine ⟨955771370579932371568189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5097447309759639315030341 955771370579932371568189)
            ·
              refine ⟨358414263967474639338071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 955771370579932371568189 358414263967474639338071)
              ·
                refine ⟨537621395951211959007107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358414263967474639338071 537621395951211959007107)
                ·
                  refine ⟨806432093926817938510661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537621395951211959007107 806432093926817938510661)
                  ·
                    refine ⟨151206017611278363470749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806432093926817938510661 151206017611278363470749)
                    ·
                      rfl

theorem cell22_441709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_441709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441709 prefixEnd_441709 := by exact prefixLift 441709
  have htrace : WordTrace (prefixWord ++ tailWord_441709) baseStart_441709 baseEnd_441709 := by
    simpa [prefixWord, tailWord_441709, baseEnd_441709] using wordTrace_append hprefix tailTrace_441709
  have hstable : (prefixWord ++ tailWord_441709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441709).length < 2 ^ (prefixWord ++ tailWord_441709).sum := by decide
  have hdescent : baseEnd_441709 < baseStart_441709 := by decide
  rcases family_descends (prefixWord ++ tailWord_441709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441735 : List Nat := [1, 1, 4, 2, 2, 2, 3, 7]
def baseStart_441735 : Nat := 118140960795 + 441735 * 2 ^ 59
def prefixEnd_441735 : Nat := 4983230072969 + 3 ^ 40 * 441735 * 2
def baseEnd_441735 : Nat := 16801657549180329146741

theorem tailTrace_441735 : CollatzResearch.WordTrace tailWord_441735 prefixEnd_441735 16801657549180329146741 := by
  unfold tailWord_441735
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111399054677012176838659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10740932703118008117892439 16111399054677012176838659)
  ·
    refine ⟨24167098582015518265257989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16111399054677012176838659 24167098582015518265257989)
    ·
      refine ⟨4531330984127909674735873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24167098582015518265257989 4531330984127909674735873)
      ·
        refine ⟨3398498238095932256051905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4531330984127909674735873 3398498238095932256051905)
        ·
          refine ⟨2548873678571949192038929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3398498238095932256051905 2548873678571949192038929)
          ·
            refine ⟨1911655258928961894029197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548873678571949192038929 1911655258928961894029197)
            ·
              refine ⟨716870722098360710260949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1911655258928961894029197 716870722098360710260949)
              ·
                refine ⟨16801657549180329146741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 716870722098360710260949 16801657549180329146741)
                ·
                  rfl

theorem cell22_441735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 7].length) (baseStart_441735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441735 prefixEnd_441735 := by exact prefixLift 441735
  have htrace : WordTrace (prefixWord ++ tailWord_441735) baseStart_441735 baseEnd_441735 := by
    simpa [prefixWord, tailWord_441735, baseEnd_441735] using wordTrace_append hprefix tailTrace_441735
  have hstable : (prefixWord ++ tailWord_441735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441735).length < 2 ^ (prefixWord ++ tailWord_441735).sum := by decide
  have hdescent : baseEnd_441735 < baseStart_441735 := by decide
  rcases family_descends (prefixWord ++ tailWord_441735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441767 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 5, 3]
def baseStart_441767 : Nat := 118140960795 + 441767 * 2 ^ 59
def prefixEnd_441767 : Nat := 4983230072969 + 3 ^ 40 * 441767 * 2
def baseEnd_441767 : Nat := 151225872196585545520571

theorem tailTrace_441767 : CollatzResearch.WordTrace tailWord_441767 prefixEnd_441767 151225872196585545520571 := by
  unfold tailWord_441767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112566190561081642003555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10741710793707387761335703 16112566190561081642003555)
  ·
    refine ⟨24168849285841622463005333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16112566190561081642003555 24168849285841622463005333)
    ·
      refine ⟨1132914810273826052953375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24168849285841622463005333 1132914810273826052953375)
      ·
        refine ⟨1699372215410739079430063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132914810273826052953375 1699372215410739079430063)
        ·
          refine ⟨2549058323116108619145095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699372215410739079430063 2549058323116108619145095)
          ·
            refine ⟨3823587484674162928717643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549058323116108619145095 3823587484674162928717643)
            ·
              refine ⟨5735381227011244393076465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823587484674162928717643 5735381227011244393076465)
              ·
                refine ⟨4301535920258433294807349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735381227011244393076465 4301535920258433294807349)
                ·
                  refine ⟨403268992524228121388189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301535920258433294807349 403268992524228121388189)
                  ·
                    refine ⟨151225872196585545520571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403268992524228121388189 151225872196585545520571)
                    ·
                      rfl

theorem cell22_441767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_441767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441767 prefixEnd_441767 := by exact prefixLift 441767
  have htrace : WordTrace (prefixWord ++ tailWord_441767) baseStart_441767 baseEnd_441767 := by
    simpa [prefixWord, tailWord_441767, baseEnd_441767] using wordTrace_append hprefix tailTrace_441767
  have hstable : (prefixWord ++ tailWord_441767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441767).length < 2 ^ (prefixWord ++ tailWord_441767).sum := by decide
  have hdescent : baseEnd_441767 < baseStart_441767 := by decide
  rcases family_descends (prefixWord ++ tailWord_441767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441784 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 1, 3]
def baseStart_441784 : Nat := 118140960795 + 441784 * 2 ^ 59
def prefixEnd_441784 : Nat := 4983230072969 + 3 ^ 40 * 441784 * 2
def baseEnd_441784 : Nat := 151231691644003167845519

theorem tailTrace_441784 : CollatzResearch.WordTrace tailWord_441784 prefixEnd_441784 151231691644003167845519 := by
  unfold tailWord_441784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8056593115749746772686203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10742124154332995696914937 8056593115749746772686203)
  ·
    refine ⟨12084889673624620159029305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8056593115749746772686203 12084889673624620159029305)
    ·
      refine ⟨9063667255218465119271979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12084889673624620159029305 9063667255218465119271979)
      ·
        refine ⟨13595500882827697678907969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063667255218465119271979 13595500882827697678907969)
        ·
          refine ⟨10196625662120773259180977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13595500882827697678907969 10196625662120773259180977)
          ·
            refine ⟨7647469246590579944385733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10196625662120773259180977 7647469246590579944385733)
            ·
              refine ⟨1433900483735733739572325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7647469246590579944385733 1433900483735733739572325)
              ·
                refine ⟨268856340700450076169811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1433900483735733739572325 268856340700450076169811)
                ·
                  refine ⟨403284511050675114254717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268856340700450076169811 403284511050675114254717)
                  ·
                    refine ⟨151231691644003167845519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403284511050675114254717 151231691644003167845519)
                    ·
                      rfl

theorem cell22_441784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_441784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441784 prefixEnd_441784 := by exact prefixLift 441784
  have htrace : WordTrace (prefixWord ++ tailWord_441784) baseStart_441784 baseEnd_441784 := by
    simpa [prefixWord, tailWord_441784, baseEnd_441784] using wordTrace_append hprefix tailTrace_441784
  have hstable : (prefixWord ++ tailWord_441784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441784).length < 2 ^ (prefixWord ++ tailWord_441784).sum := by decide
  have hdescent : baseEnd_441784 < baseStart_441784 := by decide
  rcases family_descends (prefixWord ++ tailWord_441784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441795 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_441795 : Nat := 118140960795 + 441795 * 2 ^ 59
def prefixEnd_441795 : Nat := 4983230072969 + 3 ^ 40 * 441795 * 2
def baseEnd_441795 : Nat := 151235457168802805820485

theorem tailTrace_441795 : CollatzResearch.WordTrace tailWord_441795 prefixEnd_441795 151235457168802805820485 := by
  unfold tailWord_441795
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113587434459642424022839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10742391622973094949348559 16113587434459642424022839)
  ·
    refine ⟨24170381151689463636034259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16113587434459642424022839 24170381151689463636034259)
    ·
      refine ⟨36255571727534195454051389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24170381151689463636034259 36255571727534195454051389)
      ·
        refine ⟨13595839397825323295269271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36255571727534195454051389 13595839397825323295269271)
        ·
          refine ⟨20393759096737984942903907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13595839397825323295269271 20393759096737984942903907)
          ·
            refine ⟨30590638645106977414355861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20393759096737984942903907 30590638645106977414355861)
            ·
              refine ⟨1433936186489389566297931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30590638645106977414355861 1433936186489389566297931)
              ·
                refine ⟨2150904279734084349446897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433936186489389566297931 2150904279734084349446897)
                ·
                  refine ⟨1613178209800563262085173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2150904279734084349446897 1613178209800563262085173)
                  ·
                    refine ⟨151235457168802805820485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1613178209800563262085173 151235457168802805820485)
                    ·
                      rfl

theorem cell22_441795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_441795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441795 prefixEnd_441795 := by exact prefixLift 441795
  have htrace : WordTrace (prefixWord ++ tailWord_441795) baseStart_441795 baseEnd_441795 := by
    simpa [prefixWord, tailWord_441795, baseEnd_441795] using wordTrace_append hprefix tailTrace_441795
  have hstable : (prefixWord ++ tailWord_441795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441795).length < 2 ^ (prefixWord ++ tailWord_441795).sum := by decide
  have hdescent : baseEnd_441795 < baseStart_441795 := by decide
  rcases family_descends (prefixWord ++ tailWord_441795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441855 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_441855 : Nat := 118140960795 + 441855 * 2 ^ 59
def prefixEnd_441855 : Nat := 4983230072969 + 3 ^ 40 * 441855 * 2
def baseEnd_441855 : Nat := 151255996394982649320301

theorem tailTrace_441855 : CollatzResearch.WordTrace tailWord_441855 prefixEnd_441855 151255996394982649320301 := by
  unfold tailWord_441855
  simp only [CollatzResearch.WordTrace]
  refine ⟨16115775814242272671207019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10743850542828181780804679 16115775814242272671207019)
  ·
    refine ⟨24173663721363409006810529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16115775814242272671207019 24173663721363409006810529)
    ·
      refine ⟨18130247791022556755107897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24173663721363409006810529 18130247791022556755107897)
      ·
        refine ⟨13597685843266917566330923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18130247791022556755107897 13597685843266917566330923)
        ·
          refine ⟨20396528764900376349496385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13597685843266917566330923 20396528764900376349496385)
          ·
            refine ⟨15297396573675282262122289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20396528764900376349496385 15297396573675282262122289)
            ·
              refine ⟨11473047430256461696591717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15297396573675282262122289 11473047430256461696591717)
              ·
                refine ⟨2151196393173086568110947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11473047430256461696591717 2151196393173086568110947)
                ·
                  refine ⟨3226794589759629852166421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151196393173086568110947 3226794589759629852166421)
                  ·
                    refine ⟨151255996394982649320301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3226794589759629852166421 151255996394982649320301)
                    ·
                      rfl

theorem cell22_441855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_441855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441855 prefixEnd_441855 := by exact prefixLift 441855
  have htrace : WordTrace (prefixWord ++ tailWord_441855) baseStart_441855 baseEnd_441855 := by
    simpa [prefixWord, tailWord_441855, baseEnd_441855] using wordTrace_append hprefix tailTrace_441855
  have hstable : (prefixWord ++ tailWord_441855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441855).length < 2 ^ (prefixWord ++ tailWord_441855).sum := by decide
  have hdescent : baseEnd_441855 < baseStart_441855 := by decide
  rcases family_descends (prefixWord ++ tailWord_441855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441886 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_441886 : Nat := 118140960795 + 441886 * 2 ^ 59
def prefixEnd_441886 : Nat := 4983230072969 + 3 ^ 40 * 441886 * 2
def baseEnd_441886 : Nat := 151266608328508901795207

theorem tailTrace_441886 : CollatzResearch.WordTrace tailWord_441886 prefixEnd_441886 151266608328508901795207 := by
  unfold tailWord_441886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014613309641245620698189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10744604318086643310390341 2014613309641245620698189)
  ·
    refine ⟨755479991115467107761821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2014613309641245620698189 755479991115467107761821)
    ·
      refine ⟨283304996668300165410683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 755479991115467107761821 283304996668300165410683)
      ·
        refine ⟨424957495002450248116025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283304996668300165410683 424957495002450248116025)
        ·
          refine ⟨318718121251837686087019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424957495002450248116025 318718121251837686087019)
          ·
            refine ⟨478077181877756529130529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318718121251837686087019 478077181877756529130529)
            ·
              refine ⟨358557886408317396847897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478077181877756529130529 358557886408317396847897)
              ·
                refine ⟨268918414806238047635923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358557886408317396847897 268918414806238047635923)
                ·
                  refine ⟨403377622209357071453885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268918414806238047635923 403377622209357071453885)
                  ·
                    refine ⟨151266608328508901795207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403377622209357071453885 151266608328508901795207)
                    ·
                      rfl

theorem cell22_441886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_441886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441886 prefixEnd_441886 := by exact prefixLift 441886
  have htrace : WordTrace (prefixWord ++ tailWord_441886) baseStart_441886 baseEnd_441886 := by
    simpa [prefixWord, tailWord_441886, baseEnd_441886] using wordTrace_append hprefix tailTrace_441886
  have hstable : (prefixWord ++ tailWord_441886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441886).length < 2 ^ (prefixWord ++ tailWord_441886).sum := by decide
  have hdescent : baseEnd_441886 < baseStart_441886 := by decide
  rcases family_descends (prefixWord ++ tailWord_441886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441891 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 2, 3]
def baseStart_441891 : Nat := 118140960795 + 441891 * 2 ^ 59
def prefixEnd_441891 : Nat := 4983230072969 + 3 ^ 40 * 441891 * 2
def baseEnd_441891 : Nat := 151268319930690555420191

theorem tailTrace_441891 : CollatzResearch.WordTrace tailWord_441891 prefixEnd_441891 151268319930690555420191 := by
  unfold tailWord_441891
  simp only [CollatzResearch.WordTrace]
  refine ⟨16117088842111850819517527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10744725894741233879678351 16117088842111850819517527)
  ·
    refine ⟨24175633263167776229276291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16117088842111850819517527 24175633263167776229276291)
    ·
      refine ⟨36263449894751664343914437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24175633263167776229276291 36263449894751664343914437)
      ·
        refine ⟨6799396855265937064483957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36263449894751664343914437 6799396855265937064483957)
        ·
          refine ⟨637443455181181599795371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6799396855265937064483957 637443455181181599795371)
          ·
            refine ⟨956165182771772399693057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637443455181181599795371 956165182771772399693057)
            ·
              refine ⟨717123887078829299769793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956165182771772399693057 717123887078829299769793)
              ·
                refine ⟨537842915309121974827345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717123887078829299769793 537842915309121974827345)
                ·
                  refine ⟨403382186481841481120509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537842915309121974827345 403382186481841481120509)
                  ·
                    refine ⟨151268319930690555420191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403382186481841481120509 151268319930690555420191)
                    ·
                      rfl

theorem cell22_441891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3].length) (baseStart_441891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441891 prefixEnd_441891 := by exact prefixLift 441891
  have htrace : WordTrace (prefixWord ++ tailWord_441891) baseStart_441891 baseEnd_441891 := by
    simpa [prefixWord, tailWord_441891, baseEnd_441891] using wordTrace_append hprefix tailTrace_441891
  have hstable : (prefixWord ++ tailWord_441891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441891).length < 2 ^ (prefixWord ++ tailWord_441891).sum := by decide
  have hdescent : baseEnd_441891 < baseStart_441891 := by decide
  rcases family_descends (prefixWord ++ tailWord_441891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441919 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 3, 3]
def baseStart_441919 : Nat := 118140960795 + 441919 * 2 ^ 59
def prefixEnd_441919 : Nat := 4983230072969 + 3 ^ 40 * 441919 * 2
def baseEnd_441919 : Nat := 151277904902907815720105

theorem tailTrace_441919 : CollatzResearch.WordTrace tailWord_441919 prefixEnd_441919 151277904902907815720105 := by
  unfold tailWord_441919
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118110086010411601536811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10745406724006941067691207 16118110086010411601536811)
  ·
    refine ⟨24177165129015617402305217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16118110086010411601536811 24177165129015617402305217)
    ·
      refine ⟨18132873846761713051728913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24177165129015617402305217 18132873846761713051728913)
      ·
        refine ⟨13599655385071284788796685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18132873846761713051728913 13599655385071284788796685)
        ·
          refine ⟨5099870769401731795798757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13599655385071284788796685 5099870769401731795798757)
          ·
            refine ⟨956225769262824711712267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5099870769401731795798757 956225769262824711712267)
            ·
              refine ⟨1434338653894237067568401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956225769262824711712267 1434338653894237067568401)
              ·
                refine ⟨1075753990420677800676301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434338653894237067568401 1075753990420677800676301)
                ·
                  refine ⟨403407746407754175253613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075753990420677800676301 403407746407754175253613)
                  ·
                    refine ⟨151277904902907815720105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403407746407754175253613 151277904902907815720105)
                    ·
                      rfl

theorem cell22_441919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_441919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441919 prefixEnd_441919 := by exact prefixLift 441919
  have htrace : WordTrace (prefixWord ++ tailWord_441919) baseStart_441919 baseEnd_441919 := by
    simpa [prefixWord, tailWord_441919, baseEnd_441919] using wordTrace_append hprefix tailTrace_441919
  have hstable : (prefixWord ++ tailWord_441919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441919).length < 2 ^ (prefixWord ++ tailWord_441919).sum := by decide
  have hdescent : baseEnd_441919 < baseStart_441919 := by decide
  rcases family_descends (prefixWord ++ tailWord_441919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441936 : List Nat := [2, 1, 1, 1, 1, 3, 6, 3, 1, 3]
def baseStart_441936 : Nat := 118140960795 + 441936 * 2 ^ 59
def prefixEnd_441936 : Nat := 4983230072969 + 3 ^ 40 * 441936 * 2
def baseEnd_441936 : Nat := 151283724350325438045053

theorem tailTrace_441936 : CollatzResearch.WordTrace tailWord_441936 prefixEnd_441936 151283724350325438045053 := by
  unfold tailWord_441936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059365063474411752452831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10745820084632549003270441 8059365063474411752452831)
  ·
    refine ⟨12089047595211617628679247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059365063474411752452831 12089047595211617628679247)
    ·
      refine ⟨18133571392817426443018871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12089047595211617628679247 18133571392817426443018871)
      ·
        refine ⟨27200357089226139664528307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133571392817426443018871 27200357089226139664528307)
        ·
          refine ⟨40800535633839209496792461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200357089226139664528307 40800535633839209496792461)
          ·
            refine ⟨15300200862689703561297173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40800535633839209496792461 15300200862689703561297173)
            ·
              refine ⟨717196915438579854435805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15300200862689703561297173 717196915438579854435805)
              ·
                refine ⟨268948843289467445413427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 717196915438579854435805 268948843289467445413427)
                ·
                  refine ⟨403423264934201168120141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268948843289467445413427 403423264934201168120141)
                  ·
                    refine ⟨151283724350325438045053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403423264934201168120141 151283724350325438045053)
                    ·
                      rfl

theorem cell22_441936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_441936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441936 prefixEnd_441936 := by exact prefixLift 441936
  have htrace : WordTrace (prefixWord ++ tailWord_441936) baseStart_441936 baseEnd_441936 := by
    simpa [prefixWord, tailWord_441936, baseEnd_441936] using wordTrace_append hprefix tailTrace_441936
  have hstable : (prefixWord ++ tailWord_441936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441936).length < 2 ^ (prefixWord ++ tailWord_441936).sum := by decide
  have hdescent : baseEnd_441936 < baseStart_441936 := by decide
  rcases family_descends (prefixWord ++ tailWord_441936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441942 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_441942 : Nat := 118140960795 + 441942 * 2 ^ 59
def prefixEnd_441942 : Nat := 4983230072969 + 3 ^ 40 * 441942 * 2
def baseEnd_441942 : Nat := 151285778272943422395035

theorem tailTrace_441942 : CollatzResearch.WordTrace tailWord_441942 prefixEnd_441942 151285778272943422395035 := by
  unfold tailWord_441942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1007434310307942908101505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10745965976618057686416053 1007434310307942908101505)
  ·
    refine ⟨755575732730957181076129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1007434310307942908101505 755575732730957181076129)
    ·
      refine ⟨566681799548217885807097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755575732730957181076129 566681799548217885807097)
      ·
        refine ⟨425011349661163414355323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566681799548217885807097 425011349661163414355323)
        ·
          refine ⟨637517024491745121532985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425011349661163414355323 637517024491745121532985)
          ·
            refine ⟨478137768368808841149739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637517024491745121532985 478137768368808841149739)
            ·
              refine ⟨717206652553213261724609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478137768368808841149739 717206652553213261724609)
              ·
                refine ⟨537904989414909946293457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717206652553213261724609 537904989414909946293457)
                ·
                  refine ⟨403428742061182459720093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537904989414909946293457 403428742061182459720093)
                  ·
                    refine ⟨151285778272943422395035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403428742061182459720093 151285778272943422395035)
                    ·
                      rfl

theorem cell22_441942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_441942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441942 prefixEnd_441942 := by exact prefixLift 441942
  have htrace : WordTrace (prefixWord ++ tailWord_441942) baseStart_441942 baseEnd_441942 := by
    simpa [prefixWord, tailWord_441942, baseEnd_441942] using wordTrace_append hprefix tailTrace_441942
  have hstable : (prefixWord ++ tailWord_441942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441942).length < 2 ^ (prefixWord ++ tailWord_441942).sum := by decide
  have hdescent : baseEnd_441942 < baseStart_441942 := by decide
  rcases family_descends (prefixWord ++ tailWord_441942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441977 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 6]
def baseStart_441977 : Nat := 118140960795 + 441977 * 2 ^ 59
def prefixEnd_441977 : Nat := 4983230072969 + 3 ^ 40 * 441977 * 2
def baseEnd_441977 : Nat := 50432586496071665923309

theorem tailTrace_441977 : CollatzResearch.WordTrace tailWord_441977 prefixEnd_441977 50432586496071665923309 := by
  unfold tailWord_441977
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120225519800287507148185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10746817013200191671432123 16120225519800287507148185)
  ·
    refine ⟨12090169139850215630361139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16120225519800287507148185 12090169139850215630361139)
    ·
      refine ⟨18135253709775323445541709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12090169139850215630361139 18135253709775323445541709)
      ·
        refine ⟨6800720141165746292078141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18135253709775323445541709 6800720141165746292078141)
        ·
          refine ⟨2550270052937154859529303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6800720141165746292078141 2550270052937154859529303)
          ·
            refine ⟨3825405079405732289293955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550270052937154859529303 3825405079405732289293955)
            ·
              refine ⟨5738107619108598433940933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3825405079405732289293955 5738107619108598433940933)
              ·
                refine ⟨1075895178582862206363925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5738107619108598433940933 1075895178582862206363925)
                ·
                  refine ⟨50432586496071665923309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1075895178582862206363925 50432586496071665923309)
                  ·
                    rfl

theorem cell22_441977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_441977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441977 prefixEnd_441977 := by exact prefixLift 441977
  have htrace : WordTrace (prefixWord ++ tailWord_441977) baseStart_441977 baseEnd_441977 := by
    simpa [prefixWord, tailWord_441977, baseEnd_441977] using wordTrace_append hprefix tailTrace_441977
  have hstable : (prefixWord ++ tailWord_441977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441977).length < 2 ^ (prefixWord ++ tailWord_441977).sum := by decide
  have hdescent : baseEnd_441977 < baseStart_441977 := by decide
  rcases family_descends (prefixWord ++ tailWord_441977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441979 : List Nat := [1, 1, 1, 1, 1, 4, 6, 2, 1, 4]
def baseStart_441979 : Nat := 118140960795 + 441979 * 2 ^ 59
def prefixEnd_441979 : Nat := 4983230072969 + 3 ^ 40 * 441979 * 2
def baseEnd_441979 : Nat := 151298444129087659219921

theorem tailTrace_441979 : CollatzResearch.WordTrace tailWord_441979 prefixEnd_441979 151298444129087659219921 := by
  unfold tailWord_441979
  simp only [CollatzResearch.WordTrace]
  refine ⟨16120298465793041848720991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10746865643862027899147327 16120298465793041848720991)
  ·
    refine ⟨24180447698689562773081487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16120298465793041848720991 24180447698689562773081487)
    ·
      refine ⟨36270671548034344159622231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24180447698689562773081487 36270671548034344159622231)
      ·
        refine ⟨54406007322051516239433347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36270671548034344159622231 54406007322051516239433347)
        ·
          refine ⟨81609010983077274359150021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54406007322051516239433347 81609010983077274359150021)
          ·
            refine ⟨15301689559326988942340629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81609010983077274359150021 15301689559326988942340629)
            ·
              refine ⟨717266698093452606672217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15301689559326988942340629 717266698093452606672217)
              ·
                refine ⟨537950023570089455004163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717266698093452606672217 537950023570089455004163)
                ·
                  refine ⟨806925035355134182506245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 537950023570089455004163 806925035355134182506245)
                  ·
                    refine ⟨151298444129087659219921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 806925035355134182506245 151298444129087659219921)
                    ·
                      rfl

theorem cell22_441979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 4].length) (baseStart_441979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_441979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_441979 prefixEnd_441979 := by exact prefixLift 441979
  have htrace : WordTrace (prefixWord ++ tailWord_441979) baseStart_441979 baseEnd_441979 := by
    simpa [prefixWord, tailWord_441979, baseEnd_441979] using wordTrace_append hprefix tailTrace_441979
  have hstable : (prefixWord ++ tailWord_441979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441979).length < 2 ^ (prefixWord ++ tailWord_441979).sum := by decide
  have hdescent : baseEnd_441979 < baseStart_441979 := by decide
  rcases family_descends (prefixWord ++ tailWord_441979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442030 : List Nat := [4, 1, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_442030 : Nat := 118140960795 + 442030 * 2 ^ 59
def prefixEnd_442030 : Nat := 4983230072969 + 3 ^ 40 * 442030 * 2
def baseEnd_442030 : Nat := 151315902471340526194765

theorem tailTrace_442030 : CollatzResearch.WordTrace tailWord_442030 prefixEnd_442030 151315902471340526194765 := by
  unfold tailWord_442030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015269823576034694853443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10748105725738851705885029 2015269823576034694853443)
  ·
    refine ⟨3022904735364052042280165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015269823576034694853443 3022904735364052042280165)
    ·
      refine ⟨566794637880759757927531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3022904735364052042280165 566794637880759757927531)
      ·
        refine ⟨850191956821139636891297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566794637880759757927531 850191956821139636891297)
        ·
          refine ⟨637643967615854727668473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850191956821139636891297 637643967615854727668473)
          ·
            refine ⟨478232975711891045751355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637643967615854727668473 478232975711891045751355)
            ·
              refine ⟨717349463567836568627033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478232975711891045751355 717349463567836568627033)
              ·
                refine ⟨538012097675877426470275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717349463567836568627033 538012097675877426470275)
                ·
                  refine ⟨807018146513816139705413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538012097675877426470275 807018146513816139705413)
                  ·
                    refine ⟨151315902471340526194765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807018146513816139705413 151315902471340526194765)
                    ·
                      rfl

theorem cell22_442030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_442030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442030 prefixEnd_442030 := by exact prefixLift 442030
  have htrace : WordTrace (prefixWord ++ tailWord_442030) baseStart_442030 baseEnd_442030 := by
    simpa [prefixWord, tailWord_442030, baseEnd_442030] using wordTrace_append hprefix tailTrace_442030
  have hstable : (prefixWord ++ tailWord_442030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442030).length < 2 ^ (prefixWord ++ tailWord_442030).sum := by decide
  have hdescent : baseEnd_442030 < baseStart_442030 := by decide
  rcases family_descends (prefixWord ++ tailWord_442030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442084 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 5]
def baseStart_442084 : Nat := 118140960795 + 442084 * 2 ^ 59
def prefixEnd_442084 : Nat := 4983230072969 + 3 ^ 40 * 442084 * 2
def baseEnd_442084 : Nat := 50444795924967461781533

theorem tailTrace_442084 : CollatzResearch.WordTrace tailWord_442084 prefixEnd_442084 50444795924967461781533 := by
  unfold tailWord_442084
  simp only [CollatzResearch.WordTrace]
  refine ⟨8062064065206322390646653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10749418753608429854195537 8062064065206322390646653)
  ·
    refine ⟨3023274024452370896492495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8062064065206322390646653 3023274024452370896492495)
    ·
      refine ⟨4534911036678556344738743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023274024452370896492495 4534911036678556344738743)
      ·
        refine ⟨6802366555017834517108115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4534911036678556344738743 6802366555017834517108115)
        ·
          refine ⟨10203549832526751775662173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6802366555017834517108115 10203549832526751775662173)
          ·
            refine ⟨3826331187197531915873315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10203549832526751775662173 3826331187197531915873315)
            ·
              refine ⟨5739496780796297873809973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3826331187197531915873315 5739496780796297873809973)
              ·
                refine ⟨538077823199652925669685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5739496780796297873809973 538077823199652925669685)
                ·
                  refine ⟨50444795924967461781533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 538077823199652925669685 50444795924967461781533)
                  ·
                    rfl

theorem cell22_442084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_442084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442084 prefixEnd_442084 := by exact prefixLift 442084
  have htrace : WordTrace (prefixWord ++ tailWord_442084) baseStart_442084 baseEnd_442084 := by
    simpa [prefixWord, tailWord_442084, baseEnd_442084] using wordTrace_append hprefix tailTrace_442084
  have hstable : (prefixWord ++ tailWord_442084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442084).length < 2 ^ (prefixWord ++ tailWord_442084).sum := by decide
  have hdescent : baseEnd_442084 < baseStart_442084 := by decide
  rcases family_descends (prefixWord ++ tailWord_442084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442148 : List Nat := [2, 3, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_442148 : Nat := 118140960795 + 442148 * 2 ^ 59
def prefixEnd_442148 : Nat := 4983230072969 + 3 ^ 40 * 442148 * 2
def baseEnd_442148 : Nat := 151356296282827551744403

theorem tailTrace_442148 : CollatzResearch.WordTrace tailWord_442148 prefixEnd_442148 151356296282827551744403 := by
  unfold tailWord_442148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8063231201090391855811549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10750974934787189141082065 8063231201090391855811549)
  ·
    refine ⟨3023711700408896945929331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8063231201090391855811549 3023711700408896945929331)
    ·
      refine ⟨4535567550613345418893997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3023711700408896945929331 4535567550613345418893997)
      ·
        refine ⟨1700837831480004532085249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4535567550613345418893997 1700837831480004532085249)
        ·
          refine ⟨1275628373610003399063937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1700837831480004532085249 1275628373610003399063937)
          ·
            refine ⟨956721280207502549297953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1275628373610003399063937 956721280207502549297953)
            ·
              refine ⟨717540960155626911973465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 956721280207502549297953 717540960155626911973465)
              ·
                refine ⟨538155720116720183980099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717540960155626911973465 538155720116720183980099)
                ·
                  refine ⟨807233580175080275970149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 538155720116720183980099 807233580175080275970149)
                  ·
                    refine ⟨151356296282827551744403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807233580175080275970149 151356296282827551744403)
                    ·
                      rfl

theorem cell22_442148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_442148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442148 prefixEnd_442148 := by exact prefixLift 442148
  have htrace : WordTrace (prefixWord ++ tailWord_442148) baseStart_442148 baseEnd_442148 := by
    simpa [prefixWord, tailWord_442148, baseEnd_442148] using wordTrace_append hprefix tailTrace_442148
  have hstable : (prefixWord ++ tailWord_442148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442148).length < 2 ^ (prefixWord ++ tailWord_442148).sum := by decide
  have hdescent : baseEnd_442148 < baseStart_442148 := by decide
  rcases family_descends (prefixWord ++ tailWord_442148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442161 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_442161 : Nat := 118140960795 + 442161 * 2 ^ 59
def prefixEnd_442161 : Nat := 4983230072969 + 3 ^ 40 * 442161 * 2
def baseEnd_442161 : Nat := 151360746448499851169363

theorem tailTrace_442161 : CollatzResearch.WordTrace tailWord_442161 prefixEnd_442161 151360746448499851169363 := by
  unfold tailWord_442161
  simp only [CollatzResearch.WordTrace]
  refine ⟨16126936551133686931846337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10751291034089124621230891 16126936551133686931846337)
  ·
    refine ⟨12095202413350265198884753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16126936551133686931846337 12095202413350265198884753)
    ·
      refine ⟨9071401810012698899163565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12095202413350265198884753 9071401810012698899163565)
      ·
        refine ⟨3401775678754762087186337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9071401810012698899163565 3401775678754762087186337)
        ·
          refine ⟨2551331759066071565389753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3401775678754762087186337 2551331759066071565389753)
          ·
            refine ⟨1913498819299553674042315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2551331759066071565389753 1913498819299553674042315)
            ·
              refine ⟨2870248228949330511063473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913498819299553674042315 2870248228949330511063473)
              ·
                refine ⟨2152686171711997883297605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2870248228949330511063473 2152686171711997883297605)
                ·
                  refine ⟨403628657195999603118301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2152686171711997883297605 403628657195999603118301)
                  ·
                    refine ⟨151360746448499851169363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403628657195999603118301 151360746448499851169363)
                    ·
                      rfl

theorem cell22_442161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_442161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442161 prefixEnd_442161 := by exact prefixLift 442161
  have htrace : WordTrace (prefixWord ++ tailWord_442161) baseStart_442161 baseEnd_442161 := by
    simpa [prefixWord, tailWord_442161, baseEnd_442161] using wordTrace_append hprefix tailTrace_442161
  have hstable : (prefixWord ++ tailWord_442161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442161).length < 2 ^ (prefixWord ++ tailWord_442161).sum := by decide
  have hdescent : baseEnd_442161 < baseStart_442161 := by decide
  rcases family_descends (prefixWord ++ tailWord_442161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442238 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_442238 : Nat := 118140960795 + 442238 * 2 ^ 59
def prefixEnd_442238 : Nat := 4983230072969 + 3 ^ 40 * 442238 * 2
def baseEnd_442238 : Nat := 151387105122097316994127

theorem tailTrace_442238 : CollatzResearch.WordTrace tailWord_442238 prefixEnd_442238 151387105122097316994127 := by
  unfold tailWord_442238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016218121481841135299921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10753163314569819388266245 2016218121481841135299921)
  ·
    refine ⟨1512163591111380851474941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2016218121481841135299921 1512163591111380851474941)
    ·
      refine ⟨567061346666767819303103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1512163591111380851474941 567061346666767819303103)
      ·
        refine ⟨850592020000151728954655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 567061346666767819303103 850592020000151728954655)
        ·
          refine ⟨1275888030000227593431983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850592020000151728954655 1275888030000227593431983)
          ·
            refine ⟨1913832045000341390147975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1275888030000227593431983 1913832045000341390147975)
            ·
              refine ⟨2870748067500512085221963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1913832045000341390147975 2870748067500512085221963)
              ·
                refine ⟨4306122101250768127832945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2870748067500512085221963 4306122101250768127832945)
                ·
                  refine ⟨3229591575938076095874709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4306122101250768127832945 3229591575938076095874709)
                  ·
                    refine ⟨151387105122097316994127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3229591575938076095874709 151387105122097316994127)
                    ·
                      rfl

theorem cell22_442238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_442238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442238 prefixEnd_442238 := by exact prefixLift 442238
  have htrace : WordTrace (prefixWord ++ tailWord_442238) baseStart_442238 baseEnd_442238 := by
    simpa [prefixWord, tailWord_442238, baseEnd_442238] using wordTrace_append hprefix tailTrace_442238
  have hstable : (prefixWord ++ tailWord_442238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442238).length < 2 ^ (prefixWord ++ tailWord_442238).sum := by decide
  have hdescent : baseEnd_442238 < baseStart_442238 := by decide
  rcases family_descends (prefixWord ++ tailWord_442238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442343 : List Nat := [1, 1, 5, 2, 3, 2, 8]
def baseStart_442343 : Nat := 118140960795 + 442343 * 2 ^ 59
def prefixEnd_442343 : Nat := 4983230072969 + 3 ^ 40 * 442343 * 2
def baseEnd_442343 : Nat := 5608261065478223819215

theorem tailTrace_442343 : CollatzResearch.WordTrace tailWord_442343 prefixEnd_442343 5608261065478223819215 := by
  unfold tailWord_442343
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133574636474332014971683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755716424316221343314455 16133574636474332014971683)
  ·
    refine ⟨24200361954711498022457525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16133574636474332014971683 24200361954711498022457525)
    ·
      refine ⟨2268783933254202939605393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24200361954711498022457525 2268783933254202939605393)
      ·
        refine ⟨1701587949940652204704045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2268783933254202939605393 1701587949940652204704045)
        ·
          refine ⟨638095481227744576764017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1701587949940652204704045 638095481227744576764017)
          ·
            refine ⟨478571610920808432573013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638095481227744576764017 478571610920808432573013)
            ·
              refine ⟨5608261065478223819215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 478571610920808432573013 5608261065478223819215)
              ·
                rfl

theorem cell22_442343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 8].length) (baseStart_442343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442343 prefixEnd_442343 := by exact prefixLift 442343
  have htrace : WordTrace (prefixWord ++ tailWord_442343) baseStart_442343 baseEnd_442343 := by
    simpa [prefixWord, tailWord_442343, baseEnd_442343] using wordTrace_append hprefix tailTrace_442343
  have hstable : (prefixWord ++ tailWord_442343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442343).length < 2 ^ (prefixWord ++ tailWord_442343).sum := by decide
  have hdescent : baseEnd_442343 < baseStart_442343 := by decide
  rcases family_descends (prefixWord ++ tailWord_442343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442349 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 4]
def baseStart_442349 : Nat := 118140960795 + 442349 * 2 ^ 59
def prefixEnd_442349 : Nat := 4983230072969 + 3 ^ 40 * 442349 * 2
def baseEnd_442349 : Nat := 50475034230176675822929

theorem tailTrace_442349 : CollatzResearch.WordTrace tailWord_442349 prefixEnd_442349 50475034230176675822929 := by
  unfold tailWord_442349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16133793474452595039690101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10755862316301730026460067 16133793474452595039690101)
  ·
    refine ⟨1512543138229930784970947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16133793474452595039690101 1512543138229930784970947)
    ·
      refine ⟨2268814707344896177456421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1512543138229930784970947 2268814707344896177456421)
      ·
        refine ⟨425402757627168033273079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2268814707344896177456421 425402757627168033273079)
        ·
          refine ⟨638104136440752049909619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425402757627168033273079 638104136440752049909619)
          ·
            refine ⟨957156204661128074864429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638104136440752049909619 957156204661128074864429)
            ·
              refine ⟨358933576747923028074161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957156204661128074864429 358933576747923028074161)
              ·
                refine ⟨269200182560942271055621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358933576747923028074161 269200182560942271055621)
                ·
                  refine ⟨50475034230176675822929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269200182560942271055621 50475034230176675822929)
                  ·
                    rfl

theorem cell22_442349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_442349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442349 prefixEnd_442349 := by exact prefixLift 442349
  have htrace : WordTrace (prefixWord ++ tailWord_442349) baseStart_442349 baseEnd_442349 := by
    simpa [prefixWord, tailWord_442349, baseEnd_442349] using wordTrace_append hprefix tailTrace_442349
  have hstable : (prefixWord ++ tailWord_442349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442349).length < 2 ^ (prefixWord ++ tailWord_442349).sum := by decide
  have hdescent : baseEnd_442349 < baseStart_442349 := by decide
  rcases family_descends (prefixWord ++ tailWord_442349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442418 : List Nat := [3, 2, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_442418 : Nat := 118140960795 + 442418 * 2 ^ 59
def prefixEnd_442418 : Nat := 4983230072969 + 3 ^ 40 * 442418 * 2
def baseEnd_442418 : Nat := 151448722800636847493575

theorem tailTrace_442418 : CollatzResearch.WordTrace tailWord_442418 prefixEnd_442418 151448722800636847493575 := by
  unfold tailWord_442418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034077527800654955987977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10757540074135079882634605 4034077527800654955987977)
  ·
    refine ⟨3025558145850491216990983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4034077527800654955987977 3025558145850491216990983)
    ·
      refine ⟨4538337218775736825486475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025558145850491216990983 4538337218775736825486475)
      ·
        refine ⟨6807505828163605238229713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538337218775736825486475 6807505828163605238229713)
        ·
          refine ⟨5105629371122703928672285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6807505828163605238229713 5105629371122703928672285)
          ·
            refine ⟨1914611014171013973252107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5105629371122703928672285 1914611014171013973252107)
            ·
              refine ⟨2871916521256520959878161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914611014171013973252107 2871916521256520959878161)
              ·
                refine ⟨2153937390942390719908621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2871916521256520959878161 2153937390942390719908621)
                ·
                  refine ⟨807726521603396519965733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2153937390942390719908621 807726521603396519965733)
                  ·
                    refine ⟨151448722800636847493575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 807726521603396519965733 151448722800636847493575)
                    ·
                      rfl

theorem cell22_442418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_442418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442418 prefixEnd_442418 := by exact prefixLift 442418
  have htrace : WordTrace (prefixWord ++ tailWord_442418) baseStart_442418 baseEnd_442418 := by
    simpa [prefixWord, tailWord_442418, baseEnd_442418] using wordTrace_append hprefix tailTrace_442418
  have hstable : (prefixWord ++ tailWord_442418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442418).length < 2 ^ (prefixWord ++ tailWord_442418).sum := by decide
  have hdescent : baseEnd_442418 < baseStart_442418 := by decide
  rcases family_descends (prefixWord ++ tailWord_442418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442433 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 8]
def baseStart_442433 : Nat := 118140960795 + 442433 * 2 ^ 59
def prefixEnd_442433 : Nat := 4983230072969 + 3 ^ 40 * 442433 * 2
def baseEnd_442433 : Nat := 50484619202393936122843

theorem tailTrace_442433 : CollatzResearch.WordTrace tailWord_442433 prefixEnd_442433 50484619202393936122843 := by
  unfold tailWord_442433
  simp only [CollatzResearch.WordTrace]
  refine ⟨16136857206148277385747953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10757904804098851590498635 16136857206148277385747953)
  ·
    refine ⟨12102642904611208039310965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16136857206148277385747953 12102642904611208039310965)
    ·
      refine ⟨1134622772307300753685403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12102642904611208039310965 1134622772307300753685403)
      ·
        refine ⟨1701934158460951130528105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134622772307300753685403 1701934158460951130528105)
        ·
          refine ⟨1276450618845713347896079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701934158460951130528105 1276450618845713347896079)
          ·
            refine ⟨1914675928268570021844119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276450618845713347896079 1914675928268570021844119)
            ·
              refine ⟨2872013892402855032766179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1914675928268570021844119 2872013892402855032766179)
              ·
                refine ⟨4308020838604282549149269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872013892402855032766179 4308020838604282549149269)
                ·
                  refine ⟨50484619202393936122843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4308020838604282549149269 50484619202393936122843)
                  ·
                    rfl

theorem cell22_442433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_442433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442433 prefixEnd_442433 := by exact prefixLift 442433
  have htrace : WordTrace (prefixWord ++ tailWord_442433) baseStart_442433 baseEnd_442433 := by
    simpa [prefixWord, tailWord_442433, baseEnd_442433] using wordTrace_append hprefix tailTrace_442433
  have hstable : (prefixWord ++ tailWord_442433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442433).length < 2 ^ (prefixWord ++ tailWord_442433).sum := by decide
  have hdescent : baseEnd_442433 < baseStart_442433 := by decide
  rcases family_descends (prefixWord ++ tailWord_442433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442478 : List Nat := [4, 1, 2, 2, 1, 1, 2, 9]
def baseStart_442478 : Nat := 118140960795 + 442478 * 2 ^ 59
def prefixEnd_442478 : Nat := 4983230072969 + 3 ^ 40 * 442478 * 2
def baseEnd_442478 : Nat := 16829918002979632332599

theorem tailTrace_442478 : CollatzResearch.WordTrace tailWord_442478 prefixEnd_442478 16829918002979632332599 := by
  unfold tailWord_442478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017312311373156258892011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10758998993990166714090725 2017312311373156258892011)
  ·
    refine ⟨3025968467059734388338017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2017312311373156258892011 3025968467059734388338017)
    ·
      refine ⟨2269476350294800791253513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3025968467059734388338017 2269476350294800791253513)
      ·
        refine ⟨1702107262721100593440135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2269476350294800791253513 1702107262721100593440135)
        ·
          refine ⟨2553160894081650890160203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1702107262721100593440135 2553160894081650890160203)
          ·
            refine ⟨3829741341122476335240305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2553160894081650890160203 3829741341122476335240305)
            ·
              refine ⟨2872306005841857251430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3829741341122476335240305 2872306005841857251430229)
              ·
                refine ⟨16829918002979632332599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2872306005841857251430229 16829918002979632332599)
                ·
                  rfl

theorem cell22_442478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_442478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442478 prefixEnd_442478 := by exact prefixLift 442478
  have htrace : WordTrace (prefixWord ++ tailWord_442478) baseStart_442478 baseEnd_442478 := by
    simpa [prefixWord, tailWord_442478, baseEnd_442478] using wordTrace_append hprefix tailTrace_442478
  have hstable : (prefixWord ++ tailWord_442478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442478).length < 2 ^ (prefixWord ++ tailWord_442478).sum := by decide
  have hdescent : baseEnd_442478 < baseStart_442478 := by decide
  rcases family_descends (prefixWord ++ tailWord_442478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442518 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_442518 : Nat := 118140960795 + 442518 * 2 ^ 59
def prefixEnd_442518 : Nat := 4983230072969 + 3 ^ 40 * 442518 * 2
def baseEnd_442518 : Nat := 50494318281423306664423

theorem tailTrace_442518 : CollatzResearch.WordTrace tailWord_442518 prefixEnd_442518 50494318281423306664423 := by
  unfold tailWord_442518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008747338177521056412013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10759971607226891268394805 1008747338177521056412013)
  ·
    refine ⟨378280251816570396154505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1008747338177521056412013 378280251816570396154505)
    ·
      refine ⟨283710188862427797115879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378280251816570396154505 283710188862427797115879)
      ·
        refine ⟨425565283293641695673819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283710188862427797115879 425565283293641695673819)
        ·
          refine ⟨638347924940462543510729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425565283293641695673819 638347924940462543510729)
          ·
            refine ⟨478760943705346907633047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638347924940462543510729 478760943705346907633047)
            ·
              refine ⟨718141415558020361449571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478760943705346907633047 718141415558020361449571)
              ·
                refine ⟨1077212123337030542174357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718141415558020361449571 1077212123337030542174357)
                ·
                  refine ⟨50494318281423306664423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1077212123337030542174357 50494318281423306664423)
                  ·
                    rfl

theorem cell22_442518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_442518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442518 prefixEnd_442518 := by exact prefixLift 442518
  have htrace : WordTrace (prefixWord ++ tailWord_442518) baseStart_442518 baseEnd_442518 := by
    simpa [prefixWord, tailWord_442518, baseEnd_442518] using wordTrace_append hprefix tailTrace_442518
  have hstable : (prefixWord ++ tailWord_442518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442518).length < 2 ^ (prefixWord ++ tailWord_442518).sum := by decide
  have hdescent : baseEnd_442518 < baseStart_442518 := by decide
  rcases family_descends (prefixWord ++ tailWord_442518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442527 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 3, 3]
def baseStart_442527 : Nat := 118140960795 + 442527 * 2 ^ 59
def prefixEnd_442527 : Nat := 4983230072969 + 3 ^ 40 * 442527 * 2
def baseEnd_442527 : Nat := 151486035728196896518241

theorem tailTrace_442527 : CollatzResearch.WordTrace tailWord_442527 prefixEnd_442527 151486035728196896518241 := by
  unfold tailWord_442527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16140285667807731439669835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10760190445205154293113223 16140285667807731439669835)
  ·
    refine ⟨24210428501711597159504753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16140285667807731439669835 24210428501711597159504753)
    ·
      refine ⟨18157821376283697869628565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24210428501711597159504753 18157821376283697869628565)
      ·
        refine ⟨851147877013298337638839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18157821376283697869628565 851147877013298337638839)
        ·
          refine ⟨1276721815519947506458259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 851147877013298337638839 1276721815519947506458259)
          ·
            refine ⟨1915082723279921259687389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276721815519947506458259 1915082723279921259687389)
            ·
              refine ⟨718156021229970472382771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1915082723279921259687389 718156021229970472382771)
              ·
                refine ⟨1077234031844955708574157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718156021229970472382771 1077234031844955708574157)
                ·
                  refine ⟨403962761941858390715309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077234031844955708574157 403962761941858390715309)
                  ·
                    refine ⟨151486035728196896518241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 403962761941858390715309 151486035728196896518241)
                    ·
                      rfl

theorem cell22_442527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_442527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442527 prefixEnd_442527 := by exact prefixLift 442527
  have htrace : WordTrace (prefixWord ++ tailWord_442527) baseStart_442527 baseEnd_442527 := by
    simpa [prefixWord, tailWord_442527, baseEnd_442527] using wordTrace_append hprefix tailTrace_442527
  have hstable : (prefixWord ++ tailWord_442527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442527).length < 2 ^ (prefixWord ++ tailWord_442527).sum := by decide
  have hdescent : baseEnd_442527 < baseStart_442527 := by decide
  rcases family_descends (prefixWord ++ tailWord_442527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442583 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_442583 : Nat := 118140960795 + 442583 * 2 ^ 59
def prefixEnd_442583 : Nat := 4983230072969 + 3 ^ 40 * 442583 * 2
def baseEnd_442583 : Nat := 151505205672631417118069

theorem tailTrace_442583 : CollatzResearch.WordTrace tailWord_442583 prefixEnd_442583 151505205672631417118069 := by
  unfold tailWord_442583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16142328155604853003708403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10761552103736568669138935 16142328155604853003708403)
  ·
    refine ⟨24213492233407279505562605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16142328155604853003708403 24213492233407279505562605)
    ·
      refine ⟨9080059587527729814585977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24213492233407279505562605 9080059587527729814585977)
      ·
        refine ⟨6810044690645797360939483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9080059587527729814585977 6810044690645797360939483)
        ·
          refine ⟨10215067035968696041409225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810044690645797360939483 10215067035968696041409225)
          ·
            refine ⟨7661300276976522031056919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10215067035968696041409225 7661300276976522031056919)
            ·
              refine ⟨11491950415464783046585379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7661300276976522031056919 11491950415464783046585379)
              ·
                refine ⟨17237925623197174569878069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11491950415464783046585379 17237925623197174569878069)
                ·
                  refine ⟨1616055527174735115926069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17237925623197174569878069 1616055527174735115926069)
                  ·
                    refine ⟨151505205672631417118069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1616055527174735115926069 151505205672631417118069)
                    ·
                      rfl

theorem cell22_442583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_442583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442583 prefixEnd_442583 := by exact prefixLift 442583
  have htrace : WordTrace (prefixWord ++ tailWord_442583) baseStart_442583 baseEnd_442583 := by
    simpa [prefixWord, tailWord_442583, baseEnd_442583] using wordTrace_append hprefix tailTrace_442583
  have hstable : (prefixWord ++ tailWord_442583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442583).length < 2 ^ (prefixWord ++ tailWord_442583).sum := by decide
  have hdescent : baseEnd_442583 < baseStart_442583 := by decide
  rcases family_descends (prefixWord ++ tailWord_442583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442600 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 1, 5]
def baseStart_442600 : Nat := 118140960795 + 442600 * 2 ^ 59
def prefixEnd_442600 : Nat := 4983230072969 + 3 ^ 40 * 442600 * 2
def baseEnd_442600 : Nat := 151511025120049039443017

theorem tailTrace_442600 : CollatzResearch.WordTrace tailWord_442600 prefixEnd_442600 151511025120049039443017 := by
  unfold tailWord_442600
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071474098271632453538627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10761965464362176604718169 8071474098271632453538627)
  ·
    refine ⟨12107211147407448680307941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071474098271632453538627 12107211147407448680307941)
    ·
      refine ⟨2270102090138896627557739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12107211147407448680307941 2270102090138896627557739)
      ·
        refine ⟨3405153135208344941336609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2270102090138896627557739 3405153135208344941336609)
        ·
          refine ⟨2553864851406258706002457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3405153135208344941336609 2553864851406258706002457)
          ·
            refine ⟨1915398638554694029501843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2553864851406258706002457 1915398638554694029501843)
            ·
              refine ⟨2873097957832041044252765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1915398638554694029501843 2873097957832041044252765)
              ·
                refine ⟨1077411734187015391594787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2873097957832041044252765 1077411734187015391594787)
                ·
                  refine ⟨1616117601280523087392181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1077411734187015391594787 1616117601280523087392181)
                  ·
                    refine ⟨151511025120049039443017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1616117601280523087392181 151511025120049039443017)
                    ·
                      rfl

theorem cell22_442600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_442600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442600 prefixEnd_442600 := by exact prefixLift 442600
  have htrace : WordTrace (prefixWord ++ tailWord_442600) baseStart_442600 baseEnd_442600 := by
    simpa [prefixWord, tailWord_442600, baseEnd_442600] using wordTrace_append hprefix tailTrace_442600
  have hstable : (prefixWord ++ tailWord_442600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442600).length < 2 ^ (prefixWord ++ tailWord_442600).sum := by decide
  have hdescent : baseEnd_442600 < baseStart_442600 := by decide
  rcases family_descends (prefixWord ++ tailWord_442600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442643 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_442643 : Nat := 118140960795 + 442643 * 2 ^ 59
def prefixEnd_442643 : Nat := 4983230072969 + 3 ^ 40 * 442643 * 2
def baseEnd_442643 : Nat := 151525744898811260617885

theorem tailTrace_442643 : CollatzResearch.WordTrace tailWord_442643 prefixEnd_442643 151525744898811260617885 := by
  unfold tailWord_442643
  simp only [CollatzResearch.WordTrace]
  refine ⟨16144516535387483250892583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10763011023591655500595055 16144516535387483250892583)
  ·
    refine ⟨24216774803081224876338875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16144516535387483250892583 24216774803081224876338875)
    ·
      refine ⟨36325162204621837314508313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24216774803081224876338875 36325162204621837314508313)
      ·
        refine ⟨27243871653466377985881235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36325162204621837314508313 27243871653466377985881235)
        ·
          refine ⟨40865807480199566978821853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27243871653466377985881235 40865807480199566978821853)
          ·
            refine ⟨15324677805074837617058195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40865807480199566978821853 15324677805074837617058195)
            ·
              refine ⟨22987016707612256425587293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15324677805074837617058195 22987016707612256425587293)
              ·
                refine ⟨8620131265354596159595235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22987016707612256425587293 8620131265354596159595235)
                ·
                  refine ⟨12930196898031894239392853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8620131265354596159595235 12930196898031894239392853)
                  ·
                    refine ⟨151525744898811260617885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12930196898031894239392853 151525744898811260617885)
                    ·
                      rfl

theorem cell22_442643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_442643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442643 prefixEnd_442643 := by exact prefixLift 442643
  have htrace : WordTrace (prefixWord ++ tailWord_442643) baseStart_442643 baseEnd_442643 := by
    simpa [prefixWord, tailWord_442643, baseEnd_442643] using wordTrace_append hprefix tailTrace_442643
  have hstable : (prefixWord ++ tailWord_442643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442643).length < 2 ^ (prefixWord ++ tailWord_442643).sum := by decide
  have hdescent : baseEnd_442643 < baseStart_442643 := by decide
  rcases family_descends (prefixWord ++ tailWord_442643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442664 : List Nat := [2, 1, 5, 1, 3, 2, 2, 6]
def baseStart_442664 : Nat := 118140960795 + 442664 * 2 ^ 59
def prefixEnd_442664 : Nat := 4983230072969 + 3 ^ 40 * 442664 * 2
def baseEnd_442664 : Nat := 16836992625330467315869

theorem tailTrace_442664 : CollatzResearch.WordTrace tailWord_442664 prefixEnd_442664 16836992625330467315869 := by
  unfold tailWord_442664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8072641234155701918703523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10763521645540935891604697 8072641234155701918703523)
  ·
    refine ⟨12108961851233552878055285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8072641234155701918703523 12108961851233552878055285)
    ·
      refine ⟨1135215173553145582317683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12108961851233552878055285 1135215173553145582317683)
      ·
        refine ⟨1702822760329718373476525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1135215173553145582317683 1702822760329718373476525)
        ·
          refine ⟨638558535123644390053697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1702822760329718373476525 638558535123644390053697)
          ·
            refine ⟨478918901342733292540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638558535123644390053697 478918901342733292540273)
            ·
              refine ⟨359189176007049969405205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478918901342733292540273 359189176007049969405205)
              ·
                refine ⟨16836992625330467315869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 359189176007049969405205 16836992625330467315869)
                ·
                  rfl

theorem cell22_442664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 6].length) (baseStart_442664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442664 prefixEnd_442664 := by exact prefixLift 442664
  have htrace : WordTrace (prefixWord ++ tailWord_442664) baseStart_442664 baseEnd_442664 := by
    simpa [prefixWord, tailWord_442664, baseEnd_442664] using wordTrace_append hprefix tailTrace_442664
  have hstable : (prefixWord ++ tailWord_442664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442664).length < 2 ^ (prefixWord ++ tailWord_442664).sum := by decide
  have hdescent : baseEnd_442664 < baseStart_442664 := by decide
  rcases family_descends (prefixWord ++ tailWord_442664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442737 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 4]
def baseStart_442737 : Nat := 118140960795 + 442737 * 2 ^ 59
def prefixEnd_442737 : Nat := 4983230072969 + 3 ^ 40 * 442737 * 2
def baseEnd_442737 : Nat := 50519307673275449589199

theorem tailTrace_442737 : CollatzResearch.WordTrace tailWord_442737 prefixEnd_442737 50519307673275449589199 := by
  unfold tailWord_442737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16147944997046937304814465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10765296664697958203209643 16147944997046937304814465)
  ·
    refine ⟨12110958747785202978610849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16147944997046937304814465 12110958747785202978610849)
    ·
      refine ⟨9083219060838902233958137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12110958747785202978610849 9083219060838902233958137)
      ·
        refine ⟨6812414295629176675468603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9083219060838902233958137 6812414295629176675468603)
        ·
          refine ⟨10218621443443765013202905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6812414295629176675468603 10218621443443765013202905)
          ·
            refine ⟨7663966082582823759902179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10218621443443765013202905 7663966082582823759902179)
            ·
              refine ⟨11495949123874235639853269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7663966082582823759902179 11495949123874235639853269)
              ·
                refine ⟨269436307590802397809061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11495949123874235639853269 269436307590802397809061)
                ·
                  refine ⟨50519307673275449589199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269436307590802397809061 50519307673275449589199)
                  ·
                    rfl

theorem cell22_442737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_442737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442737 prefixEnd_442737 := by exact prefixLift 442737
  have htrace : WordTrace (prefixWord ++ tailWord_442737) baseStart_442737 baseEnd_442737 := by
    simpa [prefixWord, tailWord_442737, baseEnd_442737] using wordTrace_append hprefix tailTrace_442737
  have hstable : (prefixWord ++ tailWord_442737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442737).length < 2 ^ (prefixWord ++ tailWord_442737).sum := by decide
  have hdescent : baseEnd_442737 < baseStart_442737 := by decide
  rcases family_descends (prefixWord ++ tailWord_442737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442784 : List Nat := [2, 1, 1, 4, 1, 5, 1, 1, 2, 4]
def baseStart_442784 : Nat := 118140960795 + 442784 * 2 ^ 59
def prefixEnd_442784 : Nat := 4983230072969 + 3 ^ 40 * 442784 * 2
def baseEnd_442784 : Nat := 151574012080333892842453

theorem tailTrace_442784 : CollatzResearch.WordTrace tailWord_442784 prefixEnd_442784 151574012080333892842453 := by
  unfold tailWord_442784
  simp only [CollatzResearch.WordTrace]
  refine ⟨8074829613938332165887703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10766439485251109554516937 8074829613938332165887703)
  ·
    refine ⟨12112244420907498248831555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8074829613938332165887703 12112244420907498248831555)
    ·
      refine ⟨18168366631361247373247333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12112244420907498248831555 18168366631361247373247333)
      ·
        refine ⟨3406568743380233882483875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18168366631361247373247333 3406568743380233882483875)
        ·
          refine ⟨5109853115070350823725813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406568743380233882483875 5109853115070350823725813)
          ·
            refine ⟨479048729537845389724295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5109853115070350823725813 479048729537845389724295)
            ·
              refine ⟨718573094306768084586443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479048729537845389724295 718573094306768084586443)
              ·
                refine ⟨1077859641460152126879665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718573094306768084586443 1077859641460152126879665)
                ·
                  refine ⟨808394731095114095159749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1077859641460152126879665 808394731095114095159749)
                  ·
                    refine ⟨151574012080333892842453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 808394731095114095159749 151574012080333892842453)
                    ·
                      rfl

theorem cell22_442784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_442784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442784 prefixEnd_442784 := by exact prefixLift 442784
  have htrace : WordTrace (prefixWord ++ tailWord_442784) baseStart_442784 baseEnd_442784 := by
    simpa [prefixWord, tailWord_442784, baseEnd_442784] using wordTrace_append hprefix tailTrace_442784
  have hstable : (prefixWord ++ tailWord_442784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442784).length < 2 ^ (prefixWord ++ tailWord_442784).sum := by decide
  have hdescent : baseEnd_442784 < baseStart_442784 := by decide
  rcases family_descends (prefixWord ++ tailWord_442784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442814 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_442814 : Nat := 118140960795 + 442814 * 2 ^ 59
def prefixEnd_442814 : Nat := 4983230072969 + 3 ^ 40 * 442814 * 2
def baseEnd_442814 : Nat := 151584281693423814592361

theorem tailTrace_442814 : CollatzResearch.WordTrace tailWord_442814 prefixEnd_442814 151584281693423814592361 := by
  unfold tailWord_442814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018844177220997431920937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10767168945178652970244997 2018844177220997431920937)
  ·
    refine ⟨1514133132915748073940703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2018844177220997431920937 1514133132915748073940703)
    ·
      refine ⟨2271199699373622110911055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1514133132915748073940703 2271199699373622110911055)
      ·
        refine ⟨3406799549060433166366583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271199699373622110911055 3406799549060433166366583)
        ·
          refine ⟨5110199323590649749549875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3406799549060433166366583 5110199323590649749549875)
          ·
            refine ⟨7665298985385974624324813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110199323590649749549875 7665298985385974624324813)
            ·
              refine ⟨2874487119519740484121805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7665298985385974624324813 2874487119519740484121805)
              ·
                refine ⟨1077932669819902681545677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2874487119519740484121805 1077932669819902681545677)
                ·
                  refine ⟨404224751182463505579629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1077932669819902681545677 404224751182463505579629)
                  ·
                    refine ⟨151584281693423814592361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404224751182463505579629 151584281693423814592361)
                    ·
                      rfl

theorem cell22_442814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_442814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442814 prefixEnd_442814 := by exact prefixLift 442814
  have htrace : WordTrace (prefixWord ++ tailWord_442814) baseStart_442814 baseEnd_442814 := by
    simpa [prefixWord, tailWord_442814, baseEnd_442814] using wordTrace_append hprefix tailTrace_442814
  have hstable : (prefixWord ++ tailWord_442814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442814).length < 2 ^ (prefixWord ++ tailWord_442814).sum := by decide
  have hdescent : baseEnd_442814 < baseStart_442814 := by decide
  rcases family_descends (prefixWord ++ tailWord_442814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442891 : List Nat := [1, 1, 1, 1, 7, 3, 1, 2, 1, 4]
def baseStart_442891 : Nat := 118140960795 + 442891 * 2 ^ 59
def prefixEnd_442891 : Nat := 4983230072969 + 3 ^ 40 * 442891 * 2
def baseEnd_442891 : Nat := 151610640367021280417125

theorem tailTrace_442891 : CollatzResearch.WordTrace tailWord_442891 prefixEnd_442891 151610640367021280417125 := by
  unfold tailWord_442891
  simp only [CollatzResearch.WordTrace]
  refine ⟨16153561838489021605920527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10769041225659347737280351 16153561838489021605920527)
  ·
    refine ⟨24230342757733532408880791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16153561838489021605920527 24230342757733532408880791)
    ·
      refine ⟨36345514136600298613321187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24230342757733532408880791 36345514136600298613321187)
      ·
        refine ⟨54518271204900447919981781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36345514136600298613321187 54518271204900447919981781)
        ·
          refine ⟨1277771981364854248124573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54518271204900447919981781 1277771981364854248124573)
          ·
            refine ⟨479164493011820343046715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1277771981364854248124573 479164493011820343046715)
            ·
              refine ⟨718746739517730514570073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479164493011820343046715 718746739517730514570073)
              ·
                refine ⟨539060054638297885927555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718746739517730514570073 539060054638297885927555)
                ·
                  refine ⟨808590081957446828891333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 539060054638297885927555 808590081957446828891333)
                  ·
                    refine ⟨151610640367021280417125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 808590081957446828891333 151610640367021280417125)
                    ·
                      rfl

theorem cell22_442891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 4].length) (baseStart_442891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442891 prefixEnd_442891 := by exact prefixLift 442891
  have htrace : WordTrace (prefixWord ++ tailWord_442891) baseStart_442891 baseEnd_442891 := by
    simpa [prefixWord, tailWord_442891, baseEnd_442891] using wordTrace_append hprefix tailTrace_442891
  have hstable : (prefixWord ++ tailWord_442891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442891).length < 2 ^ (prefixWord ++ tailWord_442891).sum := by decide
  have hdescent : baseEnd_442891 < baseStart_442891 := by decide
  rcases family_descends (prefixWord ++ tailWord_442891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442904 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 1, 5]
def baseStart_442904 : Nat := 118140960795 + 442904 * 2 ^ 59
def prefixEnd_442904 : Nat := 4983230072969 + 3 ^ 40 * 442904 * 2
def baseEnd_442904 : Nat := 151615090532693579842085

theorem tailTrace_442904 : CollatzResearch.WordTrace tailWord_442904 prefixEnd_442904 151615090532693579842085 := by
  unfold tailWord_442904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8077017993720962413071883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10769357324961283217429177 8077017993720962413071883)
  ·
    refine ⟨12115526990581443619607825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8077017993720962413071883 12115526990581443619607825)
    ·
      refine ⟨9086645242936082714705869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12115526990581443619607825 9086645242936082714705869)
      ·
        refine ⟨3407491966101031018014701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9086645242936082714705869 3407491966101031018014701)
        ·
          refine ⟨1277809487287886631755513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3407491966101031018014701 1277809487287886631755513)
          ·
            refine ⟨958357115465914973816635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1277809487287886631755513 958357115465914973816635)
            ·
              refine ⟨1437535673198872460724953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958357115465914973816635 1437535673198872460724953)
              ·
                refine ⟨1078151754899154345543715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1437535673198872460724953 1078151754899154345543715)
                ·
                  refine ⟨1617227632348731518315573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1078151754899154345543715 1617227632348731518315573)
                  ·
                    refine ⟨151615090532693579842085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1617227632348731518315573 151615090532693579842085)
                    ·
                      rfl

theorem cell22_442904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_442904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442904 prefixEnd_442904 := by exact prefixLift 442904
  have htrace : WordTrace (prefixWord ++ tailWord_442904) baseStart_442904 baseEnd_442904 := by
    simpa [prefixWord, tailWord_442904, baseEnd_442904] using wordTrace_append hprefix tailTrace_442904
  have hstable : (prefixWord ++ tailWord_442904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442904).length < 2 ^ (prefixWord ++ tailWord_442904).sum := by decide
  have hdescent : baseEnd_442904 < baseStart_442904 := by decide
  rcases family_descends (prefixWord ++ tailWord_442904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_442949 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_442949 : Nat := 118140960795 + 442949 * 2 ^ 59
def prefixEnd_442949 : Nat := 4983230072969 + 3 ^ 40 * 442949 * 2
def baseEnd_442949 : Nat := 151630494952328462466947

theorem tailTrace_442949 : CollatzResearch.WordTrace tailWord_442949 prefixEnd_442949 151630494952328462466947 := by
  unfold tailWord_442949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16155677272278897511531901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10770451514852598341021267 16155677272278897511531901)
  ·
    refine ⟨6058378977104586566824463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16155677272278897511531901 6058378977104586566824463)
    ·
      refine ⟨9087568465656879850236695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058378977104586566824463 9087568465656879850236695)
      ·
        refine ⟨13631352698485319775355043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9087568465656879850236695 13631352698485319775355043)
        ·
          refine ⟨20447029047727979663032565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13631352698485319775355043 20447029047727979663032565)
          ·
            refine ⟨1916908973224498093409303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20447029047727979663032565 1916908973224498093409303)
            ·
              refine ⟨2875363459836747140113955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1916908973224498093409303 2875363459836747140113955)
              ·
                refine ⟨4313045189755120710170933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2875363459836747140113955 4313045189755120710170933)
                ·
                  refine ⟨404347986539542566578525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4313045189755120710170933 404347986539542566578525)
                  ·
                    refine ⟨151630494952328462466947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404347986539542566578525 151630494952328462466947)
                    ·
                      rfl

theorem cell22_442949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_442949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_442949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_442949 prefixEnd_442949 := by exact prefixLift 442949
  have htrace : WordTrace (prefixWord ++ tailWord_442949) baseStart_442949 baseEnd_442949 := by
    simpa [prefixWord, tailWord_442949, baseEnd_442949] using wordTrace_append hprefix tailTrace_442949
  have hstable : (prefixWord ++ tailWord_442949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_442949).length < 2 ^ (prefixWord ++ tailWord_442949).sum := by decide
  have hdescent : baseEnd_442949 < baseStart_442949 := by decide
  rcases family_descends (prefixWord ++ tailWord_442949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443007 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 8]
def baseStart_443007 : Nat := 118140960795 + 443007 * 2 ^ 59
def prefixEnd_443007 : Nat := 4983230072969 + 3 ^ 40 * 443007 * 2
def baseEnd_443007 : Nat := 50550116512545214838923

theorem tailTrace_443007 : CollatzResearch.WordTrace tailWord_443007 prefixEnd_443007 50550116512545214838923 := by
  unfold tailWord_443007
  simp only [CollatzResearch.WordTrace]
  refine ⟨16157792706068773417143275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10771861804045848944762183 16157792706068773417143275)
  ·
    refine ⟨24236689059103160125714913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16157792706068773417143275 24236689059103160125714913)
    ·
      refine ⟨18177516794327370094286185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24236689059103160125714913 18177516794327370094286185)
      ·
        refine ⟨13633137595745527570714639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18177516794327370094286185 13633137595745527570714639)
        ·
          refine ⟨20449706393618291356071959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13633137595745527570714639 20449706393618291356071959)
          ·
            refine ⟨30674559590427437034107939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20449706393618291356071959 30674559590427437034107939)
            ·
              refine ⟨46011839385641155551161909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30674559590427437034107939 46011839385641155551161909)
              ·
                refine ⟨4313609942403858332921429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46011839385641155551161909 4313609942403858332921429)
                ·
                  refine ⟨50550116512545214838923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4313609942403858332921429 50550116512545214838923)
                  ·
                    rfl

theorem cell22_443007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_443007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443007 prefixEnd_443007 := by exact prefixLift 443007
  have htrace : WordTrace (prefixWord ++ tailWord_443007) baseStart_443007 baseEnd_443007 := by
    simpa [prefixWord, tailWord_443007, baseEnd_443007] using wordTrace_append hprefix tailTrace_443007
  have hstable : (prefixWord ++ tailWord_443007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443007).length < 2 ^ (prefixWord ++ tailWord_443007).sum := by decide
  have hdescent : baseEnd_443007 < baseStart_443007 := by decide
  rcases family_descends (prefixWord ++ tailWord_443007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443047 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 5]
def baseStart_443047 : Nat := 118140960795 + 443047 * 2 ^ 59
def prefixEnd_443047 : Nat := 4983230072969 + 3 ^ 40 * 443047 * 2
def baseEnd_443047 : Nat := 50554680785029624505549

theorem tailTrace_443047 : CollatzResearch.WordTrace tailWord_443047 prefixEnd_443047 50554680785029624505549 := by
  unfold tailWord_443047
  simp only [CollatzResearch.WordTrace]
  refine ⟨16159251625923860248599395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10772834417282573499066263 16159251625923860248599395)
  ·
    refine ⟨24238877438885790372899093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16159251625923860248599395 24238877438885790372899093)
    ·
      refine ⟨1136197379947771423729645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24238877438885790372899093 1136197379947771423729645)
      ·
        refine ⟨426074017480414283898617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1136197379947771423729645 426074017480414283898617)
        ·
          refine ⟨319555513110310712923963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426074017480414283898617 319555513110310712923963)
          ·
            refine ⟨479333269665466069385945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319555513110310712923963 479333269665466069385945)
            ·
              refine ⟨359499952249099552039459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479333269665466069385945 359499952249099552039459)
              ·
                refine ⟨539249928373649328059189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359499952249099552039459 539249928373649328059189)
                ·
                  refine ⟨50554680785029624505549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539249928373649328059189 50554680785029624505549)
                  ·
                    rfl

theorem cell22_443047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 5].length) (baseStart_443047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443047 prefixEnd_443047 := by exact prefixLift 443047
  have htrace : WordTrace (prefixWord ++ tailWord_443047) baseStart_443047 baseEnd_443047 := by
    simpa [prefixWord, tailWord_443047, baseEnd_443047] using wordTrace_append hprefix tailTrace_443047
  have hstable : (prefixWord ++ tailWord_443047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443047).length < 2 ^ (prefixWord ++ tailWord_443047).sum := by decide
  have hdescent : baseEnd_443047 < baseStart_443047 := by decide
  rcases family_descends (prefixWord ++ tailWord_443047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443069 : List Nat := [1, 4, 1, 2, 1, 3, 2, 8]
def baseStart_443069 : Nat := 118140960795 + 443069 * 2 ^ 59
def prefixEnd_443069 : Nat := 4983230072969 + 3 ^ 40 * 443069 * 2
def baseEnd_443069 : Nat := 16852397044965349940731

theorem tailTrace_443069 : CollatzResearch.WordTrace tailWord_443069 prefixEnd_443069 16852397044965349940731 := by
  unfold tailWord_443069
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160054031844158005900261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10773369354562772003933507 16160054031844158005900261)
  ·
    refine ⟨3030010130970779626106299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16160054031844158005900261 3030010130970779626106299)
    ·
      refine ⟨4545015196456169439159449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030010130970779626106299 4545015196456169439159449)
      ·
        refine ⟨3408761397342127079369587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4545015196456169439159449 3408761397342127079369587)
        ·
          refine ⟨5113142096013190619054381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3408761397342127079369587 5113142096013190619054381)
          ·
            refine ⟨1917428286004946482145393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5113142096013190619054381 1917428286004946482145393)
            ·
              refine ⟨1438071214503709861609045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1917428286004946482145393 1438071214503709861609045)
              ·
                refine ⟨16852397044965349940731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1438071214503709861609045 16852397044965349940731)
                ·
                  rfl

theorem cell22_443069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 8].length) (baseStart_443069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443069 prefixEnd_443069 := by exact prefixLift 443069
  have htrace : WordTrace (prefixWord ++ tailWord_443069) baseStart_443069 baseEnd_443069 := by
    simpa [prefixWord, tailWord_443069, baseEnd_443069] using wordTrace_append hprefix tailTrace_443069
  have hstable : (prefixWord ++ tailWord_443069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443069).length < 2 ^ (prefixWord ++ tailWord_443069).sum := by decide
  have hdescent : baseEnd_443069 < baseStart_443069 := by decide
  rcases family_descends (prefixWord ++ tailWord_443069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443071 : List Nat := [1, 1, 2, 2, 2, 5, 2, 1, 2, 4]
def baseStart_443071 : Nat := 118140960795 + 443071 * 2 ^ 59
def prefixEnd_443071 : Nat := 4983230072969 + 3 ^ 40 * 443071 * 2
def baseEnd_443071 : Nat := 151672258045560810916573

theorem tailTrace_443071 : CollatzResearch.WordTrace tailWord_443071 prefixEnd_443071 151672258045560810916573 := by
  unfold tailWord_443071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16160126977836912347473067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10773417985224608231648711 16160126977836912347473067)
  ·
    refine ⟨24240190466755368521209601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16160126977836912347473067 24240190466755368521209601)
    ·
      refine ⟨18180142850066526390907201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24240190466755368521209601 18180142850066526390907201)
      ·
        refine ⟨13635107137549894793180401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18180142850066526390907201 13635107137549894793180401)
        ·
          refine ⟨10226330353162421094885301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13635107137549894793180401 10226330353162421094885301)
          ·
            refine ⟨958718470608976977645497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10226330353162421094885301 958718470608976977645497)
            ·
              refine ⟨719038852956732733234123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958718470608976977645497 719038852956732733234123)
              ·
                refine ⟨1078558279435099099851185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719038852956732733234123 1078558279435099099851185)
                ·
                  refine ⟨808918709576324324888389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1078558279435099099851185 808918709576324324888389)
                  ·
                    refine ⟨151672258045560810916573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 808918709576324324888389 151672258045560810916573)
                    ·
                      rfl

theorem cell22_443071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_443071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443071 prefixEnd_443071 := by exact prefixLift 443071
  have htrace : WordTrace (prefixWord ++ tailWord_443071) baseStart_443071 baseEnd_443071 := by
    simpa [prefixWord, tailWord_443071, baseEnd_443071] using wordTrace_append hprefix tailTrace_443071
  have hstable : (prefixWord ++ tailWord_443071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443071).length < 2 ^ (prefixWord ++ tailWord_443071).sum := by decide
  have hdescent : baseEnd_443071 < baseStart_443071 := by decide
  rcases family_descends (prefixWord ++ tailWord_443071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443090 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 2, 3]
def baseStart_443090 : Nat := 118140960795 + 443090 * 2 ^ 59
def prefixEnd_443090 : Nat := 4983230072969 + 3 ^ 40 * 443090 * 2
def baseEnd_443090 : Nat := 151678762133851094691515

theorem tailTrace_443090 : CollatzResearch.WordTrace tailWord_443090 prefixEnd_443090 151678762133851094691515 := by
  unfold tailWord_443090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040204991192019648103681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10773879976512052394943149 4040204991192019648103681)
  ·
    refine ⟨3030153743394014736077761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4040204991192019648103681 3030153743394014736077761)
    ·
      refine ⟨2272615307545511052058321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3030153743394014736077761 2272615307545511052058321)
      ·
        refine ⟨1704461480659133289043741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2272615307545511052058321 1704461480659133289043741)
        ·
          refine ⟨639173055247174983391403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1704461480659133289043741 639173055247174983391403)
          ·
            refine ⟨958759582870762475087105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639173055247174983391403 958759582870762475087105)
            ·
              refine ⟨719069687153071856315329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958759582870762475087105 719069687153071856315329)
              ·
                refine ⟨539302265364803892236497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719069687153071856315329 539302265364803892236497)
                ·
                  refine ⟨404476699023602919177373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539302265364803892236497 404476699023602919177373)
                  ·
                    refine ⟨151678762133851094691515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404476699023602919177373 151678762133851094691515)
                    ·
                      rfl

theorem cell22_443090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_443090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443090 prefixEnd_443090 := by exact prefixLift 443090
  have htrace : WordTrace (prefixWord ++ tailWord_443090) baseStart_443090 baseEnd_443090 := by
    simpa [prefixWord, tailWord_443090, baseEnd_443090] using wordTrace_append hprefix tailTrace_443090
  have hstable : (prefixWord ++ tailWord_443090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443090).length < 2 ^ (prefixWord ++ tailWord_443090).sum := by decide
  have hdescent : baseEnd_443090 < baseStart_443090 := by decide
  rcases family_descends (prefixWord ++ tailWord_443090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443092 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 4]
def baseStart_443092 : Nat := 118140960795 + 443092 * 2 ^ 59
def prefixEnd_443092 : Nat := 4983230072969 + 3 ^ 40 * 443092 * 2
def baseEnd_443092 : Nat := 50559815591574585380503

theorem tailTrace_443092 : CollatzResearch.WordTrace tailWord_443092 prefixEnd_443092 50559815591574585380503 := by
  unfold tailWord_443092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080446455380416466993765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10773928607173888622658353 8080446455380416466993765)
  ·
    refine ⟨1515083710383828087561331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8080446455380416466993765 1515083710383828087561331)
    ·
      refine ⟨2272625565575742131341997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515083710383828087561331 2272625565575742131341997)
      ·
        refine ⟨852234587090903299253249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2272625565575742131341997 852234587090903299253249)
        ·
          refine ⟨639175940318177474439937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852234587090903299253249 639175940318177474439937)
          ·
            refine ⟨479381955238633105829953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639175940318177474439937 479381955238633105829953)
            ·
              refine ⟨359536466428974829372465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479381955238633105829953 359536466428974829372465)
              ·
                refine ⟨269652349821731122029349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359536466428974829372465 269652349821731122029349)
                ·
                  refine ⟨50559815591574585380503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269652349821731122029349 50559815591574585380503)
                  ·
                    rfl

theorem cell22_443092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_443092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443092 prefixEnd_443092 := by exact prefixLift 443092
  have htrace : WordTrace (prefixWord ++ tailWord_443092) baseStart_443092 baseEnd_443092 := by
    simpa [prefixWord, tailWord_443092, baseEnd_443092] using wordTrace_append hprefix tailTrace_443092
  have hstable : (prefixWord ++ tailWord_443092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443092).length < 2 ^ (prefixWord ++ tailWord_443092).sum := by decide
  have hdescent : baseEnd_443092 < baseStart_443092 := by decide
  rcases family_descends (prefixWord ++ tailWord_443092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443114 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_443114 : Nat := 118140960795 + 443114 * 2 ^ 59
def prefixEnd_443114 : Nat := 4983230072969 + 3 ^ 40 * 443114 * 2
def baseEnd_443114 : Nat := 50562325941441010697147

theorem tailTrace_443114 : CollatzResearch.WordTrace tailWord_443114 prefixEnd_443114 50562325941441010697147 := by
  unfold tailWord_443114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040423829170282672822099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10774463544454087127525597 4040423829170282672822099)
  ·
    refine ⟨6060635743755424009233149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040423829170282672822099 6060635743755424009233149)
    ·
      refine ⟨2272738403908284003462431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6060635743755424009233149 2272738403908284003462431)
      ·
        refine ⟨3409107605862426005193647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2272738403908284003462431 3409107605862426005193647)
        ·
          refine ⟨5113661408793639007790471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409107605862426005193647 5113661408793639007790471)
          ·
            refine ⟨7670492113190458511685707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5113661408793639007790471 7670492113190458511685707)
            ·
              refine ⟨11505738169785687767528561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7670492113190458511685707 11505738169785687767528561)
              ·
                refine ⟨8629303627339265825646421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11505738169785687767528561 8629303627339265825646421)
                ·
                  refine ⟨50562325941441010697147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8629303627339265825646421 50562325941441010697147)
                  ·
                    rfl

theorem cell22_443114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_443114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443114 prefixEnd_443114 := by exact prefixLift 443114
  have htrace : WordTrace (prefixWord ++ tailWord_443114) baseStart_443114 baseEnd_443114 := by
    simpa [prefixWord, tailWord_443114, baseEnd_443114] using wordTrace_append hprefix tailTrace_443114
  have hstable : (prefixWord ++ tailWord_443114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443114).length < 2 ^ (prefixWord ++ tailWord_443114).sum := by decide
  have hdescent : baseEnd_443114 < baseStart_443114 := by decide
  rcases family_descends (prefixWord ++ tailWord_443114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443118 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_443118 : Nat := 118140960795 + 443118 * 2 ^ 59
def prefixEnd_443118 : Nat := 4983230072969 + 3 ^ 40 * 443118 * 2
def baseEnd_443118 : Nat := 151688347106068354991429

theorem tailTrace_443118 : CollatzResearch.WordTrace tailWord_443118 prefixEnd_443118 151688347106068354991429 := by
  unfold tailWord_443118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020230151083329921804251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10774560805777759582956005 2020230151083329921804251)
  ·
    refine ⟨3030345226624994882706377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2020230151083329921804251 3030345226624994882706377)
    ·
      refine ⟨2272758919968746162029783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3030345226624994882706377 2272758919968746162029783)
      ·
        refine ⟨3409138379953119243044675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2272758919968746162029783 3409138379953119243044675)
        ·
          refine ⟨5113707569929678864567013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409138379953119243044675 5113707569929678864567013)
          ·
            refine ⟨958820169361814787106315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5113707569929678864567013 958820169361814787106315)
            ·
              refine ⟨1438230254042722180659473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958820169361814787106315 1438230254042722180659473)
              ·
                refine ⟨1078672690532041635494605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1438230254042722180659473 1078672690532041635494605)
                ·
                  refine ⟨404502258949515613310477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1078672690532041635494605 404502258949515613310477)
                  ·
                    refine ⟨151688347106068354991429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404502258949515613310477 151688347106068354991429)
                    ·
                      rfl

theorem cell22_443118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_443118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443118 prefixEnd_443118 := by exact prefixLift 443118
  have htrace : WordTrace (prefixWord ++ tailWord_443118) baseStart_443118 baseEnd_443118 := by
    simpa [prefixWord, tailWord_443118, baseEnd_443118] using wordTrace_append hprefix tailTrace_443118
  have hstable : (prefixWord ++ tailWord_443118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443118).length < 2 ^ (prefixWord ++ tailWord_443118).sum := by decide
  have hdescent : baseEnd_443118 < baseStart_443118 := by decide
  rcases family_descends (prefixWord ++ tailWord_443118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443176 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 6]
def baseStart_443176 : Nat := 118140960795 + 443176 * 2 ^ 59
def prefixEnd_443176 : Nat := 4983230072969 + 3 ^ 40 * 443176 * 2
def baseEnd_443176 : Nat := 50569400563791845680417

theorem tailTrace_443176 : CollatzResearch.WordTrace tailWord_443176 prefixEnd_443176 50569400563791845680417 := by
  unfold tailWord_443176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8081978321228257640022691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10775971094971010186696921 8081978321228257640022691)
  ·
    refine ⟨12122967481842386460034037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8081978321228257640022691 12122967481842386460034037)
    ·
      refine ⟨1136528201422723730628191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12122967481842386460034037 1136528201422723730628191)
      ·
        refine ⟨1704792302134085595942287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1136528201422723730628191 1704792302134085595942287)
        ·
          refine ⟨2557188453201128393913431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704792302134085595942287 2557188453201128393913431)
          ·
            refine ⟨3835782679801692590870147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557188453201128393913431 3835782679801692590870147)
            ·
              refine ⟨5753674019702538886305221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3835782679801692590870147 5753674019702538886305221)
              ·
                refine ⟨1078813878694226041182229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5753674019702538886305221 1078813878694226041182229)
                ·
                  refine ⟨50569400563791845680417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1078813878694226041182229 50569400563791845680417)
                  ·
                    rfl

theorem cell22_443176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 6].length) (baseStart_443176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443176 prefixEnd_443176 := by exact prefixLift 443176
  have htrace : WordTrace (prefixWord ++ tailWord_443176) baseStart_443176 baseEnd_443176 := by
    simpa [prefixWord, tailWord_443176, baseEnd_443176] using wordTrace_append hprefix tailTrace_443176
  have hstable : (prefixWord ++ tailWord_443176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443176).length < 2 ^ (prefixWord ++ tailWord_443176).sum := by decide
  have hdescent : baseEnd_443176 < baseStart_443176 := by decide
  rcases family_descends (prefixWord ++ tailWord_443176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443191 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 6, 3]
def baseStart_443191 : Nat := 118140960795 + 443191 * 2 ^ 59
def prefixEnd_443191 : Nat := 4983230072969 + 3 ^ 40 * 443191 * 2
def baseEnd_443191 : Nat := 151713336497920497916205

theorem tailTrace_443191 : CollatzResearch.WordTrace tailWord_443191 prefixEnd_443191 151713336497920497916205 := by
  unfold tailWord_443191
  simp only [CollatzResearch.WordTrace]
  refine ⟨16164503737402172841841427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10776335824934781894560951 16164503737402172841841427)
  ·
    refine ⟨24246755606103259262762141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16164503737402172841841427 24246755606103259262762141)
    ·
      refine ⟨9092533352288722223535803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24246755606103259262762141 9092533352288722223535803)
      ·
        refine ⟨13638800028433083335303705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9092533352288722223535803 13638800028433083335303705)
        ·
          refine ⟨10229100021324812501477779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13638800028433083335303705 10229100021324812501477779)
          ·
            refine ⟨15343650031987218752216669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10229100021324812501477779 15343650031987218752216669)
            ·
              refine ⟨5753868761995207032081251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15343650031987218752216669 5753868761995207032081251)
              ·
                refine ⟨8630803142992810548121877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5753868761995207032081251 8630803142992810548121877)
                ·
                  refine ⟨404568897327787994443213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8630803142992810548121877 404568897327787994443213)
                  ·
                    refine ⟨151713336497920497916205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404568897327787994443213 151713336497920497916205)
                    ·
                      rfl

theorem cell22_443191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_443191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443191 prefixEnd_443191 := by exact prefixLift 443191
  have htrace : WordTrace (prefixWord ++ tailWord_443191) baseStart_443191 baseEnd_443191 := by
    simpa [prefixWord, tailWord_443191, baseEnd_443191] using wordTrace_append hprefix tailTrace_443191
  have hstable : (prefixWord ++ tailWord_443191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443191).length < 2 ^ (prefixWord ++ tailWord_443191).sum := by decide
  have hdescent : baseEnd_443191 < baseStart_443191 := by decide
  rcases family_descends (prefixWord ++ tailWord_443191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443208 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_443208 : Nat := 118140960795 + 443208 * 2 ^ 59
def prefixEnd_443208 : Nat := 4983230072969 + 3 ^ 40 * 443208 * 2
def baseEnd_443208 : Nat := 151719155945338120241153

theorem tailTrace_443208 : CollatzResearch.WordTrace tailWord_443208 prefixEnd_443208 151719155945338120241153 := by
  unfold tailWord_443208
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082561889170292372605139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10776749185560389830140185 8082561889170292372605139)
  ·
    refine ⟨12123842833755438558907709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8082561889170292372605139 12123842833755438558907709)
    ·
      refine ⟨4546441062658289459590391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12123842833755438558907709 4546441062658289459590391)
      ·
        refine ⟨6819661593987434189385587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4546441062658289459590391 6819661593987434189385587)
        ·
          refine ⟨10229492390981151284078381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6819661593987434189385587 10229492390981151284078381)
          ·
            refine ⟨3836059646617931731529393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10229492390981151284078381 3836059646617931731529393)
            ·
              refine ⟨2877044734963448798647045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3836059646617931731529393 2877044734963448798647045)
              ·
                refine ⟨539445887805646649746321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2877044734963448798647045 539445887805646649746321)
                ·
                  refine ⟨404584415854234987309741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539445887805646649746321 404584415854234987309741)
                  ·
                    refine ⟨151719155945338120241153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404584415854234987309741 151719155945338120241153)
                    ·
                      rfl

theorem cell22_443208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_443208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443208 prefixEnd_443208 := by exact prefixLift 443208
  have htrace : WordTrace (prefixWord ++ tailWord_443208) baseStart_443208 baseEnd_443208 := by
    simpa [prefixWord, tailWord_443208, baseEnd_443208] using wordTrace_append hprefix tailTrace_443208
  have hstable : (prefixWord ++ tailWord_443208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443208).length < 2 ^ (prefixWord ++ tailWord_443208).sum := by decide
  have hdescent : baseEnd_443208 < baseStart_443208 := by decide
  rcases family_descends (prefixWord ++ tailWord_443208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443221 : List Nat := [1, 3, 2, 2, 2, 1, 4, 7]
def baseStart_443221 : Nat := 118140960795 + 443221 * 2 ^ 59
def prefixEnd_443221 : Nat := 4983230072969 + 3 ^ 40 * 443221 * 2
def baseEnd_443221 : Nat := 16858178456778935518457

theorem tailTrace_443221 : CollatzResearch.WordTrace tailWord_443221 prefixEnd_443221 16858178456778935518457 := by
  unfold tailWord_443221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165597927293487965433517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10777065284862325310289011 16165597927293487965433517)
  ·
    refine ⟨6062099222735057987037569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16165597927293487965433517 6062099222735057987037569)
    ·
      refine ⟨4546574417051293490278177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6062099222735057987037569 4546574417051293490278177)
      ·
        refine ⟨3409930812788470117708633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4546574417051293490278177 3409930812788470117708633)
        ·
          refine ⟨2557448109591352588281475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3409930812788470117708633 2557448109591352588281475)
          ·
            refine ⟨3836172164387028882422213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2557448109591352588281475 3836172164387028882422213)
            ·
              refine ⟨719282280822567915454165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3836172164387028882422213 719282280822567915454165)
              ·
                refine ⟨16858178456778935518457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 719282280822567915454165 16858178456778935518457)
                ·
                  rfl

theorem cell22_443221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 7].length) (baseStart_443221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443221 prefixEnd_443221 := by exact prefixLift 443221
  have htrace : WordTrace (prefixWord ++ tailWord_443221) baseStart_443221 baseEnd_443221 := by
    simpa [prefixWord, tailWord_443221, baseEnd_443221] using wordTrace_append hprefix tailTrace_443221
  have hstable : (prefixWord ++ tailWord_443221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443221).length < 2 ^ (prefixWord ++ tailWord_443221).sum := by decide
  have hdescent : baseEnd_443221 < baseStart_443221 := by decide
  rcases family_descends (prefixWord ++ tailWord_443221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443225 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_443225 : Nat := 118140960795 + 443225 * 2 ^ 59
def prefixEnd_443225 : Nat := 4983230072969 + 3 ^ 40 * 443225 * 2
def baseEnd_443225 : Nat := 151724975392755742566101

theorem tailTrace_443225 : CollatzResearch.WordTrace tailWord_443225 prefixEnd_443225 151724975392755742566101 := by
  unfold tailWord_443225
  simp only [CollatzResearch.WordTrace]
  refine ⟨16165743819278996648579129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10777162546185997765719419 16165743819278996648579129)
  ·
    refine ⟨12124307864459247486434347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16165743819278996648579129 12124307864459247486434347)
    ·
      refine ⟨18186461796688871229651521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12124307864459247486434347 18186461796688871229651521)
      ·
        refine ⟨13639846347516653422238641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18186461796688871229651521 13639846347516653422238641)
        ·
          refine ⟨10229884760637490066678981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13639846347516653422238641 10229884760637490066678981)
          ·
            refine ⟨1918103392619529387502309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10229884760637490066678981 1918103392619529387502309)
            ·
              refine ⟨359644386116161760156683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1918103392619529387502309 359644386116161760156683)
              ·
                refine ⟨539466579174242640235025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359644386116161760156683 539466579174242640235025)
                ·
                  refine ⟨404599934380681980176269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 539466579174242640235025 404599934380681980176269)
                  ·
                    refine ⟨151724975392755742566101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404599934380681980176269 151724975392755742566101)
                    ·
                      rfl

theorem cell22_443225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_443225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443225 prefixEnd_443225 := by exact prefixLift 443225
  have htrace : WordTrace (prefixWord ++ tailWord_443225) baseStart_443225 baseEnd_443225 := by
    simpa [prefixWord, tailWord_443225, baseEnd_443225] using wordTrace_append hprefix tailTrace_443225
  have hstable : (prefixWord ++ tailWord_443225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443225).length < 2 ^ (prefixWord ++ tailWord_443225).sum := by decide
  have hdescent : baseEnd_443225 < baseStart_443225 := by decide
  rcases family_descends (prefixWord ++ tailWord_443225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443328 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_443328 : Nat := 118140960795 + 443328 * 2 ^ 59
def prefixEnd_443328 : Nat := 4983230072969 + 3 ^ 40 * 443328 * 2
def baseEnd_443328 : Nat := 50586744799232602413595

theorem tailTrace_443328 : CollatzResearch.WordTrace tailWord_443328 prefixEnd_443328 50586744799232602413595 := by
  unfold tailWord_443328
  simp only [CollatzResearch.WordTrace]
  refine ⟨8084750268952922619789319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10779667025270563493052425 8084750268952922619789319)
  ·
    refine ⟨12127125403429383929683979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8084750268952922619789319 12127125403429383929683979)
    ·
      refine ⟨18190688105144075894525969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12127125403429383929683979 18190688105144075894525969)
      ·
        refine ⟨13643016078858056920894477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18190688105144075894525969 13643016078858056920894477)
        ·
          refine ⟨5116131029571771345335429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13643016078858056920894477 5116131029571771345335429)
          ·
            refine ⟨959274568044707127250393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5116131029571771345335429 959274568044707127250393)
            ·
              refine ⟨719455926033530345437795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959274568044707127250393 719455926033530345437795)
              ·
                refine ⟨1079183889050295518156693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719455926033530345437795 1079183889050295518156693)
                ·
                  refine ⟨50586744799232602413595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1079183889050295518156693 50586744799232602413595)
                  ·
                    rfl

theorem cell22_443328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_443328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443328 prefixEnd_443328 := by exact prefixLift 443328
  have htrace : WordTrace (prefixWord ++ tailWord_443328) baseStart_443328 baseEnd_443328 := by
    simpa [prefixWord, tailWord_443328, baseEnd_443328] using wordTrace_append hprefix tailTrace_443328
  have hstable : (prefixWord ++ tailWord_443328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443328).length < 2 ^ (prefixWord ++ tailWord_443328).sum := by decide
  have hdescent : baseEnd_443328 < baseStart_443328 := by decide
  rcases family_descends (prefixWord ++ tailWord_443328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443343 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 1, 5]
def baseStart_443343 : Nat := 118140960795 + 443343 * 2 ^ 59
def prefixEnd_443343 : Nat := 4983230072969 + 3 ^ 40 * 443343 * 2
def baseEnd_443343 : Nat := 151765369204242768115739

theorem tailTrace_443343 : CollatzResearch.WordTrace tailWord_443343 prefixEnd_443343 151765369204242768115739 := by
  unfold tailWord_443343
  simp only [CollatzResearch.WordTrace]
  refine ⟨16170047632851502801374683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10780031755234335200916455 16170047632851502801374683)
  ·
    refine ⟨24255071449277254202062025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16170047632851502801374683 24255071449277254202062025)
    ·
      refine ⟨18191303586957940651546519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24255071449277254202062025 18191303586957940651546519)
      ·
        refine ⟨27286955380436910977319779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18191303586957940651546519 27286955380436910977319779)
        ·
          refine ⟨40930433070655366465979669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27286955380436910977319779 40930433070655366465979669)
          ·
            refine ⟨1918614050186970303092797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40930433070655366465979669 1918614050186970303092797)
            ·
              refine ⟨719480268820113863659799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1918614050186970303092797 719480268820113863659799)
              ·
                refine ⟨1079220403230170795489699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719480268820113863659799 1079220403230170795489699)
                ·
                  refine ⟨1618830604845256193234549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1079220403230170795489699 1618830604845256193234549)
                  ·
                    refine ⟨151765369204242768115739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1618830604845256193234549 151765369204242768115739)
                    ·
                      rfl

theorem cell22_443343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_443343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443343 prefixEnd_443343 := by exact prefixLift 443343
  have htrace : WordTrace (prefixWord ++ tailWord_443343) baseStart_443343 baseEnd_443343 := by
    simpa [prefixWord, tailWord_443343, baseEnd_443343] using wordTrace_append hprefix tailTrace_443343
  have hstable : (prefixWord ++ tailWord_443343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443343).length < 2 ^ (prefixWord ++ tailWord_443343).sum := by decide
  have hdescent : baseEnd_443343 < baseStart_443343 := by decide
  rcases family_descends (prefixWord ++ tailWord_443343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443463 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 8]
def baseStart_443463 : Nat := 118140960795 + 443463 * 2 ^ 59
def prefixEnd_443463 : Nat := 4983230072969 + 3 ^ 40 * 443463 * 2
def baseEnd_443463 : Nat := 50602149218867485038457

theorem tailTrace_443463 : CollatzResearch.WordTrace tailWord_443463 prefixEnd_443463 50602149218867485038457 := by
  unfold tailWord_443463
  simp only [CollatzResearch.WordTrace]
  refine ⟨16174424392416763295743043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10782949594944508863828695 16174424392416763295743043)
  ·
    refine ⟨24261636588625144943614565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16174424392416763295743043 24261636588625144943614565)
    ·
      refine ⟨4549056860367214676927731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24261636588625144943614565 4549056860367214676927731)
      ·
        refine ⟨6823585290550822015391597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4549056860367214676927731 6823585290550822015391597)
        ·
          refine ⟨2558844483956558255771849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6823585290550822015391597 2558844483956558255771849)
          ·
            refine ⟨1919133362967418691828887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2558844483956558255771849 1919133362967418691828887)
            ·
              refine ⟨2878700044451128037743331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1919133362967418691828887 2878700044451128037743331)
              ·
                refine ⟨4318050066676692056614997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878700044451128037743331 4318050066676692056614997)
                ·
                  refine ⟨50602149218867485038457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4318050066676692056614997 50602149218867485038457)
                  ·
                    rfl

theorem cell22_443463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_443463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443463 prefixEnd_443463 := by exact prefixLift 443463
  have htrace : WordTrace (prefixWord ++ tailWord_443463) baseStart_443463 baseEnd_443463 := by
    simpa [prefixWord, tailWord_443463, baseEnd_443463] using wordTrace_append hprefix tailTrace_443463
  have hstable : (prefixWord ++ tailWord_443463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443463).length < 2 ^ (prefixWord ++ tailWord_443463).sum := by decide
  have hdescent : baseEnd_443463 < baseStart_443463 := by decide
  rcases family_descends (prefixWord ++ tailWord_443463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443486 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_443486 : Nat := 118140960795 + 443486 * 2 ^ 59
def prefixEnd_443486 : Nat := 4983230072969 + 3 ^ 40 * 443486 * 2
def baseEnd_443486 : Nat := 50604773675546020596767

theorem tailTrace_443486 : CollatzResearch.WordTrace tailWord_443486 prefixEnd_443486 50604773675546020596767 := by
  unfold tailWord_443486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2021907908916679777978789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10783508847555625482553541 2021907908916679777978789)
  ·
    refine ⟨379107732921877458371023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2021907908916679777978789 379107732921877458371023)
    ·
      refine ⟨568661599382816187556535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379107732921877458371023 568661599382816187556535)
      ·
        refine ⟨852992399074224281334803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568661599382816187556535 852992399074224281334803)
        ·
          refine ⟨1279488598611336422002205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852992399074224281334803 1279488598611336422002205)
          ·
            refine ⟨479808224479251158250827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1279488598611336422002205 479808224479251158250827)
            ·
              refine ⟨719712336718876737376241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479808224479251158250827 719712336718876737376241)
              ·
                refine ⟨539784252539157553032181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719712336718876737376241 539784252539157553032181)
                ·
                  refine ⟨50604773675546020596767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 539784252539157553032181 50604773675546020596767)
                  ·
                    rfl

theorem cell22_443486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_443486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443486 prefixEnd_443486 := by exact prefixLift 443486
  have htrace : WordTrace (prefixWord ++ tailWord_443486) baseStart_443486 baseEnd_443486 := by
    simpa [prefixWord, tailWord_443486, baseEnd_443486] using wordTrace_append hprefix tailTrace_443486
  have hstable : (prefixWord ++ tailWord_443486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443486).length < 2 ^ (prefixWord ++ tailWord_443486).sum := by decide
  have hdescent : baseEnd_443486 < baseStart_443486 := by decide
  rcases family_descends (prefixWord ++ tailWord_443486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443510 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_443510 : Nat := 118140960795 + 443510 * 2 ^ 59
def prefixEnd_443510 : Nat := 4983230072969 + 3 ^ 40 * 443510 * 2
def baseEnd_443510 : Nat := 151822536717109999190227

theorem tailTrace_443510 : CollatzResearch.WordTrace tailWord_443510 prefixEnd_443510 151822536717109999190227 := by
  unfold tailWord_443510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011008663952905645168999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10784092415497660215135989 1011008663952905645168999)
  ·
    refine ⟨1516512995929358467753499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1011008663952905645168999 1516512995929358467753499)
    ·
      refine ⟨2274769493894037701630249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1516512995929358467753499 2274769493894037701630249)
      ·
        refine ⟨1706077120420528276222687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2274769493894037701630249 1706077120420528276222687)
        ·
          refine ⟨2559115680630792414334031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706077120420528276222687 2559115680630792414334031)
          ·
            refine ⟨3838673520946188621501047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2559115680630792414334031 3838673520946188621501047)
            ·
              refine ⟨5758010281419282932251571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838673520946188621501047 5758010281419282932251571)
              ·
                refine ⟨8637015422128924398377357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758010281419282932251571 8637015422128924398377357)
                ·
                  refine ⟨3238880783298346649391509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8637015422128924398377357 3238880783298346649391509)
                  ·
                    refine ⟨151822536717109999190227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3238880783298346649391509 151822536717109999190227)
                    ·
                      rfl

theorem cell22_443510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_443510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443510 prefixEnd_443510 := by exact prefixLift 443510
  have htrace : WordTrace (prefixWord ++ tailWord_443510) baseStart_443510 baseEnd_443510 := by
    simpa [prefixWord, tailWord_443510, baseEnd_443510] using wordTrace_append hprefix tailTrace_443510
  have hstable : (prefixWord ++ tailWord_443510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443510).length < 2 ^ (prefixWord ++ tailWord_443510).sum := by decide
  have hdescent : baseEnd_443510 < baseStart_443510 := by decide
  rcases family_descends (prefixWord ++ tailWord_443510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443523 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_443523 : Nat := 118140960795 + 443523 * 2 ^ 59
def prefixEnd_443523 : Nat := 4983230072969 + 3 ^ 40 * 443523 * 2
def baseEnd_443523 : Nat := 151826986882782298615187

theorem tailTrace_443523 : CollatzResearch.WordTrace tailWord_443523 prefixEnd_443523 151826986882782298615187 := by
  unfold tailWord_443523
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176612772199393542927223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10784408514799595695284815 16176612772199393542927223)
  ·
    refine ⟨24264919158299090314390835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16176612772199393542927223 24264919158299090314390835)
    ·
      refine ⟨36397378737448635471586253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24264919158299090314390835 36397378737448635471586253)
      ·
        refine ⟨13649017026543238301844845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36397378737448635471586253 13649017026543238301844845)
        ·
          refine ⟨5118381384953714363191817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13649017026543238301844845 5118381384953714363191817)
          ·
            refine ⟨3838786038715285772393863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5118381384953714363191817 3838786038715285772393863)
            ·
              refine ⟨5758179058072928658590795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3838786038715285772393863 5758179058072928658590795)
              ·
                refine ⟨8637268587109392987886193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5758179058072928658590795 8637268587109392987886193)
                ·
                  refine ⟨6477951440332044740914645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8637268587109392987886193 6477951440332044740914645)
                  ·
                    refine ⟨151826986882782298615187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6477951440332044740914645 151826986882782298615187)
                    ·
                      rfl

theorem cell22_443523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_443523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443523 prefixEnd_443523 := by exact prefixLift 443523
  have htrace : WordTrace (prefixWord ++ tailWord_443523) baseStart_443523 baseEnd_443523 := by
    simpa [prefixWord, tailWord_443523, baseEnd_443523] using wordTrace_append hprefix tailTrace_443523
  have hstable : (prefixWord ++ tailWord_443523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443523).length < 2 ^ (prefixWord ++ tailWord_443523).sum := by decide
  have hdescent : baseEnd_443523 < baseStart_443523 := by decide
  rcases family_descends (prefixWord ++ tailWord_443523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443525 : List Nat := [1, 3, 1, 1, 6, 1, 1, 8]
def baseStart_443525 : Nat := 118140960795 + 443525 * 2 ^ 59
def prefixEnd_443525 : Nat := 4983230072969 + 3 ^ 40 * 443525 * 2
def baseEnd_443525 : Nat := 16869741280406106673909

theorem tailTrace_443525 : CollatzResearch.WordTrace tailWord_443525 prefixEnd_443525 16869741280406106673909 := by
  unfold tailWord_443525
  simp only [CollatzResearch.WordTrace]
  refine ⟨16176685718192147884500029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10784457145461431923000019 16176685718192147884500029)
  ·
    refine ⟨6066257144322055456687511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16176685718192147884500029 6066257144322055456687511)
    ·
      refine ⟨9099385716483083185031267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6066257144322055456687511 9099385716483083185031267)
      ·
        refine ⟨13649078574724624777546901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9099385716483083185031267 13649078574724624777546901)
        ·
          refine ⟨639800558190216786447511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13649078574724624777546901 639800558190216786447511)
          ·
            refine ⟨959700837285325179671267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639800558190216786447511 959700837285325179671267)
            ·
              refine ⟨1439551255927987769506901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959700837285325179671267 1439551255927987769506901)
              ·
                refine ⟨16869741280406106673909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1439551255927987769506901 16869741280406106673909)
                ·
                  rfl

theorem cell22_443525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 8].length) (baseStart_443525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443525 prefixEnd_443525 := by exact prefixLift 443525
  have htrace : WordTrace (prefixWord ++ tailWord_443525) baseStart_443525 baseEnd_443525 := by
    simpa [prefixWord, tailWord_443525, baseEnd_443525] using wordTrace_append hprefix tailTrace_443525
  have hstable : (prefixWord ++ tailWord_443525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443525).length < 2 ^ (prefixWord ++ tailWord_443525).sum := by decide
  have hdescent : baseEnd_443525 < baseStart_443525 := by decide
  rcases family_descends (prefixWord ++ tailWord_443525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443557 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_443557 : Nat := 118140960795 + 443557 * 2 ^ 59
def prefixEnd_443557 : Nat := 4983230072969 + 3 ^ 40 * 443557 * 2
def baseEnd_443557 : Nat := 151838625777617543265083

theorem tailTrace_443557 : CollatzResearch.WordTrace tailWord_443557 prefixEnd_443557 151838625777617543265083 := by
  unfold tailWord_443557
  simp only [CollatzResearch.WordTrace]
  refine ⟨16177852854076217349664925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10785235236050811566443283 16177852854076217349664925)
  ·
    refine ⟨6066694820278581506124347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16177852854076217349664925 6066694820278581506124347)
    ·
      refine ⟨9100042230417872259186521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6066694820278581506124347 9100042230417872259186521)
      ·
        refine ⟨6825031672813404194389891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9100042230417872259186521 6825031672813404194389891)
        ·
          refine ⟨10237547509220106291584837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6825031672813404194389891 10237547509220106291584837)
          ·
            refine ⟨1919540157978769929672157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10237547509220106291584837 1919540157978769929672157)
            ·
              refine ⟨719827559242038723627059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919540157978769929672157 719827559242038723627059)
              ·
                refine ⟨1079741338863058085440589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719827559242038723627059 1079741338863058085440589)
                ·
                  refine ⟨404903002073646782040221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079741338863058085440589 404903002073646782040221)
                  ·
                    refine ⟨151838625777617543265083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404903002073646782040221 151838625777617543265083)
                    ·
                      rfl

theorem cell22_443557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_443557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443557 prefixEnd_443557 := by exact prefixLift 443557
  have htrace : WordTrace (prefixWord ++ tailWord_443557) baseStart_443557 baseEnd_443557 := by
    simpa [prefixWord, tailWord_443557, baseEnd_443557] using wordTrace_append hprefix tailTrace_443557
  have hstable : (prefixWord ++ tailWord_443557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443557).length < 2 ^ (prefixWord ++ tailWord_443557).sum := by decide
  have hdescent : baseEnd_443557 < baseStart_443557 := by decide
  rcases family_descends (prefixWord ++ tailWord_443557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443608 : List Nat := [2, 1, 2, 2, 5, 2, 2, 2, 1, 3]
def baseStart_443608 : Nat := 118140960795 + 443608 * 2 ^ 59
def prefixEnd_443608 : Nat := 4983230072969 + 3 ^ 40 * 443608 * 2
def baseEnd_443608 : Nat := 151856084119870410239927

theorem tailTrace_443608 : CollatzResearch.WordTrace tailWord_443608 prefixEnd_443608 151856084119870410239927 := by
  unfold tailWord_443608
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089856488445726529885739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10786475317927635373180985 8089856488445726529885739)
  ·
    refine ⟨12134784732668589794828609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8089856488445726529885739 12134784732668589794828609)
    ·
      refine ⟨9101088549501442346121457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12134784732668589794828609 9101088549501442346121457)
      ·
        refine ⟨6825816412126081759591093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9101088549501442346121457 6825816412126081759591093)
        ·
          refine ⟨639920288636820164961665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6825816412126081759591093 639920288636820164961665)
          ·
            refine ⟨479940216477615123721249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639920288636820164961665 479940216477615123721249)
            ·
              refine ⟨359955162358211342790937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479940216477615123721249 359955162358211342790937)
              ·
                refine ⟨269966371768658507093203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359955162358211342790937 269966371768658507093203)
                ·
                  refine ⟨404949557652987760639805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269966371768658507093203 404949557652987760639805)
                  ·
                    refine ⟨151856084119870410239927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 404949557652987760639805 151856084119870410239927)
                    ·
                      rfl

theorem cell22_443608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_443608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443608 prefixEnd_443608 := by exact prefixLift 443608
  have htrace : WordTrace (prefixWord ++ tailWord_443608) baseStart_443608 baseEnd_443608 := by
    simpa [prefixWord, tailWord_443608, baseEnd_443608] using wordTrace_append hprefix tailTrace_443608
  have hstable : (prefixWord ++ tailWord_443608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443608).length < 2 ^ (prefixWord ++ tailWord_443608).sum := by decide
  have hdescent : baseEnd_443608 < baseStart_443608 := by decide
  rcases family_descends (prefixWord ++ tailWord_443608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443649 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 4]
def baseStart_443649 : Nat := 118140960795 + 443649 * 2 ^ 59
def prefixEnd_443649 : Nat := 4983230072969 + 3 ^ 40 * 443649 * 2
def baseEnd_443649 : Nat := 50623373085919989988267

theorem tailTrace_443649 : CollatzResearch.WordTrace tailWord_443649 prefixEnd_443649 50623373085919989988267 := by
  unfold tailWord_443649
  simp only [CollatzResearch.WordTrace]
  refine ⟨16181208369742917062014001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10787472246495278041342667 16181208369742917062014001)
  ·
    refine ⟨12135906277307187796510501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16181208369742917062014001 12135906277307187796510501)
    ·
      refine ⟨2275482426995097711845719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12135906277307187796510501 2275482426995097711845719)
      ·
        refine ⟨3413223640492646567768579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2275482426995097711845719 3413223640492646567768579)
        ·
          refine ⟨5119835460738969851652869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3413223640492646567768579 5119835460738969851652869)
          ·
            refine ⟨959969148888556847184913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5119835460738969851652869 959969148888556847184913)
            ·
              refine ⟨719976861666417635388685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959969148888556847184913 719976861666417635388685)
              ·
                refine ⟨269991323124906613270757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719976861666417635388685 269991323124906613270757)
                ·
                  refine ⟨50623373085919989988267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269991323124906613270757 50623373085919989988267)
                  ·
                    rfl

theorem cell22_443649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_443649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443649 prefixEnd_443649 := by exact prefixLift 443649
  have htrace : WordTrace (prefixWord ++ tailWord_443649) baseStart_443649 baseEnd_443649 := by
    simpa [prefixWord, tailWord_443649, baseEnd_443649] using wordTrace_append hprefix tailTrace_443649
  have hstable : (prefixWord ++ tailWord_443649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443649).length < 2 ^ (prefixWord ++ tailWord_443649).sum := by decide
  have hdescent : baseEnd_443649 < baseStart_443649 := by decide
  rcases family_descends (prefixWord ++ tailWord_443649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443660 : List Nat := [2, 2, 1, 2, 2, 4, 9]
def baseStart_443660 : Nat := 118140960795 + 443660 * 2 ^ 59
def prefixEnd_443660 : Nat := 4983230072969 + 3 ^ 40 * 443660 * 2
def baseEnd_443660 : Nat := 5624958695650355849621

theorem tailTrace_443660 : CollatzResearch.WordTrace tailWord_443660 prefixEnd_443660 5624958695650355849621 := by
  unfold tailWord_443660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090804786351532970332217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10787739715135377293776289 8090804786351532970332217)
  ·
    refine ⟨6068103589763649727749163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8090804786351532970332217 6068103589763649727749163)
    ·
      refine ⟨9102155384645474591623745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6068103589763649727749163 9102155384645474591623745)
      ·
        refine ⟨6826616538484105943717809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9102155384645474591623745 6826616538484105943717809)
        ·
          refine ⟨5119962403863079457788357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6826616538484105943717809 5119962403863079457788357)
          ·
            refine ⟨959992950724327398335317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5119962403863079457788357 959992950724327398335317)
            ·
              refine ⟨5624958695650355849621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 959992950724327398335317 5624958695650355849621)
              ·
                rfl

theorem cell22_443660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 9].length) (baseStart_443660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443660 prefixEnd_443660 := by exact prefixLift 443660
  have htrace : WordTrace (prefixWord ++ tailWord_443660) baseStart_443660 baseEnd_443660 := by
    simpa [prefixWord, tailWord_443660, baseEnd_443660] using wordTrace_append hprefix tailTrace_443660
  have hstable : (prefixWord ++ tailWord_443660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443660).length < 2 ^ (prefixWord ++ tailWord_443660).sum := by decide
  have hdescent : baseEnd_443660 < baseStart_443660 := by decide
  rcases family_descends (prefixWord ++ tailWord_443660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443666 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_443666 : Nat := 118140960795 + 443666 * 2 ^ 59
def prefixEnd_443666 : Nat := 4983230072969 + 3 ^ 40 * 443666 * 2
def baseEnd_443666 : Nat := 50625312901725864096583

theorem tailTrace_443666 : CollatzResearch.WordTrace tailWord_443666 prefixEnd_443666 50625312901725864096583 := by
  unfold tailWord_443666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4045457102670332241345713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10787885607120885976921901 4045457102670332241345713)
  ·
    refine ⟨3034092827002749181009285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4045457102670332241345713 3034092827002749181009285)
    ·
      refine ⟨568892405063015471439241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3034092827002749181009285 568892405063015471439241)
      ·
        refine ⟨426669303797261603579431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568892405063015471439241 426669303797261603579431)
        ·
          refine ⟨640003955695892405369147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426669303797261603579431 640003955695892405369147)
          ·
            refine ⟨960005933543838608053721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640003955695892405369147 960005933543838608053721)
            ·
              refine ⟨720004450157878956040291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 960005933543838608053721 720004450157878956040291)
              ·
                refine ⟨1080006675236818434060437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 720004450157878956040291 1080006675236818434060437)
                ·
                  refine ⟨50625312901725864096583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1080006675236818434060437 50625312901725864096583)
                  ·
                    rfl

theorem cell22_443666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_443666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443666 prefixEnd_443666 := by exact prefixLift 443666
  have htrace : WordTrace (prefixWord ++ tailWord_443666) baseStart_443666 baseEnd_443666 := by
    simpa [prefixWord, tailWord_443666, baseEnd_443666] using wordTrace_append hprefix tailTrace_443666
  have hstable : (prefixWord ++ tailWord_443666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443666).length < 2 ^ (prefixWord ++ tailWord_443666).sum := by decide
  have hdescent : baseEnd_443666 < baseStart_443666 := by decide
  rcases family_descends (prefixWord ++ tailWord_443666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443777 : List Nat := [1, 2, 4, 3, 3, 1, 2, 2, 1, 3]
def baseStart_443777 : Nat := 118140960795 + 443777 * 2 ^ 59
def prefixEnd_443777 : Nat := 4983230072969 + 3 ^ 40 * 443777 * 2
def baseEnd_443777 : Nat := 151913936273610302764409

theorem tailTrace_443777 : CollatzResearch.WordTrace tailWord_443777 prefixEnd_443777 151913936273610302764409 := by
  unfold tailWord_443777
  simp only [CollatzResearch.WordTrace]
  refine ⟨16185876913279194922673585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10790584608852796615115723 16185876913279194922673585)
  ·
    refine ⟨12139407684959396192005189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16185876913279194922673585 12139407684959396192005189)
    ·
      refine ⟨2276138940929886786000973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12139407684959396192005189 2276138940929886786000973)
      ·
        refine ⟨853552102848707544750365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2276138940929886786000973 853552102848707544750365)
        ·
          refine ⟨320082038568265329281387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853552102848707544750365 320082038568265329281387)
          ·
            refine ⟨480123057852397993922081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320082038568265329281387 480123057852397993922081)
            ·
              refine ⟨360092293389298495441561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480123057852397993922081 360092293389298495441561)
              ·
                refine ⟨270069220041973871581171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360092293389298495441561 270069220041973871581171)
                ·
                  refine ⟨405103830062960807371757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270069220041973871581171 405103830062960807371757)
                  ·
                    refine ⟨151913936273610302764409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405103830062960807371757 151913936273610302764409)
                    ·
                      rfl

theorem cell22_443777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_443777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443777 prefixEnd_443777 := by exact prefixLift 443777
  have htrace : WordTrace (prefixWord ++ tailWord_443777) baseStart_443777 baseEnd_443777 := by
    simpa [prefixWord, tailWord_443777, baseEnd_443777] using wordTrace_append hprefix tailTrace_443777
  have hstable : (prefixWord ++ tailWord_443777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443777).length < 2 ^ (prefixWord ++ tailWord_443777).sum := by decide
  have hdescent : baseEnd_443777 < baseStart_443777 := by decide
  rcases family_descends (prefixWord ++ tailWord_443777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443797 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_443797 : Nat := 118140960795 + 443797 * 2 ^ 59
def prefixEnd_443797 : Nat := 4983230072969 + 3 ^ 40 * 443797 * 2
def baseEnd_443797 : Nat := 151920782682336917264347

theorem tailTrace_443797 : CollatzResearch.WordTrace tailWord_443797 prefixEnd_443797 151920782682336917264347 := by
  unfold tailWord_443797
  simp only [CollatzResearch.WordTrace]
  refine ⟨16186606373206738338401645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10791070915471158892267763 16186606373206738338401645)
  ·
    refine ⟨6069977389952526876900617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16186606373206738338401645 6069977389952526876900617)
    ·
      refine ⟨4552483042464395157675463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6069977389952526876900617 4552483042464395157675463)
      ·
        refine ⟨6828724563696592736513195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4552483042464395157675463 6828724563696592736513195)
        ·
          refine ⟨10243086845544889104769793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6828724563696592736513195 10243086845544889104769793)
          ·
            refine ⟨7682315134158666828577345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10243086845544889104769793 7682315134158666828577345)
            ·
              refine ⟨5761736350619000121433009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7682315134158666828577345 5761736350619000121433009)
              ·
                refine ⟨4321302262964250091074757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5761736350619000121433009 4321302262964250091074757)
                ·
                  refine ⟨810244174305796892076517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4321302262964250091074757 810244174305796892076517)
                  ·
                    refine ⟨151920782682336917264347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 810244174305796892076517 151920782682336917264347)
                    ·
                      rfl

theorem cell22_443797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_443797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443797 prefixEnd_443797 := by exact prefixLift 443797
  have htrace : WordTrace (prefixWord ++ tailWord_443797) baseStart_443797 baseEnd_443797 := by
    simpa [prefixWord, tailWord_443797, baseEnd_443797] using wordTrace_append hprefix tailTrace_443797
  have hstable : (prefixWord ++ tailWord_443797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443797).length < 2 ^ (prefixWord ++ tailWord_443797).sum := by decide
  have hdescent : baseEnd_443797 < baseStart_443797 := by decide
  rcases family_descends (prefixWord ++ tailWord_443797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443833 : List Nat := [1, 2, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_443833 : Nat := 118140960795 + 443833 * 2 ^ 59
def prefixEnd_443833 : Nat := 4983230072969 + 3 ^ 40 * 443833 * 2
def baseEnd_443833 : Nat := 151933106218044823364237

theorem tailTrace_443833 : CollatzResearch.WordTrace tailWord_443833 prefixEnd_443833 151933106218044823364237 := by
  unfold tailWord_443833
  simp only [CollatzResearch.WordTrace]
  refine ⟨16187919401076316486712153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10791946267384210991141435 16187919401076316486712153)
  ·
    refine ⟨12140939550807237365034115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16187919401076316486712153 12140939550807237365034115)
    ·
      refine ⟨18211409326210856047551173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12140939550807237365034115 18211409326210856047551173)
      ·
        refine ⟨3414639248664535508915845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18211409326210856047551173 3414639248664535508915845)
        ·
          refine ⟨640244859124600407921721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3414639248664535508915845 640244859124600407921721)
          ·
            refine ⟨480183644343450305941291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640244859124600407921721 480183644343450305941291)
            ·
              refine ⟨720275466515175458911937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480183644343450305941291 720275466515175458911937)
              ·
                refine ⟨540206599886381594183953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 720275466515175458911937 540206599886381594183953)
                ·
                  refine ⟨405154949914786195637965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540206599886381594183953 405154949914786195637965)
                  ·
                    refine ⟨151933106218044823364237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405154949914786195637965 151933106218044823364237)
                    ·
                      rfl

theorem cell22_443833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_443833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443833 prefixEnd_443833 := by exact prefixLift 443833
  have htrace : WordTrace (prefixWord ++ tailWord_443833) baseStart_443833 baseEnd_443833 := by
    simpa [prefixWord, tailWord_443833, baseEnd_443833] using wordTrace_append hprefix tailTrace_443833
  have hstable : (prefixWord ++ tailWord_443833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443833).length < 2 ^ (prefixWord ++ tailWord_443833).sum := by decide
  have hdescent : baseEnd_443833 < baseStart_443833 := by decide
  rcases family_descends (prefixWord ++ tailWord_443833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_443872 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 4, 5]
def baseStart_443872 : Nat := 118140960795 + 443872 * 2 ^ 59
def prefixEnd_443872 : Nat := 4983230072969 + 3 ^ 40 * 443872 * 2
def baseEnd_443872 : Nat := 151946456715061721639117

theorem tailTrace_443872 : CollatzResearch.WordTrace tailWord_443872 prefixEnd_443872 151946456715061721639117 := by
  unfold tailWord_443872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094670923967513073690935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10792894565290017431587913 8094670923967513073690935)
  ·
    refine ⟨12142006385951269610536403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8094670923967513073690935 12142006385951269610536403)
    ·
      refine ⟨18213009578926904415804605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12142006385951269610536403 18213009578926904415804605)
      ·
        refine ⟨6829878592097589155926727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18213009578926904415804605 6829878592097589155926727)
        ·
          refine ⟨10244817888146383733890091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6829878592097589155926727 10244817888146383733890091)
          ·
            refine ⟨15367226832219575600835137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10244817888146383733890091 15367226832219575600835137)
            ·
              refine ⟨11525420124164681700626353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15367226832219575600835137 11525420124164681700626353)
              ·
                refine ⟨8644065093123511275469765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11525420124164681700626353 8644065093123511275469765)
                ·
                  refine ⟨1620762204960658364150581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8644065093123511275469765 1620762204960658364150581)
                  ·
                    refine ⟨151946456715061721639117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1620762204960658364150581 151946456715061721639117)
                    ·
                      rfl

theorem cell22_443872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_443872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_443872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_443872 prefixEnd_443872 := by exact prefixLift 443872
  have htrace : WordTrace (prefixWord ++ tailWord_443872) baseStart_443872 baseEnd_443872 := by
    simpa [prefixWord, tailWord_443872, baseEnd_443872] using wordTrace_append hprefix tailTrace_443872
  have hstable : (prefixWord ++ tailWord_443872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_443872).length < 2 ^ (prefixWord ++ tailWord_443872).sum := by decide
  have hdescent : baseEnd_443872 < baseStart_443872 := by decide
  rcases family_descends (prefixWord ++ tailWord_443872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444116 : List Nat := [2, 4, 1, 3, 1, 11]
def baseStart_444116 : Nat := 118140960795 + 444116 * 2 ^ 59
def prefixEnd_444116 : Nat := 4983230072969 + 3 ^ 40 * 444116 * 2
def baseEnd_444116 : Nat := 1876913369154647142449

theorem tailTrace_444116 : CollatzResearch.WordTrace tailWord_444116 prefixEnd_444116 1876913369154647142449 := by
  unfold tailWord_444116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099120629525527909632101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10798827506034037212842801 8099120629525527909632101)
  ·
    refine ⟨1518585118036036483056019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8099120629525527909632101 1518585118036036483056019)
    ·
      refine ⟨2277877677054054724584029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518585118036036483056019 2277877677054054724584029)
      ·
        refine ⟨854204128895270521719011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2277877677054054724584029 854204128895270521719011)
        ·
          refine ⟨1281306193342905782578517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854204128895270521719011 1281306193342905782578517)
          ·
            refine ⟨1876913369154647142449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1281306193342905782578517 1876913369154647142449)
            ·
              rfl

theorem cell22_444116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 11].length) (baseStart_444116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444116 prefixEnd_444116 := by exact prefixLift 444116
  have htrace : WordTrace (prefixWord ++ tailWord_444116) baseStart_444116 baseEnd_444116 := by
    simpa [prefixWord, tailWord_444116, baseEnd_444116] using wordTrace_append hprefix tailTrace_444116
  have hstable : (prefixWord ++ tailWord_444116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444116).length < 2 ^ (prefixWord ++ tailWord_444116).sum := by decide
  have hdescent : baseEnd_444116 < baseStart_444116 := by decide
  rcases family_descends (prefixWord ++ tailWord_444116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444146 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_444146 : Nat := 118140960795 + 444146 * 2 ^ 59
def prefixEnd_444146 : Nat := 4983230072969 + 3 ^ 40 * 444146 * 2
def baseEnd_444146 : Nat := 152040252514616340288277

theorem tailTrace_444146 : CollatzResearch.WordTrace tailWord_444146 prefixEnd_444146 152040252514616340288277 := by
  unfold tailWord_444146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049833862235592735714073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10799556965961580628570861 4049833862235592735714073)
  ·
    refine ⟨3037375396676694551785555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4049833862235592735714073 3037375396676694551785555)
    ·
      refine ⟨4556063095015041827678333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037375396676694551785555 4556063095015041827678333)
      ·
        refine ⟨1708523660630640685379375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4556063095015041827678333 1708523660630640685379375)
        ·
          refine ⟨2562785490945961028069063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1708523660630640685379375 2562785490945961028069063)
          ·
            refine ⟨3844178236418941542103595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2562785490945961028069063 3844178236418941542103595)
            ·
              refine ⟨5766267354628412313155393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844178236418941542103595 5766267354628412313155393)
              ·
                refine ⟨4324700515971309234866545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766267354628412313155393 4324700515971309234866545)
                ·
                  refine ⟨3243525386978481926149909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4324700515971309234866545 3243525386978481926149909)
                  ·
                    refine ⟨152040252514616340288277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3243525386978481926149909 152040252514616340288277)
                    ·
                      rfl

theorem cell22_444146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_444146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444146 prefixEnd_444146 := by exact prefixLift 444146
  have htrace : WordTrace (prefixWord ++ tailWord_444146) baseStart_444146 baseEnd_444146 := by
    simpa [prefixWord, tailWord_444146, baseEnd_444146] using wordTrace_append hprefix tailTrace_444146
  have hstable : (prefixWord ++ tailWord_444146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444146).length < 2 ^ (prefixWord ++ tailWord_444146).sum := by decide
  have hdescent : baseEnd_444146 < baseStart_444146 := by decide
  rcases family_descends (prefixWord ++ tailWord_444146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444255 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 2, 3]
def baseStart_444255 : Nat := 118140960795 + 444255 * 2 ^ 59
def prefixEnd_444255 : Nat := 4983230072969 + 3 ^ 40 * 444255 * 2
def baseEnd_444255 : Nat := 152077565442176389312943

theorem tailTrace_444255 : CollatzResearch.WordTrace tailWord_444255 prefixEnd_444255 152077565442176389312943 := by
  unfold tailWord_444255
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203311005547482558574219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10802207337031655039049479 16203311005547482558574219)
  ·
    refine ⟨24304966508321223837861329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16203311005547482558574219 24304966508321223837861329)
    ·
      refine ⟨18228724881240917878395997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24304966508321223837861329 18228724881240917878395997)
      ·
        refine ⟨6835771830465344204398499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18228724881240917878395997 6835771830465344204398499)
        ·
          refine ⟨10253657745698016306597749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835771830465344204398499 10253657745698016306597749)
          ·
            refine ⟨961280413659189028743539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10253657745698016306597749 961280413659189028743539)
            ·
              refine ⟨1441920620488783543115309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961280413659189028743539 1441920620488783543115309)
              ·
                refine ⟨540720232683293828668241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1441920620488783543115309 540720232683293828668241)
                ·
                  refine ⟨405540174512470371501181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540720232683293828668241 405540174512470371501181)
                  ·
                    refine ⟨152077565442176389312943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405540174512470371501181 152077565442176389312943)
                    ·
                      rfl

theorem cell22_444255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_444255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444255 prefixEnd_444255 := by exact prefixLift 444255
  have htrace : WordTrace (prefixWord ++ tailWord_444255) baseStart_444255 baseEnd_444255 := by
    simpa [prefixWord, tailWord_444255, baseEnd_444255] using wordTrace_append hprefix tailTrace_444255
  have hstable : (prefixWord ++ tailWord_444255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444255).length < 2 ^ (prefixWord ++ tailWord_444255).sum := by decide
  have hdescent : baseEnd_444255 < baseStart_444255 := by decide
  rcases family_descends (prefixWord ++ tailWord_444255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444270 : List Nat := [4, 1, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_444270 : Nat := 118140960795 + 444270 * 2 ^ 59
def prefixEnd_444270 : Nat := 4983230072969 + 3 ^ 40 * 444270 * 2
def baseEnd_444270 : Nat := 152082700248721350187897

theorem tailTrace_444270 : CollatzResearch.WordTrace tailWord_444270 prefixEnd_444270 152082700248721350187897 := by
  unfold tailWord_444270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025482262561642515046283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10802572066995426746913509 2025482262561642515046283)
  ·
    refine ⟨3038223393842463772569425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025482262561642515046283 3038223393842463772569425)
    ·
      refine ⟨2278667545381847829427069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3038223393842463772569425 2278667545381847829427069)
      ·
        refine ⟨854500329518192936035151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2278667545381847829427069 854500329518192936035151)
        ·
          refine ⟨1281750494277289404052727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854500329518192936035151 1281750494277289404052727)
          ·
            refine ⟨1922625741415934106079091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1281750494277289404052727 1922625741415934106079091)
            ·
              refine ⟨2883938612123901159118637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1922625741415934106079091 2883938612123901159118637)
              ·
                refine ⟨1081476979546462934669489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2883938612123901159118637 1081476979546462934669489)
                ·
                  refine ⟨811107734659847201002117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1081476979546462934669489 811107734659847201002117)
                  ·
                    refine ⟨152082700248721350187897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811107734659847201002117 152082700248721350187897)
                    ·
                      rfl

theorem cell22_444270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_444270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444270 prefixEnd_444270 := by exact prefixLift 444270
  have htrace : WordTrace (prefixWord ++ tailWord_444270) baseStart_444270 baseEnd_444270 := by
    simpa [prefixWord, tailWord_444270, baseEnd_444270] using wordTrace_append hprefix tailTrace_444270
  have hstable : (prefixWord ++ tailWord_444270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444270).length < 2 ^ (prefixWord ++ tailWord_444270).sum := by decide
  have hdescent : baseEnd_444270 < baseStart_444270 := by decide
  rcases family_descends (prefixWord ++ tailWord_444270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444289 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_444289 : Nat := 118140960795 + 444289 * 2 ^ 59
def prefixEnd_444289 : Nat := 4983230072969 + 3 ^ 40 * 444289 * 2
def baseEnd_444289 : Nat := 152089204337011633962839

theorem tailTrace_444289 : CollatzResearch.WordTrace tailWord_444289 prefixEnd_444289 152089204337011633962839 := by
  unfold tailWord_444289
  simp only [CollatzResearch.WordTrace]
  refine ⟨16204551087424306365311921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10803034058282870910207947 16204551087424306365311921)
  ·
    refine ⟨12153413315568229773983941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16204551087424306365311921 12153413315568229773983941)
    ·
      refine ⟨2278764996669043082621989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12153413315568229773983941 2278764996669043082621989)
      ·
        refine ⟨427268436875445577991623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2278764996669043082621989 427268436875445577991623)
        ·
          refine ⟨640902655313168366987435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427268436875445577991623 640902655313168366987435)
          ·
            refine ⟨961353982969752550481153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640902655313168366987435 961353982969752550481153)
            ·
              refine ⟨721015487227314412860865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961353982969752550481153 721015487227314412860865)
              ·
                refine ⟨540761615420485809645649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721015487227314412860865 540761615420485809645649)
                ·
                  refine ⟨405571211565364357234237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 540761615420485809645649 405571211565364357234237)
                  ·
                    refine ⟨152089204337011633962839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405571211565364357234237 152089204337011633962839)
                    ·
                      rfl

theorem cell22_444289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_444289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444289 prefixEnd_444289 := by exact prefixLift 444289
  have htrace : WordTrace (prefixWord ++ tailWord_444289) baseStart_444289 baseEnd_444289 := by
    simpa [prefixWord, tailWord_444289, baseEnd_444289] using wordTrace_append hprefix tailTrace_444289
  have hstable : (prefixWord ++ tailWord_444289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444289).length < 2 ^ (prefixWord ++ tailWord_444289).sum := by decide
  have hdescent : baseEnd_444289 < baseStart_444289 := by decide
  rcases family_descends (prefixWord ++ tailWord_444289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444302 : List Nat := [4, 1, 1, 5, 1, 2, 1, 7]
def baseStart_444302 : Nat := 118140960795 + 444302 * 2 ^ 59
def prefixEnd_444302 : Nat := 4983230072969 + 3 ^ 40 * 444302 * 2
def baseEnd_444302 : Nat := 16899294944742659265311

theorem tailTrace_444302 : CollatzResearch.WordTrace tailWord_444302 prefixEnd_444302 16899294944742659265311 := by
  unfold tailWord_444302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025628154547151198191895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10803350157584806390356773 2025628154547151198191895)
  ·
    refine ⟨3038442231820726797287843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025628154547151198191895 3038442231820726797287843)
    ·
      refine ⟨4557663347731090195931765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038442231820726797287843 4557663347731090195931765)
      ·
        refine ⟨427280938849789705868603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4557663347731090195931765 427280938849789705868603)
        ·
          refine ⟨640921408274684558802905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427280938849789705868603 640921408274684558802905)
          ·
            refine ⟨480691056206013419102179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640921408274684558802905 480691056206013419102179)
            ·
              refine ⟨721036584309020128653269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480691056206013419102179 721036584309020128653269)
              ·
                refine ⟨16899294944742659265311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 721036584309020128653269 16899294944742659265311)
                ·
                  rfl

theorem cell22_444302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_444302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444302 prefixEnd_444302 := by exact prefixLift 444302
  have htrace : WordTrace (prefixWord ++ tailWord_444302) baseStart_444302 baseEnd_444302 := by
    simpa [prefixWord, tailWord_444302, baseEnd_444302] using wordTrace_append hprefix tailTrace_444302
  have hstable : (prefixWord ++ tailWord_444302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444302).length < 2 ^ (prefixWord ++ tailWord_444302).sum := by decide
  have hdescent : baseEnd_444302 < baseStart_444302 := by decide
  rcases family_descends (prefixWord ++ tailWord_444302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444313 : List Nat := [1, 2, 1, 2, 1, 3, 4, 3, 5]
def baseStart_444313 : Nat := 118140960795 + 444313 * 2 ^ 59
def prefixEnd_444313 : Nat := 4983230072969 + 3 ^ 40 * 444313 * 2
def baseEnd_444313 : Nat := 50699140009161190454255

theorem tailTrace_444313 : CollatzResearch.WordTrace tailWord_444313 prefixEnd_444313 50699140009161190454255 := by
  unfold tailWord_444313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205426439337358464185593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10803617626224905642790395 16205426439337358464185593)
  ·
    refine ⟨12154069829503018848139195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16205426439337358464185593 12154069829503018848139195)
    ·
      refine ⟨18231104744254528272208793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12154069829503018848139195 18231104744254528272208793)
      ·
        refine ⟨13673328558190896204156595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18231104744254528272208793 13673328558190896204156595)
        ·
          refine ⟨20509992837286344306234893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13673328558190896204156595 20509992837286344306234893)
          ·
            refine ⟨7691247313982379114838085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20509992837286344306234893 7691247313982379114838085)
            ·
              refine ⟨1442108871371696084032141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7691247313982379114838085 1442108871371696084032141)
              ·
                refine ⟨540790826764386031512053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442108871371696084032141 540790826764386031512053)
                ·
                  refine ⟨50699140009161190454255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540790826764386031512053 50699140009161190454255)
                  ·
                    rfl

theorem cell22_444313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_444313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444313 prefixEnd_444313 := by exact prefixLift 444313
  have htrace : WordTrace (prefixWord ++ tailWord_444313) baseStart_444313 baseEnd_444313 := by
    simpa [prefixWord, tailWord_444313, baseEnd_444313] using wordTrace_append hprefix tailTrace_444313
  have hstable : (prefixWord ++ tailWord_444313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444313).length < 2 ^ (prefixWord ++ tailWord_444313).sum := by decide
  have hdescent : baseEnd_444313 < baseStart_444313 := by decide
  rcases family_descends (prefixWord ++ tailWord_444313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444377 : List Nat := [1, 2, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_444377 : Nat := 118140960795 + 444377 * 2 ^ 59
def prefixEnd_444377 : Nat := 4983230072969 + 3 ^ 40 * 444377 * 2
def baseEnd_444377 : Nat := 152119328535408737762569

theorem tailTrace_444377 : CollatzResearch.WordTrace tailWord_444377 prefixEnd_444377 152119328535408737762569 := by
  unfold tailWord_444377
  simp only [CollatzResearch.WordTrace]
  refine ⟨16207760711105497394515385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10805173807403664929676923 16207760711105497394515385)
  ·
    refine ⟨12155820533329123045886539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16207760711105497394515385 12155820533329123045886539)
    ·
      refine ⟨18233730799993684568829809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12155820533329123045886539 18233730799993684568829809)
      ·
        refine ⟨13675298099995263426622357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18233730799993684568829809 13675298099995263426622357)
        ·
          refine ⟨641029598437277973122923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13675298099995263426622357 641029598437277973122923)
          ·
            refine ⟨961544397655916959684385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641029598437277973122923 961544397655916959684385)
            ·
              refine ⟨721158298241937719763289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961544397655916959684385 721158298241937719763289)
              ·
                refine ⟨540868723681453289822467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721158298241937719763289 540868723681453289822467)
                ·
                  refine ⟨811303085522179934733701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540868723681453289822467 811303085522179934733701)
                  ·
                    refine ⟨152119328535408737762569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811303085522179934733701 152119328535408737762569)
                    ·
                      rfl

theorem cell22_444377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_444377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444377 prefixEnd_444377 := by exact prefixLift 444377
  have htrace : WordTrace (prefixWord ++ tailWord_444377) baseStart_444377 baseEnd_444377 := by
    simpa [prefixWord, tailWord_444377, baseEnd_444377] using wordTrace_append hprefix tailTrace_444377
  have hstable : (prefixWord ++ tailWord_444377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444377).length < 2 ^ (prefixWord ++ tailWord_444377).sum := by decide
  have hdescent : baseEnd_444377 < baseStart_444377 := by decide
  rcases family_descends (prefixWord ++ tailWord_444377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444388 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 1, 6]
def baseStart_444388 : Nat := 118140960795 + 444388 * 2 ^ 59
def prefixEnd_444388 : Nat := 4983230072969 + 3 ^ 40 * 444388 * 2
def baseEnd_444388 : Nat := 152123094060208375737535

theorem tailTrace_444388 : CollatzResearch.WordTrace tailWord_444388 prefixEnd_444388 152123094060208375737535 := by
  unfold tailWord_444388
  simp only [CollatzResearch.WordTrace]
  refine ⟨8104080957032823136582909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10805441276043764182110545 8104080957032823136582909)
  ·
    refine ⟨3039030358887308676218591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8104080957032823136582909 3039030358887308676218591)
    ·
      refine ⟨4558545538330963014327887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3039030358887308676218591 4558545538330963014327887)
      ·
        refine ⟨6837818307496444521491831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4558545538330963014327887 6837818307496444521491831)
        ·
          refine ⟨10256727461244666782237747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6837818307496444521491831 10256727461244666782237747)
          ·
            refine ⟨15385091191867000173356621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10256727461244666782237747 15385091191867000173356621)
            ·
              refine ⟨5769409196950125065008733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15385091191867000173356621 5769409196950125065008733)
              ·
                refine ⟨2163528448856296899378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5769409196950125065008733 2163528448856296899378275)
                ·
                  refine ⟨3245292673284445349067413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2163528448856296899378275 3245292673284445349067413)
                  ·
                    refine ⟨152123094060208375737535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3245292673284445349067413 152123094060208375737535)
                    ·
                      rfl

theorem cell22_444388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_444388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444388 prefixEnd_444388 := by exact prefixLift 444388
  have htrace : WordTrace (prefixWord ++ tailWord_444388) baseStart_444388 baseEnd_444388 := by
    simpa [prefixWord, tailWord_444388, baseEnd_444388] using wordTrace_append hprefix tailTrace_444388
  have hstable : (prefixWord ++ tailWord_444388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444388).length < 2 ^ (prefixWord ++ tailWord_444388).sum := by decide
  have hdescent : baseEnd_444388 < baseStart_444388 := by decide
  rcases family_descends (prefixWord ++ tailWord_444388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444435 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 3, 3]
def baseStart_444435 : Nat := 118140960795 + 444435 * 2 ^ 59
def prefixEnd_444435 : Nat := 4983230072969 + 3 ^ 40 * 444435 * 2
def baseEnd_444435 : Nat := 152139183120715919812391

theorem tailTrace_444435 : CollatzResearch.WordTrace tailWord_444435 prefixEnd_444435 152139183120715919812391 := by
  unfold tailWord_444435
  simp only [CollatzResearch.WordTrace]
  refine ⟨16209876144895373300126759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10806584096596915533417839 16209876144895373300126759)
  ·
    refine ⟨24314814217343059950190139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16209876144895373300126759 24314814217343059950190139)
    ·
      refine ⟨36472221326014589925285209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24314814217343059950190139 36472221326014589925285209)
      ·
        refine ⟨27354165994510942443963907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36472221326014589925285209 27354165994510942443963907)
        ·
          refine ⟨41031248991766413665945861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27354165994510942443963907 41031248991766413665945861)
          ·
            refine ⟨7693359185956202562364849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41031248991766413665945861 7693359185956202562364849)
            ·
              refine ⟨5770019389467151921773637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7693359185956202562364849 5770019389467151921773637)
              ·
                refine ⟨1081878635525090985332557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5770019389467151921773637 1081878635525090985332557)
                ·
                  refine ⟨405704488321909119499709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081878635525090985332557 405704488321909119499709)
                  ·
                    refine ⟨152139183120715919812391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405704488321909119499709 152139183120715919812391)
                    ·
                      rfl

theorem cell22_444435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3].length) (baseStart_444435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444435 prefixEnd_444435 := by exact prefixLift 444435
  have htrace : WordTrace (prefixWord ++ tailWord_444435) baseStart_444435 baseEnd_444435 := by
    simpa [prefixWord, tailWord_444435, baseEnd_444435] using wordTrace_append hprefix tailTrace_444435
  have hstable : (prefixWord ++ tailWord_444435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444435).length < 2 ^ (prefixWord ++ tailWord_444435).sum := by decide
  have hdescent : baseEnd_444435 < baseStart_444435 := by decide
  rcases family_descends (prefixWord ++ tailWord_444435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444465 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 5]
def baseStart_444465 : Nat := 118140960795 + 444465 * 2 ^ 59
def prefixEnd_444465 : Nat := 4983230072969 + 3 ^ 40 * 444465 * 2
def baseEnd_444465 : Nat := 50716484244601947187433

theorem tailTrace_444465 : CollatzResearch.WordTrace tailWord_444465 prefixEnd_444465 50716484244601947187433 := by
  unfold tailWord_444465
  simp only [CollatzResearch.WordTrace]
  refine ⟨16210970334786688423718849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10807313556524458949145899 16210970334786688423718849)
  ·
    refine ⟨12158227751090016317789137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16210970334786688423718849 12158227751090016317789137)
    ·
      refine ⟨9118670813317512238341853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12158227751090016317789137 9118670813317512238341853)
      ·
        refine ⟨3419501554994067089378195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9118670813317512238341853 3419501554994067089378195)
        ·
          refine ⟨5129252332491100634067293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419501554994067089378195 5129252332491100634067293)
          ·
            refine ⟨1923469624684162737775235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5129252332491100634067293 1923469624684162737775235)
            ·
              refine ⟨2885204437026244106662853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923469624684162737775235 2885204437026244106662853)
              ·
                refine ⟨540975831942420769999285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2885204437026244106662853 540975831942420769999285)
                ·
                  refine ⟨50716484244601947187433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 540975831942420769999285 50716484244601947187433)
                  ·
                    rfl

theorem cell22_444465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_444465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444465 prefixEnd_444465 := by exact prefixLift 444465
  have htrace : WordTrace (prefixWord ++ tailWord_444465) baseStart_444465 baseEnd_444465 := by
    simpa [prefixWord, tailWord_444465, baseEnd_444465] using wordTrace_append hprefix tailTrace_444465
  have hstable : (prefixWord ++ tailWord_444465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444465).length < 2 ^ (prefixWord ++ tailWord_444465).sum := by decide
  have hdescent : baseEnd_444465 < baseStart_444465 := by decide
  rcases family_descends (prefixWord ++ tailWord_444465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444480 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_444480 : Nat := 118140960795 + 444480 * 2 ^ 59
def prefixEnd_444480 : Nat := 4983230072969 + 3 ^ 40 * 444480 * 2
def baseEnd_444480 : Nat := 152154587540350802437253

theorem tailTrace_444480 : CollatzResearch.WordTrace tailWord_444480 prefixEnd_444480 152154587540350802437253 := by
  unfold tailWord_444480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105758714866172992757447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10807678286488230657009929 8105758714866172992757447)
  ·
    refine ⟨12158638072299259489136171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8105758714866172992757447 12158638072299259489136171)
    ·
      refine ⟨18237957108448889233704257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12158638072299259489136171 18237957108448889233704257)
      ·
        refine ⟨13678467831336666925278193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18237957108448889233704257 13678467831336666925278193)
        ·
          refine ⟨10258850873502500193958645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13678467831336666925278193 10258850873502500193958645)
          ·
            refine ⟨961767269390859393183623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10258850873502500193958645 961767269390859393183623)
            ·
              refine ⟨1442650904086289089775435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961767269390859393183623 1442650904086289089775435)
              ·
                refine ⟨2163976356129433634663153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1442650904086289089775435 2163976356129433634663153)
                ·
                  refine ⟨1622982267097075225997365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2163976356129433634663153 1622982267097075225997365)
                  ·
                    refine ⟨152154587540350802437253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1622982267097075225997365 152154587540350802437253)
                    ·
                      rfl

theorem cell22_444480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_444480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444480 prefixEnd_444480 := by exact prefixLift 444480
  have htrace : WordTrace (prefixWord ++ tailWord_444480) baseStart_444480 baseEnd_444480 := by
    simpa [prefixWord, tailWord_444480, baseEnd_444480] using wordTrace_append hprefix tailTrace_444480
  have hstable : (prefixWord ++ tailWord_444480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444480).length < 2 ^ (prefixWord ++ tailWord_444480).sum := by decide
  have hdescent : baseEnd_444480 < baseStart_444480 := by decide
  rcases family_descends (prefixWord ++ tailWord_444480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444512 : List Nat := [2, 1, 1, 3, 2, 4, 1, 3, 1, 4]
def baseStart_444512 : Nat := 118140960795 + 444512 * 2 ^ 59
def prefixEnd_444512 : Nat := 4983230072969 + 3 ^ 40 * 444512 * 2
def baseEnd_444512 : Nat := 152165541794313385637155

theorem tailTrace_444512 : CollatzResearch.WordTrace tailWord_444512 prefixEnd_444512 152165541794313385637155 := by
  unfold tailWord_444512
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106342282808207725339895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10808456377077610300453193 8106342282808207725339895)
  ·
    refine ⟨12159513424212311588009843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8106342282808207725339895 12159513424212311588009843)
    ·
      refine ⟨18239270136318467382014765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12159513424212311588009843 18239270136318467382014765)
      ·
        refine ⟨6839726301119425268255537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18239270136318467382014765 6839726301119425268255537)
        ·
          refine ⟨5129794725839568951191653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6839726301119425268255537 5129794725839568951191653)
          ·
            refine ⟨961836511094919178348435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5129794725839568951191653 961836511094919178348435)
            ·
              refine ⟨1442754766642378767522653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961836511094919178348435 1442754766642378767522653)
              ·
                refine ⟨541033037490892037820995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442754766642378767522653 541033037490892037820995)
                ·
                  refine ⟨811549556236338056731493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541033037490892037820995 811549556236338056731493)
                  ·
                    refine ⟨152165541794313385637155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811549556236338056731493 152165541794313385637155)
                    ·
                      rfl

theorem cell22_444512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_444512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444512 prefixEnd_444512 := by exact prefixLift 444512
  have htrace : WordTrace (prefixWord ++ tailWord_444512) baseStart_444512 baseEnd_444512 := by
    simpa [prefixWord, tailWord_444512, baseEnd_444512] using wordTrace_append hprefix tailTrace_444512
  have hstable : (prefixWord ++ tailWord_444512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444512).length < 2 ^ (prefixWord ++ tailWord_444512).sum := by decide
  have hdescent : baseEnd_444512 < baseStart_444512 := by decide
  rcases family_descends (prefixWord ++ tailWord_444512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444527 : List Nat := [1, 1, 2, 1, 3, 4, 2, 4, 4]
def baseStart_444527 : Nat := 118140960795 + 444527 * 2 ^ 59
def prefixEnd_444527 : Nat := 4983230072969 + 3 ^ 40 * 444527 * 2
def baseEnd_444527 : Nat := 50723558866952782170703

theorem tailTrace_444527 : CollatzResearch.WordTrace tailWord_444527 prefixEnd_444527 50723558866952782170703 := by
  unfold tailWord_444527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16213231660562073012475835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10808821107041382008317223 16213231660562073012475835)
  ·
    refine ⟨24319847490843109518713753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16213231660562073012475835 24319847490843109518713753)
    ·
      refine ⟨18239885618132332139035315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24319847490843109518713753 18239885618132332139035315)
      ·
        refine ⟨27359828427198498208552973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18239885618132332139035315 27359828427198498208552973)
        ·
          refine ⟨10259935660199436828207365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27359828427198498208552973 10259935660199436828207365)
          ·
            refine ⟨1923737936287394405288881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10259935660199436828207365 1923737936287394405288881)
            ·
              refine ⟨1442803452215545803966661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1923737936287394405288881 1442803452215545803966661)
              ·
                refine ⟨270525647290414838243749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1442803452215545803966661 270525647290414838243749)
                ·
                  refine ⟨50723558866952782170703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270525647290414838243749 50723558866952782170703)
                  ·
                    rfl

theorem cell22_444527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 4].length) (baseStart_444527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444527 prefixEnd_444527 := by exact prefixLift 444527
  have htrace : WordTrace (prefixWord ++ tailWord_444527) baseStart_444527 baseEnd_444527 := by
    simpa [prefixWord, tailWord_444527, baseEnd_444527] using wordTrace_append hprefix tailTrace_444527
  have hstable : (prefixWord ++ tailWord_444527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444527).length < 2 ^ (prefixWord ++ tailWord_444527).sum := by decide
  have hdescent : baseEnd_444527 < baseStart_444527 := by decide
  rcases family_descends (prefixWord ++ tailWord_444527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444540 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_444540 : Nat := 118140960795 + 444540 * 2 ^ 59
def prefixEnd_444540 : Nat := 4983230072969 + 3 ^ 40 * 444540 * 2
def baseEnd_444540 : Nat := 152175126766530645937069

theorem tailTrace_444540 : CollatzResearch.WordTrace tailWord_444540 prefixEnd_444540 152175126766530645937069 := by
  unfold tailWord_444540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8106852904757488116349537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10809137206343317488466049 8106852904757488116349537)
  ·
    refine ⟨6080139678568116087262153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8106852904757488116349537 6080139678568116087262153)
    ·
      refine ⟨4560104758926087065446615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6080139678568116087262153 4560104758926087065446615)
      ·
        refine ⟨6840157138389130598169923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560104758926087065446615 6840157138389130598169923)
        ·
          refine ⟨10260235707583695897254885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6840157138389130598169923 10260235707583695897254885)
          ·
            refine ⟨1923794195171942980735291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10260235707583695897254885 1923794195171942980735291)
            ·
              refine ⟨2885691292757914471102937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1923794195171942980735291 2885691292757914471102937)
              ·
                refine ⟨2164268469568435853327203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2885691292757914471102937 2164268469568435853327203)
                ·
                  refine ⟨3246402704352653779990805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2164268469568435853327203 3246402704352653779990805)
                  ·
                    refine ⟨152175126766530645937069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3246402704352653779990805 152175126766530645937069)
                    ·
                      rfl

theorem cell22_444540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_444540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444540 prefixEnd_444540 := by exact prefixLift 444540
  have htrace : WordTrace (prefixWord ++ tailWord_444540) baseStart_444540 baseEnd_444540 := by
    simpa [prefixWord, tailWord_444540, baseEnd_444540] using wordTrace_append hprefix tailTrace_444540
  have hstable : (prefixWord ++ tailWord_444540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444540).length < 2 ^ (prefixWord ++ tailWord_444540).sum := by decide
  have hdescent : baseEnd_444540 < baseStart_444540 := by decide
  rcases family_descends (prefixWord ++ tailWord_444540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444593 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_444593 : Nat := 118140960795 + 444593 * 2 ^ 59
def prefixEnd_444593 : Nat := 4983230072969 + 3 ^ 40 * 444593 * 2
def baseEnd_444593 : Nat := 152193269749656174361907

theorem tailTrace_444593 : CollatzResearch.WordTrace tailWord_444593 prefixEnd_444593 152193269749656174361907 := by
  unfold tailWord_444593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16215638878322966284378433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810425918881977522918955 16215638878322966284378433)
  ·
    refine ⟨12161729158742224713283825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16215638878322966284378433 12161729158742224713283825)
    ·
      refine ⟨9121296869056668534962869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12161729158742224713283825 9121296869056668534962869)
      ·
        refine ⟨855121581474062675152769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9121296869056668534962869 855121581474062675152769)
        ·
          refine ⟨641341186105547006364577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855121581474062675152769 641341186105547006364577)
          ·
            refine ⟨481005889579160254773433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641341186105547006364577 481005889579160254773433)
            ·
              refine ⟨360754417184370191080075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481005889579160254773433 360754417184370191080075)
              ·
                refine ⟨541131625776555286620113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360754417184370191080075 541131625776555286620113)
                ·
                  refine ⟨405848719332416464965085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541131625776555286620113 405848719332416464965085)
                  ·
                    refine ⟨152193269749656174361907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405848719332416464965085 152193269749656174361907)
                    ·
                      rfl

theorem cell22_444593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_444593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444593 prefixEnd_444593 := by exact prefixLift 444593
  have htrace : WordTrace (prefixWord ++ tailWord_444593) baseStart_444593 baseEnd_444593 := by
    simpa [prefixWord, tailWord_444593, baseEnd_444593] using wordTrace_append hprefix tailTrace_444593
  have hstable : (prefixWord ++ tailWord_444593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444593).length < 2 ^ (prefixWord ++ tailWord_444593).sum := by decide
  have hdescent : baseEnd_444593 < baseStart_444593 := by decide
  rcases family_descends (prefixWord ++ tailWord_444593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444615 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_444615 : Nat := 118140960795 + 444615 * 2 ^ 59
def prefixEnd_444615 : Nat := 4983230072969 + 3 ^ 40 * 444615 * 2
def baseEnd_444615 : Nat := 152200800799255450311839

theorem tailTrace_444615 : CollatzResearch.WordTrace tailWord_444615 prefixEnd_444615 152200800799255450311839 := by
  unfold tailWord_444615
  simp only [CollatzResearch.WordTrace]
  refine ⟨16216441284243264041679299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10810960856162176027786199 16216441284243264041679299)
  ·
    refine ⟨24324661926364896062518949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16216441284243264041679299 24324661926364896062518949)
    ·
      refine ⟨4560874111193418011722303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24324661926364896062518949 4560874111193418011722303)
      ·
        refine ⟨6841311166790127017583455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4560874111193418011722303 6841311166790127017583455)
        ·
          refine ⟨10261966750185190526375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6841311166790127017583455 10261966750185190526375183)
          ·
            refine ⟨15392950125277785789562775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10261966750185190526375183 15392950125277785789562775)
            ·
              refine ⟨23089425187916678684344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15392950125277785789562775 23089425187916678684344163)
              ·
                refine ⟨34634137781875018026516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23089425187916678684344163 34634137781875018026516245)
                ·
                  refine ⟨1623475208525391469992949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34634137781875018026516245 1623475208525391469992949)
                  ·
                    refine ⟨152200800799255450311839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1623475208525391469992949 152200800799255450311839)
                    ·
                      rfl

theorem cell22_444615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_444615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444615 prefixEnd_444615 := by exact prefixLift 444615
  have htrace : WordTrace (prefixWord ++ tailWord_444615) baseStart_444615 baseEnd_444615 := by
    simpa [prefixWord, tailWord_444615, baseEnd_444615] using wordTrace_append hprefix tailTrace_444615
  have hstable : (prefixWord ++ tailWord_444615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444615).length < 2 ^ (prefixWord ++ tailWord_444615).sum := by decide
  have hdescent : baseEnd_444615 < baseStart_444615 := by decide
  rcases family_descends (prefixWord ++ tailWord_444615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444662 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_444662 : Nat := 118140960795 + 444662 * 2 ^ 59
def prefixEnd_444662 : Nat := 4983230072969 + 3 ^ 40 * 444662 * 2
def baseEnd_444662 : Nat := 50738963286587664795565

theorem tailTrace_444662 : CollatzResearch.WordTrace tailWord_444662 prefixEnd_444662 50738963286587664795565 := by
  unfold tailWord_444662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013634719692061941790015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10812103676715327379093493 1013634719692061941790015)
  ·
    refine ⟨1520452079538092912685023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013634719692061941790015 1520452079538092912685023)
    ·
      refine ⟨2280678119307139369027535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520452079538092912685023 2280678119307139369027535)
      ·
        refine ⟨3421017178960709053541303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2280678119307139369027535 3421017178960709053541303)
        ·
          refine ⟨5131525768441063580311955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3421017178960709053541303 5131525768441063580311955)
          ·
            refine ⟨7697288652661595370467933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5131525768441063580311955 7697288652661595370467933)
            ·
              refine ⟨2886483244748098263925475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7697288652661595370467933 2886483244748098263925475)
              ·
                refine ⟨4329724867122147395888213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2886483244748098263925475 4329724867122147395888213)
                ·
                  refine ⟨50738963286587664795565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4329724867122147395888213 50738963286587664795565)
                  ·
                    rfl

theorem cell22_444662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_444662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444662 prefixEnd_444662 := by exact prefixLift 444662
  have htrace : WordTrace (prefixWord ++ tailWord_444662) baseStart_444662 baseEnd_444662 := by
    simpa [prefixWord, tailWord_444662, baseEnd_444662] using wordTrace_append hprefix tailTrace_444662
  have hstable : (prefixWord ++ tailWord_444662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444662).length < 2 ^ (prefixWord ++ tailWord_444662).sum := by decide
  have hdescent : baseEnd_444662 < baseStart_444662 := by decide
  rcases family_descends (prefixWord ++ tailWord_444662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444681 : List Nat := [1, 2, 1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_444681 : Nat := 118140960795 + 444681 * 2 ^ 59
def prefixEnd_444681 : Nat := 4983230072969 + 3 ^ 40 * 444681 * 2
def baseEnd_444681 : Nat := 152223393948053278161637

theorem tailTrace_444681 : CollatzResearch.WordTrace tailWord_444681 prefixEnd_444681 152223393948053278161637 := by
  unfold tailWord_444681
  simp only [CollatzResearch.WordTrace]
  refine ⟨16218848502004157313581897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10812565668002771542387931 16218848502004157313581897)
  ·
    refine ⟨12164136376503117985186423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16218848502004157313581897 12164136376503117985186423)
    ·
      refine ⟨18246204564754676977779635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12164136376503117985186423 18246204564754676977779635)
      ·
        refine ⟨27369306847132015466669453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18246204564754676977779635 27369306847132015466669453)
        ·
          refine ⟨10263490067674505800001045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27369306847132015466669453 10263490067674505800001045)
          ·
            refine ⟨481101096922242459375049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10263490067674505800001045 481101096922242459375049)
            ·
              refine ⟨360825822691681844531287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481101096922242459375049 360825822691681844531287)
              ·
                refine ⟨541238734037522766796931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360825822691681844531287 541238734037522766796931)
                ·
                  refine ⟨811858101056284150195397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541238734037522766796931 811858101056284150195397)
                  ·
                    refine ⟨152223393948053278161637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 811858101056284150195397 152223393948053278161637)
                    ·
                      rfl

theorem cell22_444681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_444681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444681 prefixEnd_444681 := by exact prefixLift 444681
  have htrace : WordTrace (prefixWord ++ tailWord_444681) baseStart_444681 baseEnd_444681 := by
    simpa [prefixWord, tailWord_444681, baseEnd_444681] using wordTrace_append hprefix tailTrace_444681
  have hstable : (prefixWord ++ tailWord_444681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444681).length < 2 ^ (prefixWord ++ tailWord_444681).sum := by decide
  have hdescent : baseEnd_444681 < baseStart_444681 := by decide
  rcases family_descends (prefixWord ++ tailWord_444681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444724 : List Nat := [2, 5, 1, 1, 1, 3, 1, 8]
def baseStart_444724 : Nat := 118140960795 + 444724 * 2 ^ 59
def prefixEnd_444724 : Nat := 4983230072969 + 3 ^ 40 * 444724 * 2
def baseEnd_444724 : Nat := 16915345969646166592945

theorem tailTrace_444724 : CollatzResearch.WordTrace tailWord_444724 prefixEnd_444724 16915345969646166592945 := by
  unfold tailWord_444724
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110208420424187828698613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10813611227232250438264817 8110208420424187828698613)
  ·
    refine ⟨760332039414767608940495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8110208420424187828698613 760332039414767608940495)
    ·
      refine ⟨1140498059122151413410743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 760332039414767608940495 1140498059122151413410743)
      ·
        refine ⟨1710747088683227120116115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140498059122151413410743 1710747088683227120116115)
        ·
          refine ⟨2566120633024840680174173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1710747088683227120116115 2566120633024840680174173)
          ·
            refine ⟨962295237384315255065315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2566120633024840680174173 962295237384315255065315)
            ·
              refine ⟨1443442856076472882597973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962295237384315255065315 1443442856076472882597973)
              ·
                refine ⟨16915345969646166592945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1443442856076472882597973 16915345969646166592945)
                ·
                  rfl

theorem cell22_444724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 8].length) (baseStart_444724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444724 prefixEnd_444724 := by exact prefixLift 444724
  have htrace : WordTrace (prefixWord ++ tailWord_444724) baseStart_444724 baseEnd_444724 := by
    simpa [prefixWord, tailWord_444724, baseEnd_444724] using wordTrace_append hprefix tailTrace_444724
  have hstable : (prefixWord ++ tailWord_444724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444724).length < 2 ^ (prefixWord ++ tailWord_444724).sum := by decide
  have hdescent : baseEnd_444724 < baseStart_444724 := by decide
  rcases family_descends (prefixWord ++ tailWord_444724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444752 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 7]
def baseStart_444752 : Nat := 118140960795 + 444752 * 2 ^ 59
def prefixEnd_444752 : Nat := 4983230072969 + 3 ^ 40 * 444752 * 2
def baseEnd_444752 : Nat := 50749232899677586545473

theorem tailTrace_444752 : CollatzResearch.WordTrace tailWord_444752 prefixEnd_444752 50749232899677586545473 := by
  unfold tailWord_444752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110719042373468219708255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10814292056497957626277673 8110719042373468219708255)
  ·
    refine ⟨12166078563560202329562383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8110719042373468219708255 12166078563560202329562383)
    ·
      refine ⟨18249117845340303494343575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12166078563560202329562383 18249117845340303494343575)
      ·
        refine ⟨27373676768010455241515363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18249117845340303494343575 27373676768010455241515363)
        ·
          refine ⟨41060515152015682862273045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27373676768010455241515363 41060515152015682862273045)
          ·
            refine ⟨1924711647750735134169049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41060515152015682862273045 1924711647750735134169049)
            ·
              refine ⟨1443533735813051350626787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924711647750735134169049 1443533735813051350626787)
              ·
                refine ⟨2165300603719577025940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443533735813051350626787 2165300603719577025940181)
                ·
                  refine ⟨50749232899677586545473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2165300603719577025940181 50749232899677586545473)
                  ·
                    rfl

theorem cell22_444752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 7].length) (baseStart_444752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444752 prefixEnd_444752 := by exact prefixLift 444752
  have htrace : WordTrace (prefixWord ++ tailWord_444752) baseStart_444752 baseEnd_444752 := by
    simpa [prefixWord, tailWord_444752, baseEnd_444752] using wordTrace_append hprefix tailTrace_444752
  have hstable : (prefixWord ++ tailWord_444752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444752).length < 2 ^ (prefixWord ++ tailWord_444752).sum := by decide
  have hdescent : baseEnd_444752 < baseStart_444752 := by decide
  rcases family_descends (prefixWord ++ tailWord_444752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444756 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_444756 : Nat := 118140960795 + 444756 * 2 ^ 59
def prefixEnd_444756 : Nat := 4983230072969 + 3 ^ 40 * 444756 * 2
def baseEnd_444756 : Nat := 152249067980778082536407

theorem tailTrace_444756 : CollatzResearch.WordTrace tailWord_444756 prefixEnd_444756 152249067980778082536407 := by
  unfold tailWord_444756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8110791988366222561281061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10814389317821630081708081 8110791988366222561281061)
  ·
    refine ⟨1520773497818666730240199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8110791988366222561281061 1520773497818666730240199)
    ·
      refine ⟨2281160246728000095360299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520773497818666730240199 2281160246728000095360299)
      ·
        refine ⟨3421740370092000143040449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281160246728000095360299 3421740370092000143040449)
        ·
          refine ⟨2566305277569000107280337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3421740370092000143040449 2566305277569000107280337)
          ·
            refine ⟨1924728958176750080460253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2566305277569000107280337 1924728958176750080460253)
            ·
              refine ⟨721773359316281280172595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1924728958176750080460253 721773359316281280172595)
              ·
                refine ⟨1082660038974421920258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721773359316281280172595 1082660038974421920258893)
                ·
                  refine ⟨405997514615408220097085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082660038974421920258893 405997514615408220097085)
                  ·
                    refine ⟨152249067980778082536407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405997514615408220097085 152249067980778082536407)
                    ·
                      rfl

theorem cell22_444756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_444756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444756 prefixEnd_444756 := by exact prefixLift 444756
  have htrace : WordTrace (prefixWord ++ tailWord_444756) baseStart_444756 baseEnd_444756 := by
    simpa [prefixWord, tailWord_444756, baseEnd_444756] using wordTrace_append hprefix tailTrace_444756
  have hstable : (prefixWord ++ tailWord_444756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444756).length < 2 ^ (prefixWord ++ tailWord_444756).sum := by decide
  have hdescent : baseEnd_444756 < baseStart_444756 := by decide
  rcases family_descends (prefixWord ++ tailWord_444756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444767 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 2, 5]
def baseStart_444767 : Nat := 118140960795 + 444767 * 2 ^ 59
def prefixEnd_444767 : Nat := 4983230072969 + 3 ^ 40 * 444767 * 2
def baseEnd_444767 : Nat := 152252833505577720511373

theorem tailTrace_444767 : CollatzResearch.WordTrace tailWord_444767 prefixEnd_444767 152252833505577720511373 := by
  unfold tailWord_444767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16221985179692594001212555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10814656786461729334141703 16221985179692594001212555)
  ·
    refine ⟨24332977769538891001818833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16221985179692594001212555 24332977769538891001818833)
    ·
      refine ⟨18249733327154168251364125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24332977769538891001818833 18249733327154168251364125)
      ·
        refine ⟨6843649997682813094261547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18249733327154168251364125 6843649997682813094261547)
        ·
          refine ⟨10265474996524219641392321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6843649997682813094261547 10265474996524219641392321)
          ·
            refine ⟨7699106247393164731044241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10265474996524219641392321 7699106247393164731044241)
            ·
              refine ⟨5774329685544873548283181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7699106247393164731044241 5774329685544873548283181)
              ·
                refine ⟨2165373632079327580606193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5774329685544873548283181 2165373632079327580606193)
                ·
                  refine ⟨1624030224059495685454645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2165373632079327580606193 1624030224059495685454645)
                  ·
                    refine ⟨152252833505577720511373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1624030224059495685454645 152252833505577720511373)
                    ·
                      rfl

theorem cell22_444767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_444767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444767 prefixEnd_444767 := by exact prefixLift 444767
  have htrace : WordTrace (prefixWord ++ tailWord_444767) baseStart_444767 baseEnd_444767 := by
    simpa [prefixWord, tailWord_444767, baseEnd_444767] using wordTrace_append hprefix tailTrace_444767
  have hstable : (prefixWord ++ tailWord_444767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444767).length < 2 ^ (prefixWord ++ tailWord_444767).sum := by decide
  have hdescent : baseEnd_444767 < baseStart_444767 := by decide
  rcases family_descends (prefixWord ++ tailWord_444767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444865 : List Nat := [1, 2, 7, 1, 1, 1, 2, 1, 6]
def baseStart_444865 : Nat := 118140960795 + 444865 * 2 ^ 59
def prefixEnd_444865 : Nat := 4983230072969 + 3 ^ 40 * 444865 * 2
def baseEnd_444865 : Nat := 50762126969446043853691

theorem tailTrace_444865 : CollatzResearch.WordTrace tailWord_444865 prefixEnd_444865 50762126969446043853691 := by
  unfold tailWord_444865
  simp only [CollatzResearch.WordTrace]
  refine ⟨16225559533337556738280049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10817039688891704492186699 16225559533337556738280049)
  ·
    refine ⟨12169169650003167553710037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16225559533337556738280049 12169169650003167553710037)
    ·
      refine ⟨285214913671949239540079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12169169650003167553710037 285214913671949239540079)
      ·
        refine ⟨427822370507923859310119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285214913671949239540079 427822370507923859310119)
        ·
          refine ⟨641733555761885788965179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427822370507923859310119 641733555761885788965179)
          ·
            refine ⟨962600333642828683447769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641733555761885788965179 962600333642828683447769)
            ·
              refine ⟨721950250232121512585827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962600333642828683447769 721950250232121512585827)
              ·
                refine ⟨1082925375348182268878741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721950250232121512585827 1082925375348182268878741)
                ·
                  refine ⟨50762126969446043853691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1082925375348182268878741 50762126969446043853691)
                  ·
                    rfl

theorem cell22_444865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_444865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444865 prefixEnd_444865 := by exact prefixLift 444865
  have htrace : WordTrace (prefixWord ++ tailWord_444865) baseStart_444865 baseEnd_444865 := by
    simpa [prefixWord, tailWord_444865, baseEnd_444865] using wordTrace_append hprefix tailTrace_444865
  have hstable : (prefixWord ++ tailWord_444865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444865).length < 2 ^ (prefixWord ++ tailWord_444865).sum := by decide
  have hdescent : baseEnd_444865 < baseStart_444865 := by decide
  rcases family_descends (prefixWord ++ tailWord_444865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444904 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 7]
def baseStart_444904 : Nat := 118140960795 + 444904 * 2 ^ 59
def prefixEnd_444904 : Nat := 4983230072969 + 3 ^ 40 * 444904 * 2
def baseEnd_444904 : Nat := 50766577135118343278651

theorem tailTrace_444904 : CollatzResearch.WordTrace tailWord_444904 prefixEnd_444904 50766577135118343278651 := by
  unfold tailWord_444904
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113490990098133199474883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10817987986797510932633177 8113490990098133199474883)
  ·
    refine ⟨12170236485147199799212325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8113490990098133199474883 12170236485147199799212325)
    ·
      refine ⟨2281919340965099962352311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12170236485147199799212325 2281919340965099962352311)
      ·
        refine ⟨3422879011447649943528467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2281919340965099962352311 3422879011447649943528467)
        ·
          refine ⟨5134318517171474915292701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422879011447649943528467 5134318517171474915292701)
          ·
            refine ⟨1925369443939303093234763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5134318517171474915292701 1925369443939303093234763)
            ·
              refine ⟨2888054165908954639852145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1925369443939303093234763 2888054165908954639852145)
              ·
                refine ⟨2166040624431715979889109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2888054165908954639852145 2166040624431715979889109)
                ·
                  refine ⟨50766577135118343278651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2166040624431715979889109 50766577135118343278651)
                  ·
                    rfl

theorem cell22_444904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 7].length) (baseStart_444904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444904 prefixEnd_444904 := by exact prefixLift 444904
  have htrace : WordTrace (prefixWord ++ tailWord_444904) baseStart_444904 baseEnd_444904 := by
    simpa [prefixWord, tailWord_444904, baseEnd_444904] using wordTrace_append hprefix tailTrace_444904
  have hstable : (prefixWord ++ tailWord_444904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444904).length < 2 ^ (prefixWord ++ tailWord_444904).sum := by decide
  have hdescent : baseEnd_444904 < baseStart_444904 := by decide
  rcases family_descends (prefixWord ++ tailWord_444904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444925 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_444925 : Nat := 118140960795 + 444925 * 2 ^ 59
def prefixEnd_444925 : Nat := 4983230072969 + 3 ^ 40 * 444925 * 2
def baseEnd_444925 : Nat := 152306920134517975060889

theorem tailTrace_444925 : CollatzResearch.WordTrace tailWord_444925 prefixEnd_444925 152306920134517975060889 := by
  unfold tailWord_444925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16227747913120186985464229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10818498608746791323642819 16227747913120186985464229)
  ·
    refine ⟨3042702733710035059774543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16227747913120186985464229 3042702733710035059774543)
    ·
      refine ⟨4564054100565052589661815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042702733710035059774543 4564054100565052589661815)
      ·
        refine ⟨6846081150847578884492723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564054100565052589661815 6846081150847578884492723)
        ·
          refine ⟨10269121726271368326739085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6846081150847578884492723 10269121726271368326739085)
          ·
            refine ⟨3850920647351763122527157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10269121726271368326739085 3850920647351763122527157)
            ·
              refine ⟨361023810689227792736921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3850920647351763122527157 361023810689227792736921)
              ·
                refine ⟨270767858016920844552691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361023810689227792736921 270767858016920844552691)
                ·
                  refine ⟨406151787025381266829037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270767858016920844552691 406151787025381266829037)
                  ·
                    refine ⟨152306920134517975060889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406151787025381266829037 152306920134517975060889)
                    ·
                      rfl

theorem cell22_444925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_444925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444925 prefixEnd_444925 := by exact prefixLift 444925
  have htrace : WordTrace (prefixWord ++ tailWord_444925) baseStart_444925 baseEnd_444925 := by
    simpa [prefixWord, tailWord_444925, baseEnd_444925] using wordTrace_append hprefix tailTrace_444925
  have hstable : (prefixWord ++ tailWord_444925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444925).length < 2 ^ (prefixWord ++ tailWord_444925).sum := by decide
  have hdescent : baseEnd_444925 < baseStart_444925 := by decide
  rcases family_descends (prefixWord ++ tailWord_444925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_444949 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 8]
def baseStart_444949 : Nat := 118140960795 + 444949 * 2 ^ 59
def prefixEnd_444949 : Nat := 4983230072969 + 3 ^ 40 * 444949 * 2
def baseEnd_444949 : Nat := 50771711941663304153605

theorem tailTrace_444949 : CollatzResearch.WordTrace tailWord_444949 prefixEnd_444949 50771711941663304153605 := by
  unfold tailWord_444949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16228623265033239084337901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10819082176688826056225267 16228623265033239084337901)
  ·
    refine ⟨6085733724387464656626713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16228623265033239084337901 6085733724387464656626713)
    ·
      refine ⟨4564300293290598492470035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6085733724387464656626713 4564300293290598492470035)
      ·
        refine ⟨6846450439935897738705053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4564300293290598492470035 6846450439935897738705053)
        ·
          refine ⟨2567418914975961652014395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6846450439935897738705053 2567418914975961652014395)
          ·
            refine ⟨3851128372463942478021593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2567418914975961652014395 3851128372463942478021593)
            ·
              refine ⟨2888346279347956858516195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3851128372463942478021593 2888346279347956858516195)
              ·
                refine ⟨4332519419021935287774293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2888346279347956858516195 4332519419021935287774293)
                ·
                  refine ⟨50771711941663304153605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4332519419021935287774293 50771711941663304153605)
                  ·
                    rfl

theorem cell22_444949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_444949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_444949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_444949 prefixEnd_444949 := by exact prefixLift 444949
  have htrace : WordTrace (prefixWord ++ tailWord_444949) baseStart_444949 baseEnd_444949 := by
    simpa [prefixWord, tailWord_444949, baseEnd_444949] using wordTrace_append hprefix tailTrace_444949
  have hstable : (prefixWord ++ tailWord_444949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_444949).length < 2 ^ (prefixWord ++ tailWord_444949).sum := by decide
  have hdescent : baseEnd_444949 < baseStart_444949 := by decide
  rcases family_descends (prefixWord ++ tailWord_444949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445032 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_445032 : Nat := 118140960795 + 445032 * 2 ^ 59
def prefixEnd_445032 : Nat := 4983230072969 + 3 ^ 40 * 445032 * 2
def baseEnd_445032 : Nat := 152343548421205362635561

theorem tailTrace_445032 : CollatzResearch.WordTrace tailWord_445032 prefixEnd_445032 152343548421205362635561 := by
  unfold tailWord_445032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8115825261866272129804675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10821100349155029506406233 8115825261866272129804675)
  ·
    refine ⟨12173737892799408194707013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8115825261866272129804675 12173737892799408194707013)
    ·
      refine ⟨2282575854899889036507565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12173737892799408194707013 2282575854899889036507565)
      ·
        refine ⟨855965945587458388690337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2282575854899889036507565 855965945587458388690337)
        ·
          refine ⟨641974459190593791517753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855965945587458388690337 641974459190593791517753)
          ·
            refine ⟨481480844392945343638315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641974459190593791517753 481480844392945343638315)
            ·
              refine ⟨722221266589418015457473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481480844392945343638315 722221266589418015457473)
              ·
                refine ⟨541665949942063511593105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722221266589418015457473 541665949942063511593105)
                ·
                  refine ⟨406249462456547633694829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 541665949942063511593105 406249462456547633694829)
                  ·
                    refine ⟨152343548421205362635561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406249462456547633694829 152343548421205362635561)
                    ·
                      rfl

theorem cell22_445032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_445032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445032 prefixEnd_445032 := by exact prefixLift 445032
  have htrace : WordTrace (prefixWord ++ tailWord_445032) baseStart_445032 baseEnd_445032 := by
    simpa [prefixWord, tailWord_445032, baseEnd_445032] using wordTrace_append hprefix tailTrace_445032
  have hstable : (prefixWord ++ tailWord_445032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445032).length < 2 ^ (prefixWord ++ tailWord_445032).sum := by decide
  have hdescent : baseEnd_445032 < baseStart_445032 := by decide
  rcases family_descends (prefixWord ++ tailWord_445032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445120 : List Nat := [2, 1, 1, 2, 4, 4, 1, 2, 1, 4]
def baseStart_445120 : Nat := 118140960795 + 445120 * 2 ^ 59
def prefixEnd_445120 : Nat := 4983230072969 + 3 ^ 40 * 445120 * 2
def baseEnd_445120 : Nat := 152373672619602466435291

theorem tailTrace_445120 : CollatzResearch.WordTrace tailWord_445120 prefixEnd_445120 152373672619602466435291 := by
  unfold tailWord_445120
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117430073706867644406407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10823240098275823525875209 8117430073706867644406407)
  ·
    refine ⟨12176145110560301466609611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8117430073706867644406407 12176145110560301466609611)
    ·
      refine ⟨18264217665840452199914417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176145110560301466609611 18264217665840452199914417)
      ·
        refine ⟨13698163249380339149935813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18264217665840452199914417 13698163249380339149935813)
        ·
          refine ⟨2568405609258813590612965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13698163249380339149935813 2568405609258813590612965)
          ·
            refine ⟨481576051736027548239931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2568405609258813590612965 481576051736027548239931)
            ·
              refine ⟨722364077604041322359897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481576051736027548239931 722364077604041322359897)
              ·
                refine ⟨541773058203030991769923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 722364077604041322359897 541773058203030991769923)
                ·
                  refine ⟨812659587304546487654885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541773058203030991769923 812659587304546487654885)
                  ·
                    refine ⟨152373672619602466435291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 812659587304546487654885 152373672619602466435291)
                    ·
                      rfl

theorem cell22_445120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 1, 4].length) (baseStart_445120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445120 prefixEnd_445120 := by exact prefixLift 445120
  have htrace : WordTrace (prefixWord ++ tailWord_445120) baseStart_445120 baseEnd_445120 := by
    simpa [prefixWord, tailWord_445120, baseEnd_445120] using wordTrace_append hprefix tailTrace_445120
  have hstable : (prefixWord ++ tailWord_445120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445120).length < 2 ^ (prefixWord ++ tailWord_445120).sum := by decide
  have hdescent : baseEnd_445120 < baseStart_445120 := by decide
  rcases family_descends (prefixWord ++ tailWord_445120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445176 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_445176 : Nat := 118140960795 + 445176 * 2 ^ 59
def prefixEnd_445176 : Nat := 4983230072969 + 3 ^ 40 * 445176 * 2
def baseEnd_445176 : Nat := 152392842564036987035119

theorem tailTrace_445176 : CollatzResearch.WordTrace tailWord_445176 prefixEnd_445176 152392842564036987035119 := by
  unfold tailWord_445176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8118451317605428426425691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10824601756807237901900921 8118451317605428426425691)
  ·
    refine ⟨12177676976408142639638537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8118451317605428426425691 12177676976408142639638537)
    ·
      refine ⟨9133257732306106979728903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12177676976408142639638537 9133257732306106979728903)
      ·
        refine ⟨13699886598459160469593355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9133257732306106979728903 13699886598459160469593355)
        ·
          refine ⟨20549829897688740704390033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13699886598459160469593355 20549829897688740704390033)
          ·
            refine ⟨15412372423266555528292525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20549829897688740704390033 15412372423266555528292525)
            ·
              refine ⟨5779639658724958323109697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15412372423266555528292525 5779639658724958323109697)
              ·
                refine ⟨4334729744043718742332273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5779639658724958323109697 4334729744043718742332273)
                ·
                  refine ⟨3251047308032789056749205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4334729744043718742332273 3251047308032789056749205)
                  ·
                    refine ⟨152392842564036987035119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3251047308032789056749205 152392842564036987035119)
                    ·
                      rfl

theorem cell22_445176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_445176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445176 prefixEnd_445176 := by exact prefixLift 445176
  have htrace : WordTrace (prefixWord ++ tailWord_445176) baseStart_445176 baseEnd_445176 := by
    simpa [prefixWord, tailWord_445176, baseEnd_445176] using wordTrace_append hprefix tailTrace_445176
  have hstable : (prefixWord ++ tailWord_445176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445176).length < 2 ^ (prefixWord ++ tailWord_445176).sum := by decide
  have hdescent : baseEnd_445176 < baseStart_445176 := by decide
  rcases family_descends (prefixWord ++ tailWord_445176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445178 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 5, 3]
def baseStart_445178 : Nat := 118140960795 + 445178 * 2 ^ 59
def prefixEnd_445178 : Nat := 4983230072969 + 3 ^ 40 * 445178 * 2
def baseEnd_445178 : Nat := 152393527204909648485113

theorem tailTrace_445178 : CollatzResearch.WordTrace tailWord_445178 prefixEnd_445178 152393527204909648485113 := by
  unfold tailWord_445178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059243895300902798606047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10824650387469074129616125 4059243895300902798606047)
  ·
    refine ⟨6088865842951354197909071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4059243895300902798606047 6088865842951354197909071)
    ·
      refine ⟨9133298764427031296863607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088865842951354197909071 9133298764427031296863607)
      ·
        refine ⟨13699948146640546945295411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9133298764427031296863607 13699948146640546945295411)
        ·
          refine ⟨20549922219960820417943117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13699948146640546945295411 20549922219960820417943117)
          ·
            refine ⟨7706220832485307656728669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20549922219960820417943117 7706220832485307656728669)
            ·
              refine ⟨2889832812181990371273251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7706220832485307656728669 2889832812181990371273251)
              ·
                refine ⟨4334749218272985556909877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2889832812181990371273251 4334749218272985556909877)
                ·
                  refine ⟨406382739213092395960301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4334749218272985556909877 406382739213092395960301)
                  ·
                    refine ⟨152393527204909648485113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406382739213092395960301 152393527204909648485113)
                    ·
                      rfl

theorem cell22_445178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_445178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445178 prefixEnd_445178 := by exact prefixLift 445178
  have htrace : WordTrace (prefixWord ++ tailWord_445178) baseStart_445178 baseEnd_445178 := by
    simpa [prefixWord, tailWord_445178, baseEnd_445178] using wordTrace_append hprefix tailTrace_445178
  have hstable : (prefixWord ++ tailWord_445178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445178).length < 2 ^ (prefixWord ++ tailWord_445178).sum := by decide
  have hdescent : baseEnd_445178 < baseStart_445178 := by decide
  rcases family_descends (prefixWord ++ tailWord_445178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445182 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_445182 : Nat := 118140960795 + 445182 * 2 ^ 59
def prefixEnd_445182 : Nat := 4983230072969 + 3 ^ 40 * 445182 * 2
def baseEnd_445182 : Nat := 152394896486654971385101

theorem tailTrace_445182 : CollatzResearch.WordTrace tailWord_445182 prefixEnd_445182 152394896486654971385101 := by
  unfold tailWord_445182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029640184148639984696225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10824747648792746585046533 2029640184148639984696225)
  ·
    refine ⟨1522230138111479988522169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2029640184148639984696225 1522230138111479988522169)
    ·
      refine ⟨1141672603583609991391627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1522230138111479988522169 1141672603583609991391627)
      ·
        refine ⟨1712508905375414987087441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141672603583609991391627 1712508905375414987087441)
        ·
          refine ⟨1284381679031561240315581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1712508905375414987087441 1284381679031561240315581)
          ·
            refine ⟨481643129636835465118343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1284381679031561240315581 481643129636835465118343)
            ·
              refine ⟨722464694455253197677515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481643129636835465118343 722464694455253197677515)
              ·
                refine ⟨1083697041682879796516273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722464694455253197677515 1083697041682879796516273)
                ·
                  refine ⟨812772781262159847387205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1083697041682879796516273 812772781262159847387205)
                  ·
                    refine ⟨152394896486654971385101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 812772781262159847387205 152394896486654971385101)
                    ·
                      rfl

theorem cell22_445182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_445182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445182 prefixEnd_445182 := by exact prefixLift 445182
  have htrace : WordTrace (prefixWord ++ tailWord_445182) baseStart_445182 baseEnd_445182 := by
    simpa [prefixWord, tailWord_445182, baseEnd_445182] using wordTrace_append hprefix tailTrace_445182
  have hstable : (prefixWord ++ tailWord_445182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445182).length < 2 ^ (prefixWord ++ tailWord_445182).sum := by decide
  have hdescent : baseEnd_445182 < baseStart_445182 := by decide
  rcases family_descends (prefixWord ++ tailWord_445182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445212 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_445212 : Nat := 118140960795 + 445212 * 2 ^ 59
def prefixEnd_445212 : Nat := 4983230072969 + 3 ^ 40 * 445212 * 2
def baseEnd_445212 : Nat := 152405166099744893135009

theorem tailTrace_445212 : CollatzResearch.WordTrace tailWord_445212 prefixEnd_445212 152405166099744893135009 := by
  unfold tailWord_445212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119107831540217500580945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10825477108720290000774593 8119107831540217500580945)
  ·
    refine ⟨6089330873655163125435709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8119107831540217500580945 6089330873655163125435709)
    ·
      refine ⟨2283499077620686172038391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6089330873655163125435709 2283499077620686172038391)
      ·
        refine ⟨3425248616431029258057587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283499077620686172038391 3425248616431029258057587)
        ·
          refine ⟨5137872924646543887086381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425248616431029258057587 5137872924646543887086381)
          ·
            refine ⟨1926702346742453957657393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5137872924646543887086381 1926702346742453957657393)
            ·
              refine ⟨1445026760056840468243045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926702346742453957657393 1445026760056840468243045)
              ·
                refine ⟨270942517510657587795571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1445026760056840468243045 270942517510657587795571)
                ·
                  refine ⟨406413776265986381693357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270942517510657587795571 406413776265986381693357)
                  ·
                    refine ⟨152405166099744893135009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406413776265986381693357 152405166099744893135009)
                    ·
                      rfl

theorem cell22_445212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_445212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445212 prefixEnd_445212 := by exact prefixLift 445212
  have htrace : WordTrace (prefixWord ++ tailWord_445212) baseStart_445212 baseEnd_445212 := by
    simpa [prefixWord, tailWord_445212, baseEnd_445212] using wordTrace_append hprefix tailTrace_445212
  have hstable : (prefixWord ++ tailWord_445212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445212).length < 2 ^ (prefixWord ++ tailWord_445212).sum := by decide
  have hdescent : baseEnd_445212 < baseStart_445212 := by decide
  rcases family_descends (prefixWord ++ tailWord_445212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445246 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_445246 : Nat := 118140960795 + 445246 * 2 ^ 59
def prefixEnd_445246 : Nat := 4983230072969 + 3 ^ 40 * 445246 * 2
def baseEnd_445246 : Nat := 152416804994580137784905

theorem tailTrace_445246 : CollatzResearch.WordTrace tailWord_445246 prefixEnd_445246 152416804994580137784905 := by
  unfold tailWord_445246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029931968119657350987449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10826303829971505871933061 2029931968119657350987449)
  ·
    refine ⟨1522448976089743013240587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2029931968119657350987449 1522448976089743013240587)
    ·
      refine ⟨2283673464134614519860881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522448976089743013240587 2283673464134614519860881)
      ·
        refine ⟨1712755098100960889895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2283673464134614519860881 1712755098100960889895661)
        ·
          refine ⟨642283161787860333710873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1712755098100960889895661 642283161787860333710873)
          ·
            refine ⟨481712371340895250283155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642283161787860333710873 481712371340895250283155)
            ·
              refine ⟨722568557011342875424733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481712371340895250283155 722568557011342875424733)
              ·
                refine ⟨270963208879253578284275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722568557011342875424733 270963208879253578284275)
                ·
                  refine ⟨406444813318880367426413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270963208879253578284275 406444813318880367426413)
                  ·
                    refine ⟨152416804994580137784905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406444813318880367426413 152416804994580137784905)
                    ·
                      rfl

theorem cell22_445246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_445246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445246 prefixEnd_445246 := by exact prefixLift 445246
  have htrace : WordTrace (prefixWord ++ tailWord_445246) baseStart_445246 baseEnd_445246 := by
    simpa [prefixWord, tailWord_445246, baseEnd_445246] using wordTrace_append hprefix tailTrace_445246
  have hstable : (prefixWord ++ tailWord_445246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445246).length < 2 ^ (prefixWord ++ tailWord_445246).sum := by decide
  have hdescent : baseEnd_445246 < baseStart_445246 := by decide
  rcases family_descends (prefixWord ++ tailWord_445246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445298 : List Nat := [3, 2, 1, 2, 1, 1, 4, 8]
def baseStart_445298 : Nat := 118140960795 + 445298 * 2 ^ 59
def prefixEnd_445298 : Nat := 4983230072969 + 3 ^ 40 * 445298 * 2
def baseEnd_445298 : Nat := 16937178406363259498305

theorem tailTrace_445298 : CollatzResearch.WordTrace tailWord_445298 prefixEnd_445298 16937178406363259498305 := by
  unfold tailWord_445298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060338085192217922198137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10827568227179247792528365 4060338085192217922198137)
  ·
    refine ⟨3045253563894163441648603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4060338085192217922198137 3045253563894163441648603)
    ·
      refine ⟨4567880345841245162472905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045253563894163441648603 4567880345841245162472905)
      ·
        refine ⟨3425910259380933871854679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4567880345841245162472905 3425910259380933871854679)
        ·
          refine ⟨5138865389071400807782019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425910259380933871854679 5138865389071400807782019)
          ·
            refine ⟨7708298083607101211673029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5138865389071400807782019 7708298083607101211673029)
            ·
              refine ⟨1445305890676331477188693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7708298083607101211673029 1445305890676331477188693)
              ·
                refine ⟨16937178406363259498305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1445305890676331477188693 16937178406363259498305)
                ·
                  rfl

theorem cell22_445298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_445298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445298 prefixEnd_445298 := by exact prefixLift 445298
  have htrace : WordTrace (prefixWord ++ tailWord_445298) baseStart_445298 baseEnd_445298 := by
    simpa [prefixWord, tailWord_445298, baseEnd_445298] using wordTrace_append hprefix tailTrace_445298
  have hstable : (prefixWord ++ tailWord_445298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445298).length < 2 ^ (prefixWord ++ tailWord_445298).sum := by decide
  have hdescent : baseEnd_445298 < baseStart_445298 := by decide
  rcases family_descends (prefixWord ++ tailWord_445298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445302 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_445302 : Nat := 118140960795 + 445302 * 2 ^ 59
def prefixEnd_445302 : Nat := 4983230072969 + 3 ^ 40 * 445302 * 2
def baseEnd_445302 : Nat := 152435974939014658384733

theorem tailTrace_445302 : CollatzResearch.WordTrace tailWord_445302 prefixEnd_445302 152435974939014658384733 := by
  unfold tailWord_445302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015093639547148773246135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10827665488502920247958773 1015093639547148773246135)
  ·
    refine ⟨1522640459320723159869203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1015093639547148773246135 1522640459320723159869203)
    ·
      refine ⟨2283960688981084739803805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522640459320723159869203 2283960688981084739803805)
      ·
        refine ⟨856485258367906777426427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2283960688981084739803805 856485258367906777426427)
        ·
          refine ⟨1284727887551860166139641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856485258367906777426427 1284727887551860166139641)
          ·
            refine ⟨963545915663895124604731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284727887551860166139641 963545915663895124604731)
            ·
              refine ⟨1445318873495842686907097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963545915663895124604731 1445318873495842686907097)
              ·
                refine ⟨1083989155121882015180323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445318873495842686907097 1083989155121882015180323)
                ·
                  refine ⟨1625983732682823022770485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083989155121882015180323 1625983732682823022770485)
                  ·
                    refine ⟨152435974939014658384733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1625983732682823022770485 152435974939014658384733)
                    ·
                      rfl

theorem cell22_445302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_445302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445302 prefixEnd_445302 := by exact prefixLift 445302
  have htrace : WordTrace (prefixWord ++ tailWord_445302) baseStart_445302 baseEnd_445302 := by
    simpa [prefixWord, tailWord_445302, baseEnd_445302] using wordTrace_append hprefix tailTrace_445302
  have hstable : (prefixWord ++ tailWord_445302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445302).length < 2 ^ (prefixWord ++ tailWord_445302).sum := by decide
  have hdescent : baseEnd_445302 < baseStart_445302 := by decide
  rcases family_descends (prefixWord ++ tailWord_445302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445394 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_445394 : Nat := 118140960795 + 445394 * 2 ^ 59
def prefixEnd_445394 : Nat := 4983230072969 + 3 ^ 40 * 445394 * 2
def baseEnd_445394 : Nat := 50822489473052361694817

theorem tailTrace_445394 : CollatzResearch.WordTrace tailWord_445394 prefixEnd_445394 50822489473052361694817 := by
  unfold tailWord_445394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061213437105270021071809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10829902498947386722858157 4061213437105270021071809)
  ·
    refine ⟨3045910077828952515803857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4061213437105270021071809 3045910077828952515803857)
    ·
      refine ⟨2284432558371714386852893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045910077828952515803857 2284432558371714386852893)
      ·
        refine ⟨856662209389392895069835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2284432558371714386852893 856662209389392895069835)
        ·
          refine ⟨1284993314084089342604753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856662209389392895069835 1284993314084089342604753)
          ·
            refine ⟨963744985563067006953565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1284993314084089342604753 963744985563067006953565)
            ·
              refine ⟨361404369586150127607587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 963744985563067006953565 361404369586150127607587)
              ·
                refine ⟨542106554379225191411381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361404369586150127607587 542106554379225191411381)
                ·
                  refine ⟨50822489473052361694817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 542106554379225191411381 50822489473052361694817)
                  ·
                    rfl

theorem cell22_445394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_445394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445394 prefixEnd_445394 := by exact prefixLift 445394
  have htrace : WordTrace (prefixWord ++ tailWord_445394) baseStart_445394 baseEnd_445394 := by
    simpa [prefixWord, tailWord_445394, baseEnd_445394] using wordTrace_append hprefix tailTrace_445394
  have hstable : (prefixWord ++ tailWord_445394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445394).length < 2 ^ (prefixWord ++ tailWord_445394).sum := by decide
  have hdescent : baseEnd_445394 < baseStart_445394 := by decide
  rcases family_descends (prefixWord ++ tailWord_445394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445437 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_445437 : Nat := 118140960795 + 445437 * 2 ^ 59
def prefixEnd_445437 : Nat := 4983230072969 + 3 ^ 40 * 445437 * 2
def baseEnd_445437 : Nat := 152482188197919306259319

theorem tailTrace_445437 : CollatzResearch.WordTrace tailWord_445437 prefixEnd_445437 152482188197919306259319 := by
  unfold tailWord_445437
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246422087265298428102565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10830948058176865618735043 16246422087265298428102565)
  ·
    refine ⟨3046204141362243455269231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16246422087265298428102565 3046204141362243455269231)
    ·
      refine ⟨4569306212043365182903847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046204141362243455269231 4569306212043365182903847)
      ·
        refine ⟨6853959318065047774355771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569306212043365182903847 6853959318065047774355771)
        ·
          refine ⟨10280938977097571661533657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6853959318065047774355771 10280938977097571661533657)
          ·
            refine ⟨7710704232823178746150243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10280938977097571661533657 7710704232823178746150243)
            ·
              refine ⟨11566056349234768119225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7710704232823178746150243 11566056349234768119225365)
              ·
                refine ⟨542158891370379755588689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11566056349234768119225365 542158891370379755588689)
                ·
                  refine ⟨406619168527784816691517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542158891370379755588689 406619168527784816691517)
                  ·
                    refine ⟨152482188197919306259319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406619168527784816691517 152482188197919306259319)
                    ·
                      rfl

theorem cell22_445437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_445437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445437 prefixEnd_445437 := by exact prefixLift 445437
  have htrace : WordTrace (prefixWord ++ tailWord_445437) baseStart_445437 baseEnd_445437 := by
    simpa [prefixWord, tailWord_445437, baseEnd_445437] using wordTrace_append hprefix tailTrace_445437
  have hstable : (prefixWord ++ tailWord_445437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445437).length < 2 ^ (prefixWord ++ tailWord_445437).sum := by decide
  have hdescent : baseEnd_445437 < baseStart_445437 := by decide
  rcases family_descends (prefixWord ++ tailWord_445437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445450 : List Nat := [3, 1, 2, 2, 3, 1, 1, 9]
def baseStart_445450 : Nat := 118140960795 + 445450 * 2 ^ 59
def prefixEnd_445450 : Nat := 4983230072969 + 3 ^ 40 * 445450 * 2
def baseEnd_445450 : Nat := 16942959818176845076031

theorem tailTrace_445450 : CollatzResearch.WordTrace tailWord_445450 prefixEnd_445450 16942959818176845076031 := by
  unfold tailWord_445450
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061724059054550412081451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10831264157478801098883869 4061724059054550412081451)
  ·
    refine ⟨6092586088581825618122177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061724059054550412081451 6092586088581825618122177)
    ·
      refine ⟨4569439566436369213591633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6092586088581825618122177 4569439566436369213591633)
      ·
        refine ⟨3427079674827276910193725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4569439566436369213591633 3427079674827276910193725)
        ·
          refine ⟨1285154878060228841322647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3427079674827276910193725 1285154878060228841322647)
          ·
            refine ⟨1927732317090343261983971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285154878060228841322647 1927732317090343261983971)
            ·
              refine ⟨2891598475635514892975957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927732317090343261983971 2891598475635514892975957)
              ·
                refine ⟨16942959818176845076031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2891598475635514892975957 16942959818176845076031)
                ·
                  rfl

theorem cell22_445450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_445450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445450 prefixEnd_445450 := by exact prefixLift 445450
  have htrace : WordTrace (prefixWord ++ tailWord_445450) baseStart_445450 baseEnd_445450 := by
    simpa [prefixWord, tailWord_445450, baseEnd_445450] using wordTrace_append hprefix tailTrace_445450
  have hstable : (prefixWord ++ tailWord_445450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445450).length < 2 ^ (prefixWord ++ tailWord_445450).sum := by decide
  have hdescent : baseEnd_445450 < baseStart_445450 := by decide
  rcases family_descends (prefixWord ++ tailWord_445450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445454 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_445454 : Nat := 118140960795 + 445454 * 2 ^ 59
def prefixEnd_445454 : Nat := 4983230072969 + 3 ^ 40 * 445454 * 2
def baseEnd_445454 : Nat := 152488007645336928584267

theorem tailTrace_445454 : CollatzResearch.WordTrace tailWord_445454 prefixEnd_445454 152488007645336928584267 := by
  unfold tailWord_445454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030880266025463791433927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10831361418802473554314277 2030880266025463791433927)
  ·
    refine ⟨3046320399038195687150891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030880266025463791433927 3046320399038195687150891)
    ·
      refine ⟨4569480598557293530726337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046320399038195687150891 4569480598557293530726337)
      ·
        refine ⟨3427110448917970148044753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4569480598557293530726337 3427110448917970148044753)
        ·
          refine ⟨2570332836688477611033565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3427110448917970148044753 2570332836688477611033565)
          ·
            refine ⟨963874813758179104137587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2570332836688477611033565 963874813758179104137587)
            ·
              refine ⟨1445812220637268656206381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963874813758179104137587 1445812220637268656206381)
              ·
                refine ⟨542179582738975746077393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1445812220637268656206381 542179582738975746077393)
                ·
                  refine ⟨406634687054231809558045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 542179582738975746077393 406634687054231809558045)
                  ·
                    refine ⟨152488007645336928584267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406634687054231809558045 152488007645336928584267)
                    ·
                      rfl

theorem cell22_445454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_445454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445454 prefixEnd_445454 := by exact prefixLift 445454
  have htrace : WordTrace (prefixWord ++ tailWord_445454) baseStart_445454 baseEnd_445454 := by
    simpa [prefixWord, tailWord_445454, baseEnd_445454] using wordTrace_append hprefix tailTrace_445454
  have hstable : (prefixWord ++ tailWord_445454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445454).length < 2 ^ (prefixWord ++ tailWord_445454).sum := by decide
  have hdescent : baseEnd_445454 < baseStart_445454 := by decide
  rcases family_descends (prefixWord ++ tailWord_445454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445469 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_445469 : Nat := 118140960795 + 445469 * 2 ^ 59
def prefixEnd_445469 : Nat := 4983230072969 + 3 ^ 40 * 445469 * 2
def baseEnd_445469 : Nat := 152493142451881889459221

theorem tailTrace_445469 : CollatzResearch.WordTrace tailWord_445469 prefixEnd_445469 152493142451881889459221 := by
  unfold tailWord_445469
  simp only [CollatzResearch.WordTrace]
  refine ⟨16247589223149367893267461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10831726148766245262178307 16247589223149367893267461)
  ·
    refine ⟨3046422979340506479987649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16247589223149367893267461 3046422979340506479987649)
    ·
      refine ⟨2284817234505379859990737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3046422979340506479987649 2284817234505379859990737)
      ·
        refine ⟨1713612925879034894993053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2284817234505379859990737 1713612925879034894993053)
        ·
          refine ⟨642604847204638085622395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1713612925879034894993053 642604847204638085622395)
          ·
            refine ⟨963907270806957128433593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642604847204638085622395 963907270806957128433593)
            ·
              refine ⟨722930453105217846325195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 963907270806957128433593 722930453105217846325195)
              ·
                refine ⟨1084395679657826769487793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722930453105217846325195 1084395679657826769487793)
                ·
                  refine ⟨813296759743370077115845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084395679657826769487793 813296759743370077115845)
                  ·
                    refine ⟨152493142451881889459221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813296759743370077115845 152493142451881889459221)
                    ·
                      rfl

theorem cell22_445469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_445469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445469 prefixEnd_445469 := by exact prefixLift 445469
  have htrace : WordTrace (prefixWord ++ tailWord_445469) baseStart_445469 baseEnd_445469 := by
    simpa [prefixWord, tailWord_445469, baseEnd_445469] using wordTrace_append hprefix tailTrace_445469
  have hstable : (prefixWord ++ tailWord_445469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445469).length < 2 ^ (prefixWord ++ tailWord_445469).sum := by decide
  have hdescent : baseEnd_445469 < baseStart_445469 := by decide
  rcases family_descends (prefixWord ++ tailWord_445469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445540 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 10]
def baseStart_445540 : Nat := 118140960795 + 445540 * 2 ^ 59
def prefixEnd_445540 : Nat := 4983230072969 + 3 ^ 40 * 445540 * 2
def baseEnd_445540 : Nat := 50839149067620456978001

theorem tailTrace_445540 : CollatzResearch.WordTrace tailWord_445540 prefixEnd_445540 50839149067620456978001 := by
  unfold tailWord_445540
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125089402946073509551037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10833452537261431346068049 8125089402946073509551037)
  ·
    refine ⟨3046908526104777566081639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8125089402946073509551037 3046908526104777566081639)
    ·
      refine ⟨4570362789157166349122459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046908526104777566081639 4570362789157166349122459)
      ·
        refine ⟨6855544183735749523683689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570362789157166349122459 6855544183735749523683689)
        ·
          refine ⟨5141658137801812142762767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6855544183735749523683689 5141658137801812142762767)
          ·
            refine ⟨7712487206702718214144151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141658137801812142762767 7712487206702718214144151)
            ·
              refine ⟨11568730810054077321216227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712487206702718214144151 11568730810054077321216227)
              ·
                refine ⟨17353096215081115981824341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11568730810054077321216227 17353096215081115981824341)
                ·
                  refine ⟨50839149067620456978001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 17353096215081115981824341 50839149067620456978001)
                  ·
                    rfl

theorem cell22_445540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_445540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445540 prefixEnd_445540 := by exact prefixLift 445540
  have htrace : WordTrace (prefixWord ++ tailWord_445540) baseStart_445540 baseEnd_445540 := by
    simpa [prefixWord, tailWord_445540, baseEnd_445540] using wordTrace_append hprefix tailTrace_445540
  have hstable : (prefixWord ++ tailWord_445540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445540).length < 2 ^ (prefixWord ++ tailWord_445540).sum := by decide
  have hdescent : baseEnd_445540 < baseStart_445540 := by decide
  rcases family_descends (prefixWord ++ tailWord_445540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445576 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_445576 : Nat := 118140960795 + 445576 * 2 ^ 59
def prefixEnd_445576 : Nat := 4983230072969 + 3 ^ 40 * 445576 * 2
def baseEnd_445576 : Nat := 152529770738569277033893

theorem tailTrace_445576 : CollatzResearch.WordTrace tailWord_445576 prefixEnd_445576 152529770738569277033893 := by
  unfold tailWord_445576
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125745916880862583706291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10834327889174483444941721 8125745916880862583706291)
  ·
    refine ⟨12188618875321293875559437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125745916880862583706291 12188618875321293875559437)
    ·
      refine ⟨4570732078245485203334789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12188618875321293875559437 4570732078245485203334789)
      ·
        refine ⟨857012264671028475625273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4570732078245485203334789 857012264671028475625273)
        ·
          refine ⟨642759198503271356718955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857012264671028475625273 642759198503271356718955)
          ·
            refine ⟨964138797754907035078433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642759198503271356718955 964138797754907035078433)
            ·
              refine ⟨723104098316180276308825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964138797754907035078433 723104098316180276308825)
              ·
                refine ⟨542328073737135207231619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723104098316180276308825 542328073737135207231619)
                ·
                  refine ⟨813492110605702810847429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 542328073737135207231619 813492110605702810847429)
                  ·
                    refine ⟨152529770738569277033893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813492110605702810847429 152529770738569277033893)
                    ·
                      rfl

theorem cell22_445576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_445576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445576 prefixEnd_445576 := by exact prefixLift 445576
  have htrace : WordTrace (prefixWord ++ tailWord_445576) baseStart_445576 baseEnd_445576 := by
    simpa [prefixWord, tailWord_445576, baseEnd_445576] using wordTrace_append hprefix tailTrace_445576
  have hstable : (prefixWord ++ tailWord_445576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445576).length < 2 ^ (prefixWord ++ tailWord_445576).sum := by decide
  have hdescent : baseEnd_445576 < baseStart_445576 := by decide
  rcases family_descends (prefixWord ++ tailWord_445576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445591 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 4]
def baseStart_445591 : Nat := 118140960795 + 445591 * 2 ^ 59
def prefixEnd_445591 : Nat := 4983230072969 + 3 ^ 40 * 445591 * 2
def baseEnd_445591 : Nat := 50844968515038079302949

theorem tailTrace_445591 : CollatzResearch.WordTrace tailWord_445591 prefixEnd_445591 50844968515038079302949 := by
  unfold tailWord_445591
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252038928707382729208627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10834692619138255152805751 16252038928707382729208627)
  ·
    refine ⟨24378058393061074093812941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252038928707382729208627 24378058393061074093812941)
    ·
      refine ⟨9141771897397902785179853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24378058393061074093812941 9141771897397902785179853)
      ·
        refine ⟨3428164461524213544442445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9141771897397902785179853 3428164461524213544442445)
        ·
          refine ⟨1285561673071580079165917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3428164461524213544442445 1285561673071580079165917)
          ·
            refine ⟨482085627401842529687219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1285561673071580079165917 482085627401842529687219)
            ·
              refine ⟨723128441102763794530829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482085627401842529687219 723128441102763794530829)
              ·
                refine ⟨271173165413536422949061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 723128441102763794530829 271173165413536422949061)
                ·
                  refine ⟨50844968515038079302949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271173165413536422949061 50844968515038079302949)
                  ·
                    rfl

theorem cell22_445591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 4].length) (baseStart_445591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445591 prefixEnd_445591 := by exact prefixLift 445591
  have htrace : WordTrace (prefixWord ++ tailWord_445591) baseStart_445591 baseEnd_445591 := by
    simpa [prefixWord, tailWord_445591, baseEnd_445591] using wordTrace_append hprefix tailTrace_445591
  have hstable : (prefixWord ++ tailWord_445591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445591).length < 2 ^ (prefixWord ++ tailWord_445591).sum := by decide
  have hdescent : baseEnd_445591 < baseStart_445591 := by decide
  rcases family_descends (prefixWord ++ tailWord_445591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445604 : List Nat := [2, 3, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_445604 : Nat := 118140960795 + 445604 * 2 ^ 59
def prefixEnd_445604 : Nat := 4983230072969 + 3 ^ 40 * 445604 * 2
def baseEnd_445604 : Nat := 152539355710786537333807

theorem tailTrace_445604 : CollatzResearch.WordTrace tailWord_445604 prefixEnd_445604 152539355710786537333807 := by
  unfold tailWord_445604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126256538830142974715933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10835008718440190632954577 8126256538830142974715933)
  ·
    refine ⟨3047346202061303615518475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8126256538830142974715933 3047346202061303615518475)
    ·
      refine ⟨4571019303091955423277713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047346202061303615518475 4571019303091955423277713)
      ·
        refine ⟨3428264477318966567458285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4571019303091955423277713 3428264477318966567458285)
        ·
          refine ⟨1285599178994612462796857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3428264477318966567458285 1285599178994612462796857)
          ·
            refine ⟨964199384245959347097643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1285599178994612462796857 964199384245959347097643)
            ·
              refine ⟨1446299076368939020646465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964199384245959347097643 1446299076368939020646465)
              ·
                refine ⟨1084724307276704265484849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1446299076368939020646465 1084724307276704265484849)
                ·
                  refine ⟨813543230457528199113637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1084724307276704265484849 813543230457528199113637)
                  ·
                    refine ⟨152539355710786537333807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 813543230457528199113637 152539355710786537333807)
                    ·
                      rfl

theorem cell22_445604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_445604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445604 prefixEnd_445604 := by exact prefixLift 445604
  have htrace : WordTrace (prefixWord ++ tailWord_445604) baseStart_445604 baseEnd_445604 := by
    simpa [prefixWord, tailWord_445604, baseEnd_445604] using wordTrace_append hprefix tailTrace_445604
  have hstable : (prefixWord ++ tailWord_445604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445604).length < 2 ^ (prefixWord ++ tailWord_445604).sum := by decide
  have hdescent : baseEnd_445604 < baseStart_445604 := by decide
  rcases family_descends (prefixWord ++ tailWord_445604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445664 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 5]
def baseStart_445664 : Nat := 118140960795 + 445664 * 2 ^ 59
def prefixEnd_445664 : Nat := 4983230072969 + 3 ^ 40 * 445664 * 2
def baseEnd_445664 : Nat := 50853298312322126944541

theorem tailTrace_445664 : CollatzResearch.WordTrace tailWord_445664 prefixEnd_445664 50853298312322126944541 := by
  unfold tailWord_445664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127350728721458098308023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10836467638295277464410697 8127350728721458098308023)
  ·
    refine ⟨12191026093082187147462035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8127350728721458098308023 12191026093082187147462035)
    ·
      refine ⟨18286539139623280721193053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12191026093082187147462035 18286539139623280721193053)
      ·
        refine ⟨6857452177358730270447395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18286539139623280721193053 6857452177358730270447395)
        ·
          refine ⟨10286178266038095405671093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6857452177358730270447395 10286178266038095405671093)
          ·
            refine ⟨964329212441071444281665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10286178266038095405671093 964329212441071444281665)
            ·
              refine ⟨723246909330803583211249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 964329212441071444281665 723246909330803583211249)
              ·
                refine ⟨542435181998102687408437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 723246909330803583211249 542435181998102687408437)
                ·
                  refine ⟨50853298312322126944541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 542435181998102687408437 50853298312322126944541)
                  ·
                    rfl

theorem cell22_445664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_445664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445664 prefixEnd_445664 := by exact prefixLift 445664
  have htrace : WordTrace (prefixWord ++ tailWord_445664) baseStart_445664 baseEnd_445664 := by
    simpa [prefixWord, tailWord_445664, baseEnd_445664] using wordTrace_append hprefix tailTrace_445664
  have hstable : (prefixWord ++ tailWord_445664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445664).length < 2 ^ (prefixWord ++ tailWord_445664).sum := by decide
  have hdescent : baseEnd_445664 < baseStart_445664 := by decide
  rcases family_descends (prefixWord ++ tailWord_445664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445668 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_445668 : Nat := 118140960795 + 445668 * 2 ^ 59
def prefixEnd_445668 : Nat := 4983230072969 + 3 ^ 40 * 445668 * 2
def baseEnd_445668 : Nat := 152561264218711703733611

theorem tailTrace_445668 : CollatzResearch.WordTrace tailWord_445668 prefixEnd_445668 152561264218711703733611 := by
  unfold tailWord_445668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127423674714212439880829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10836564899618949919841105 8127423674714212439880829)
  ·
    refine ⟨3047783878017829664955311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8127423674714212439880829 3047783878017829664955311)
    ·
      refine ⟨4571675817026744497432967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047783878017829664955311 4571675817026744497432967)
      ·
        refine ⟨6857513725540116746149451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571675817026744497432967 6857513725540116746149451)
        ·
          refine ⟨10286270588310175119224177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6857513725540116746149451 10286270588310175119224177)
          ·
            refine ⟨7714702941232631339418133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10286270588310175119224177 7714702941232631339418133)
            ·
              refine ⟨361626700370279594035225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7714702941232631339418133 361626700370279594035225)
              ·
                refine ⟨271220025277709695526419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361626700370279594035225 271220025277709695526419)
                ·
                  refine ⟨406830037916564543289629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271220025277709695526419 406830037916564543289629)
                  ·
                    refine ⟨152561264218711703733611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406830037916564543289629 152561264218711703733611)
                    ·
                      rfl

theorem cell22_445668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_445668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445668 prefixEnd_445668 := by exact prefixLift 445668
  have htrace : WordTrace (prefixWord ++ tailWord_445668) baseStart_445668 baseEnd_445668 := by
    simpa [prefixWord, tailWord_445668, baseEnd_445668] using wordTrace_append hprefix tailTrace_445668
  have hstable : (prefixWord ++ tailWord_445668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445668).length < 2 ^ (prefixWord ++ tailWord_445668).sum := by decide
  have hdescent : baseEnd_445668 < baseStart_445668 := by decide
  rcases family_descends (prefixWord ++ tailWord_445668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445679 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 2, 5]
def baseStart_445679 : Nat := 118140960795 + 445679 * 2 ^ 59
def prefixEnd_445679 : Nat := 4983230072969 + 3 ^ 40 * 445679 * 2
def baseEnd_445679 : Nat := 152565029743511341708577

theorem tailTrace_445679 : CollatzResearch.WordTrace tailWord_445679 prefixEnd_445679 152565029743511341708577 := by
  unfold tailWord_445679
  simp only [CollatzResearch.WordTrace]
  refine ⟨16255248552388573758412091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10836832368259049172274727 16255248552388573758412091)
  ·
    refine ⟨24382872828582860637618137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16255248552388573758412091 24382872828582860637618137)
    ·
      refine ⟨18287154621437145478213603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24382872828582860637618137 18287154621437145478213603)
      ·
        refine ⟨27430731932155718217320405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18287154621437145478213603 27430731932155718217320405)
        ·
          refine ⟨642907779659899645718447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27430731932155718217320405 642907779659899645718447)
          ·
            refine ⟨964361669489849468577671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642907779659899645718447 964361669489849468577671)
            ·
              refine ⟨1446542504234774202866507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964361669489849468577671 1446542504234774202866507)
              ·
                refine ⟨2169813756352161304299761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446542504234774202866507 2169813756352161304299761)
                ·
                  refine ⟨1627360317264120978224821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169813756352161304299761 1627360317264120978224821)
                  ·
                    refine ⟨152565029743511341708577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1627360317264120978224821 152565029743511341708577)
                    ·
                      rfl

theorem cell22_445679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_445679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445679 prefixEnd_445679 := by exact prefixLift 445679
  have htrace : WordTrace (prefixWord ++ tailWord_445679) baseStart_445679 baseEnd_445679 := by
    simpa [prefixWord, tailWord_445679, baseEnd_445679] using wordTrace_append hprefix tailTrace_445679
  have hstable : (prefixWord ++ tailWord_445679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445679).length < 2 ^ (prefixWord ++ tailWord_445679).sum := by decide
  have hdescent : baseEnd_445679 < baseStart_445679 := by decide
  rcases family_descends (prefixWord ++ tailWord_445679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445752 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_445752 : Nat := 118140960795 + 445752 * 2 ^ 59
def prefixEnd_445752 : Nat := 4983230072969 + 3 ^ 40 * 445752 * 2
def baseEnd_445752 : Nat := 152590019135363484633353

theorem tailTrace_445752 : CollatzResearch.WordTrace tailWord_445752 prefixEnd_445752 152590019135363484633353 := by
  unfold tailWord_445752
  simp only [CollatzResearch.WordTrace]
  refine ⟨8128955540562053612909755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10838607387416071483879673 8128955540562053612909755)
  ·
    refine ⟨12193433310843080419364633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8128955540562053612909755 12193433310843080419364633)
    ·
      refine ⟨9145074983132310314523475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12193433310843080419364633 9145074983132310314523475)
      ·
        refine ⟨13717612474698465471785213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9145074983132310314523475 13717612474698465471785213)
        ·
          refine ⟨5144104678011924551919455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13717612474698465471785213 5144104678011924551919455)
          ·
            refine ⟨7716157017017886827879183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5144104678011924551919455 7716157017017886827879183)
            ·
              refine ⟨11574235525526830241818775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7716157017017886827879183 11574235525526830241818775)
              ·
                refine ⟨17361353288290245362728163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11574235525526830241818775 17361353288290245362728163)
                ·
                  refine ⟨26042029932435368044092245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17361353288290245362728163 26042029932435368044092245)
                  ·
                    refine ⟨152590019135363484633353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26042029932435368044092245 152590019135363484633353)
                    ·
                      rfl

theorem cell22_445752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_445752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445752 prefixEnd_445752 := by exact prefixLift 445752
  have htrace : WordTrace (prefixWord ++ tailWord_445752) baseStart_445752 baseEnd_445752 := by
    simpa [prefixWord, tailWord_445752, baseEnd_445752] using wordTrace_append hprefix tailTrace_445752
  have hstable : (prefixWord ++ tailWord_445752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445752).length < 2 ^ (prefixWord ++ tailWord_445752).sum := by decide
  have hdescent : baseEnd_445752 < baseStart_445752 := by decide
  rcases family_descends (prefixWord ++ tailWord_445752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445769 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_445769 : Nat := 118140960795 + 445769 * 2 ^ 59
def prefixEnd_445769 : Nat := 4983230072969 + 3 ^ 40 * 445769 * 2
def baseEnd_445769 : Nat := 152595838582781106958301

theorem tailTrace_445769 : CollatzResearch.WordTrace tailWord_445769 prefixEnd_445769 152595838582781106958301 := by
  unfold tailWord_445769
  simp only [CollatzResearch.WordTrace]
  refine ⟨16258531122062519129188361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10839020748041679419458907 16258531122062519129188361)
  ·
    refine ⟨12193898341546889346891271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16258531122062519129188361 12193898341546889346891271)
    ·
      refine ⟨18290847512320334020336907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12193898341546889346891271 18290847512320334020336907)
      ·
        refine ⟨27436271268480501030505361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18290847512320334020336907 27436271268480501030505361)
        ·
          refine ⟨20577203451360375772879021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27436271268480501030505361 20577203451360375772879021)
          ·
            refine ⟨7716451294260140914829633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20577203451360375772879021 7716451294260140914829633)
            ·
              refine ⟨5787338470695105686122225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7716451294260140914829633 5787338470695105686122225)
              ·
                refine ⟨4340503853021329264591669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787338470695105686122225 4340503853021329264591669)
                ·
                  refine ⟨406922236220749618555469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4340503853021329264591669 406922236220749618555469)
                  ·
                    refine ⟨152595838582781106958301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406922236220749618555469 152595838582781106958301)
                    ·
                      rfl

theorem cell22_445769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_445769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445769 prefixEnd_445769 := by exact prefixLift 445769
  have htrace : WordTrace (prefixWord ++ tailWord_445769) baseStart_445769 baseEnd_445769 := by
    simpa [prefixWord, tailWord_445769, baseEnd_445769] using wordTrace_append hprefix tailTrace_445769
  have hstable : (prefixWord ++ tailWord_445769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445769).length < 2 ^ (prefixWord ++ tailWord_445769).sum := by decide
  have hdescent : baseEnd_445769 < baseStart_445769 := by decide
  rcases family_descends (prefixWord ++ tailWord_445769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445786 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 3, 3]
def baseStart_445786 : Nat := 118140960795 + 445786 * 2 ^ 59
def prefixEnd_445786 : Nat := 4983230072969 + 3 ^ 40 * 445786 * 2
def baseEnd_445786 : Nat := 152601658030198729283249

theorem tailTrace_445786 : CollatzResearch.WordTrace tailWord_445786 prefixEnd_445786 152601658030198729283249 := by
  unfold tailWord_445786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064787790750232758139303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10839434108667287355038141 4064787790750232758139303)
  ·
    refine ⟨6097181686125349137208955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064787790750232758139303 6097181686125349137208955)
    ·
      refine ⟨9145772529188023705813433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6097181686125349137208955 9145772529188023705813433)
      ·
        refine ⟨6859329396891017779360075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9145772529188023705813433 6859329396891017779360075)
        ·
          refine ⟨10288994095336526669040113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859329396891017779360075 10288994095336526669040113)
          ·
            refine ⟨7716745571502395001780085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10288994095336526669040113 7716745571502395001780085)
            ·
              refine ⟨723444897328349531416883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7716745571502395001780085 723444897328349531416883)
              ·
                refine ⟨1085167345992524297125325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723444897328349531416883 1085167345992524297125325)
                ·
                  refine ⟨406937754747196611421997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085167345992524297125325 406937754747196611421997)
                  ·
                    refine ⟨152601658030198729283249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 406937754747196611421997 152601658030198729283249)
                    ·
                      rfl

theorem cell22_445786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_445786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445786 prefixEnd_445786 := by exact prefixLift 445786
  have htrace : WordTrace (prefixWord ++ tailWord_445786) baseStart_445786 baseEnd_445786 := by
    simpa [prefixWord, tailWord_445786, baseEnd_445786] using wordTrace_append hprefix tailTrace_445786
  have hstable : (prefixWord ++ tailWord_445786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445786).length < 2 ^ (prefixWord ++ tailWord_445786).sum := by decide
  have hdescent : baseEnd_445786 < baseStart_445786 := by decide
  rcases family_descends (prefixWord ++ tailWord_445786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445910 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_445910 : Nat := 118140960795 + 445910 * 2 ^ 59
def prefixEnd_445910 : Nat := 4983230072969 + 3 ^ 40 * 445910 * 2
def baseEnd_445910 : Nat := 152644105764303739182869

theorem tailTrace_445910 : CollatzResearch.WordTrace tailWord_445910 prefixEnd_445910 152644105764303739182869 := by
  unfold tailWord_445910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016479613409481263129449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10842449209701133473380789 1016479613409481263129449)
  ·
    refine ⟨762359710057110947347087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016479613409481263129449 762359710057110947347087)
    ·
      refine ⟨1143539565085666421020631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762359710057110947347087 1143539565085666421020631)
      ·
        refine ⟨1715309347628499631530947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143539565085666421020631 1715309347628499631530947)
        ·
          refine ⟨2572964021442749447296421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715309347628499631530947 2572964021442749447296421)
          ·
            refine ⟨482430754020515521368079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2572964021442749447296421 482430754020515521368079)
            ·
              refine ⟨723646131030773282052119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482430754020515521368079 723646131030773282052119)
              ·
                refine ⟨1085469196546159923078179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723646131030773282052119 1085469196546159923078179)
                ·
                  refine ⟨1628203794819239884617269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085469196546159923078179 1628203794819239884617269)
                  ·
                    refine ⟨152644105764303739182869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1628203794819239884617269 152644105764303739182869)
                    ·
                      rfl

theorem cell22_445910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_445910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445910 prefixEnd_445910 := by exact prefixLift 445910
  have htrace : WordTrace (prefixWord ++ tailWord_445910) baseStart_445910 baseEnd_445910 := by
    simpa [prefixWord, tailWord_445910, baseEnd_445910] using wordTrace_append hprefix tailTrace_445910
  have hstable : (prefixWord ++ tailWord_445910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445910).length < 2 ^ (prefixWord ++ tailWord_445910).sum := by decide
  have hdescent : baseEnd_445910 < baseStart_445910 := by decide
  rcases family_descends (prefixWord ++ tailWord_445910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_445923 : List Nat := [1, 1, 1, 6, 2, 3, 2, 6]
def baseStart_445923 : Nat := 118140960795 + 445923 * 2 ^ 59
def prefixEnd_445923 : Nat := 4983230072969 + 3 ^ 40 * 445923 * 2
def baseEnd_445923 : Nat := 16960950658886226511981

theorem tailTrace_445923 : CollatzResearch.WordTrace tailWord_445923 prefixEnd_445923 16960950658886226511981 := by
  unfold tailWord_445923
  simp only [CollatzResearch.WordTrace]
  refine ⟨16264147963504603430294423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10842765309003068953529615 16264147963504603430294423)
  ·
    refine ⟨24396221945256905145441635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16264147963504603430294423 24396221945256905145441635)
    ·
      refine ⟨36594332917885357718162453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24396221945256905145441635 36594332917885357718162453)
      ·
        refine ⟨1715359355525876143038865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36594332917885357718162453 1715359355525876143038865)
        ·
          refine ⟨1286519516644407107279149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1715359355525876143038865 1286519516644407107279149)
          ·
            refine ⟨482444818741652665229681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1286519516644407107279149 482444818741652665229681)
            ·
              refine ⟨361833614056239498922261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482444818741652665229681 361833614056239498922261)
              ·
                refine ⟨16960950658886226511981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361833614056239498922261 16960950658886226511981)
                ·
                  rfl

theorem cell22_445923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 6].length) (baseStart_445923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_445923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_445923 prefixEnd_445923 := by exact prefixLift 445923
  have htrace : WordTrace (prefixWord ++ tailWord_445923) baseStart_445923 baseEnd_445923 := by
    simpa [prefixWord, tailWord_445923, baseEnd_445923] using wordTrace_append hprefix tailTrace_445923
  have hstable : (prefixWord ++ tailWord_445923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_445923).length < 2 ^ (prefixWord ++ tailWord_445923).sum := by decide
  have hdescent : baseEnd_445923 < baseStart_445923 := by decide
  rcases family_descends (prefixWord ++ tailWord_445923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446006 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_446006 : Nat := 118140960795 + 446006 * 2 ^ 59
def prefixEnd_446006 : Nat := 4983230072969 + 3 ^ 40 * 446006 * 2
def baseEnd_446006 : Nat := 152676968526191488782575

theorem tailTrace_446006 : CollatzResearch.WordTrace tailWord_446006 prefixEnd_446006 152676968526191488782575 := by
  unfold tailWord_446006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016698451387744287847867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10844783481469272403710581 1016698451387744287847867)
  ·
    refine ⟨1525047677081616431771801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016698451387744287847867 1525047677081616431771801)
    ·
      refine ⟨1143785757811212323828851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1525047677081616431771801 1143785757811212323828851)
      ·
        refine ⟨1715678636716818485743277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143785757811212323828851 1715678636716818485743277)
        ·
          refine ⟨643379488768806932153729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1715678636716818485743277 643379488768806932153729)
          ·
            refine ⟨482534616576605199115297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643379488768806932153729 482534616576605199115297)
            ·
              refine ⟨361900962432453899336473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482534616576605199115297 361900962432453899336473)
              ·
                refine ⟨271425721824340424502355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361900962432453899336473 271425721824340424502355)
                ·
                  refine ⟨407138582736510636753533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271425721824340424502355 407138582736510636753533)
                  ·
                    refine ⟨152676968526191488782575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407138582736510636753533 152676968526191488782575)
                    ·
                      rfl

theorem cell22_446006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_446006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446006 prefixEnd_446006 := by exact prefixLift 446006
  have htrace : WordTrace (prefixWord ++ tailWord_446006) baseStart_446006 baseEnd_446006 := by
    simpa [prefixWord, tailWord_446006, baseEnd_446006] using wordTrace_append hprefix tailTrace_446006
  have hstable : (prefixWord ++ tailWord_446006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446006).length < 2 ^ (prefixWord ++ tailWord_446006).sum := by decide
  have hdescent : baseEnd_446006 < baseStart_446006 := by decide
  rcases family_descends (prefixWord ++ tailWord_446006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446026 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_446026 : Nat := 118140960795 + 446026 * 2 ^ 59
def prefixEnd_446026 : Nat := 4983230072969 + 3 ^ 40 * 446026 * 2
def baseEnd_446026 : Nat := 152683814934918103282513

theorem tailTrace_446026 : CollatzResearch.WordTrace tailWord_446026 prefixEnd_446026 152683814934918103282513 := by
  unfold tailWord_446026
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066976170532863005323483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10845269788087634680862621 4066976170532863005323483)
  ·
    refine ⟨6100464255799294507985225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4066976170532863005323483 6100464255799294507985225)
    ·
      refine ⟨4575348191849470880988919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6100464255799294507985225 4575348191849470880988919)
      ·
        refine ⟨6863022287774206321483379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575348191849470880988919 6863022287774206321483379)
        ·
          refine ⟨10294533431661309482225069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863022287774206321483379 10294533431661309482225069)
          ·
            refine ⟨3860450036872991055834401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10294533431661309482225069 3860450036872991055834401)
            ·
              refine ⟨2895337527654743291875801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860450036872991055834401 2895337527654743291875801)
              ·
                refine ⟨2171503145741057468906851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2895337527654743291875801 2171503145741057468906851)
                ·
                  refine ⟨3257254718611586203360277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171503145741057468906851 3257254718611586203360277)
                  ·
                    refine ⟨152683814934918103282513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3257254718611586203360277 152683814934918103282513)
                    ·
                      rfl

theorem cell22_446026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_446026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446026 prefixEnd_446026 := by exact prefixLift 446026
  have htrace : WordTrace (prefixWord ++ tailWord_446026) baseStart_446026 baseEnd_446026 := by
    simpa [prefixWord, tailWord_446026, baseEnd_446026] using wordTrace_append hprefix tailTrace_446026
  have hstable : (prefixWord ++ tailWord_446026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446026).length < 2 ^ (prefixWord ++ tailWord_446026).sum := by decide
  have hdescent : baseEnd_446026 < baseStart_446026 := by decide
  rcases family_descends (prefixWord ++ tailWord_446026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446028 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_446028 : Nat := 118140960795 + 446028 * 2 ^ 59
def prefixEnd_446028 : Nat := 4983230072969 + 3 ^ 40 * 446028 * 2
def baseEnd_446028 : Nat := 152684499575790764732507

theorem tailTrace_446028 : CollatzResearch.WordTrace tailWord_446028 prefixEnd_446028 152684499575790764732507 := by
  unfold tailWord_446028
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133988814062103181433369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10845318418749470908577825 8133988814062103181433369)
  ·
    refine ⟨6100491610546577386075027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8133988814062103181433369 6100491610546577386075027)
    ·
      refine ⟨9150737415819866079112541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6100491610546577386075027 9150737415819866079112541)
      ·
        refine ⟨3431526530932449779667203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9150737415819866079112541 3431526530932449779667203)
        ·
          refine ⟨5147289796398674669500805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3431526530932449779667203 5147289796398674669500805)
          ·
            refine ⟨965116836824751500531401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5147289796398674669500805 965116836824751500531401)
            ·
              refine ⟨723837627618563625398551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965116836824751500531401 723837627618563625398551)
              ·
                refine ⟨1085756441427845438097827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723837627618563625398551 1085756441427845438097827)
                ·
                  refine ⟨1628634662141768157146741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085756441427845438097827 1628634662141768157146741)
                  ·
                    refine ⟨152684499575790764732507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1628634662141768157146741 152684499575790764732507)
                    ·
                      rfl

theorem cell22_446028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_446028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446028 prefixEnd_446028 := by exact prefixLift 446028
  have htrace : WordTrace (prefixWord ++ tailWord_446028) baseStart_446028 baseEnd_446028 := by
    simpa [prefixWord, tailWord_446028, baseEnd_446028] using wordTrace_append hprefix tailTrace_446028
  have hstable : (prefixWord ++ tailWord_446028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446028).length < 2 ^ (prefixWord ++ tailWord_446028).sum := by decide
  have hdescent : baseEnd_446028 < baseStart_446028 := by decide
  rcases family_descends (prefixWord ++ tailWord_446028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446090 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 3, 3]
def baseStart_446090 : Nat := 118140960795 + 446090 * 2 ^ 59
def prefixEnd_446090 : Nat := 4983230072969 + 3 ^ 40 * 446090 * 2
def baseEnd_446090 : Nat := 152705723442843269682317

theorem tailTrace_446090 : CollatzResearch.WordTrace tailWord_446090 prefixEnd_446090 152705723442843269682317 := by
  unfold tailWord_446090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067559738474897737905931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10846825969266393967749149 4067559738474897737905931)
  ·
    refine ⟨6101339607712346606858897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4067559738474897737905931 6101339607712346606858897)
    ·
      refine ⟨4576004705784259955144173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6101339607712346606858897 4576004705784259955144173)
      ·
        refine ⟨1716001764669097483179065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4576004705784259955144173 1716001764669097483179065)
        ·
          refine ⟨1287001323501823112384299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716001764669097483179065 1287001323501823112384299)
          ·
            refine ⟨1930501985252734668576449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287001323501823112384299 1930501985252734668576449)
            ·
              refine ⟨1447876488939551001432337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930501985252734668576449 1447876488939551001432337)
              ·
                refine ⟨1085907366704663251074253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447876488939551001432337 1085907366704663251074253)
                ·
                  refine ⟨407215262514248719152845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1085907366704663251074253 407215262514248719152845)
                  ·
                    refine ⟨152705723442843269682317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407215262514248719152845 152705723442843269682317)
                    ·
                      rfl

theorem cell22_446090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_446090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446090 prefixEnd_446090 := by exact prefixLift 446090
  have htrace : WordTrace (prefixWord ++ tailWord_446090) baseStart_446090 baseEnd_446090 := by
    simpa [prefixWord, tailWord_446090, baseEnd_446090] using wordTrace_append hprefix tailTrace_446090
  have hstable : (prefixWord ++ tailWord_446090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446090).length < 2 ^ (prefixWord ++ tailWord_446090).sum := by decide
  have hdescent : baseEnd_446090 < baseStart_446090 := by decide
  rcases family_descends (prefixWord ++ tailWord_446090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446101 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_446101 : Nat := 118140960795 + 446101 * 2 ^ 59
def prefixEnd_446101 : Nat := 4983230072969 + 3 ^ 40 * 446101 * 2
def baseEnd_446101 : Nat := 152709488967642907657283

theorem tailTrace_446101 : CollatzResearch.WordTrace tailWord_446101 prefixEnd_446101 152709488967642907657283 := by
  unfold tailWord_446101
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270640156859739830274157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10847093437906493220182771 16270640156859739830274157)
  ·
    refine ⟨6101490058822402436352809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16270640156859739830274157 6101490058822402436352809)
    ·
      refine ⟨4576117544116801827264607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6101490058822402436352809 4576117544116801827264607)
      ·
        refine ⟨6864176316175202740896911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576117544116801827264607 6864176316175202740896911)
        ·
          refine ⟨10296264474262804111345367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864176316175202740896911 10296264474262804111345367)
          ·
            refine ⟨15444396711394206167018051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296264474262804111345367 15444396711394206167018051)
            ·
              refine ⟨23166595067091309250527077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444396711394206167018051 23166595067091309250527077)
              ·
                refine ⟨4343736575079620484473827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23166595067091309250527077 4343736575079620484473827)
                ·
                  refine ⟨6515604862619430726710741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343736575079620484473827 6515604862619430726710741)
                  ·
                    refine ⟨152709488967642907657283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6515604862619430726710741 152709488967642907657283)
                    ·
                      rfl

theorem cell22_446101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_446101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446101 prefixEnd_446101 := by exact prefixLift 446101
  have htrace : WordTrace (prefixWord ++ tailWord_446101) baseStart_446101 baseEnd_446101 := by
    simpa [prefixWord, tailWord_446101, baseEnd_446101] using wordTrace_append hprefix tailTrace_446101
  have hstable : (prefixWord ++ tailWord_446101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446101).length < 2 ^ (prefixWord ++ tailWord_446101).sum := by decide
  have hdescent : baseEnd_446101 < baseStart_446101 := by decide
  rcases family_descends (prefixWord ++ tailWord_446101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446148 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_446148 : Nat := 118140960795 + 446148 * 2 ^ 59
def prefixEnd_446148 : Nat := 4983230072969 + 3 ^ 40 * 446148 * 2
def baseEnd_446148 : Nat := 50908526009383483910713

theorem tailTrace_446148 : CollatzResearch.WordTrace tailWord_446148 prefixEnd_446148 50908526009383483910713 := by
  unfold tailWord_446148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8136177193844733428617549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10848236258459644571490065 8136177193844733428617549)
  ·
    refine ⟨3051066447691775035731581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8136177193844733428617549 3051066447691775035731581)
    ·
      refine ⟨1144149917884415638399343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3051066447691775035731581 1144149917884415638399343)
      ·
        refine ⟨1716224876826623457599015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144149917884415638399343 1716224876826623457599015)
        ·
          refine ⟨2574337315239935186398523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716224876826623457599015 2574337315239935186398523)
          ·
            refine ⟨3861505972859902779597785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574337315239935186398523 3861505972859902779597785)
            ·
              refine ⟨2896129479644927084698339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861505972859902779597785 2896129479644927084698339)
              ·
                refine ⟨4344194219467390627047509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896129479644927084698339 4344194219467390627047509)
                ·
                  refine ⟨50908526009383483910713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4344194219467390627047509 50908526009383483910713)
                  ·
                    rfl

theorem cell22_446148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_446148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446148 prefixEnd_446148 := by exact prefixLift 446148
  have htrace : WordTrace (prefixWord ++ tailWord_446148) baseStart_446148 baseEnd_446148 := by
    simpa [prefixWord, tailWord_446148, baseEnd_446148] using wordTrace_append hprefix tailTrace_446148
  have hstable : (prefixWord ++ tailWord_446148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446148).length < 2 ^ (prefixWord ++ tailWord_446148).sum := by decide
  have hdescent : baseEnd_446148 < baseStart_446148 := by decide
  rcases family_descends (prefixWord ++ tailWord_446148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446193 : List Nat := [1, 2, 2, 2, 2, 3, 3, 7]
def baseStart_446193 : Nat := 118140960795 + 446193 * 2 ^ 59
def prefixEnd_446193 : Nat := 4983230072969 + 3 ^ 40 * 446193 * 2
def baseEnd_446193 : Nat := 16971220271976148261889

theorem tailTrace_446193 : CollatzResearch.WordTrace tailWord_446193 prefixEnd_446193 16971220271976148261889 := by
  unfold tailWord_446193
  simp only [CollatzResearch.WordTrace]
  refine ⟨16273995672526439542623233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10849330448350959695082155 16273995672526439542623233)
  ·
    refine ⟨12205496754394829656967425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16273995672526439542623233 12205496754394829656967425)
    ·
      refine ⟨9154122565796122242725569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12205496754394829656967425 9154122565796122242725569)
      ·
        refine ⟨6865591924347091682044177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9154122565796122242725569 6865591924347091682044177)
        ·
          refine ⟨5149193943260318761533133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6865591924347091682044177 5149193943260318761533133)
          ·
            refine ⟨1930947728722619535574925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5149193943260318761533133 1930947728722619535574925)
            ·
              refine ⟨724105398270982325840597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1930947728722619535574925 724105398270982325840597)
              ·
                refine ⟨16971220271976148261889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 724105398270982325840597 16971220271976148261889)
                ·
                  rfl

theorem cell22_446193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 7].length) (baseStart_446193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446193 prefixEnd_446193 := by exact prefixLift 446193
  have htrace : WordTrace (prefixWord ++ tailWord_446193) baseStart_446193 baseEnd_446193 := by
    simpa [prefixWord, tailWord_446193, baseEnd_446193] using wordTrace_append hprefix tailTrace_446193
  have hstable : (prefixWord ++ tailWord_446193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446193).length < 2 ^ (prefixWord ++ tailWord_446193).sum := by decide
  have hdescent : baseEnd_446193 < baseStart_446193 := by decide
  rcases family_descends (prefixWord ++ tailWord_446193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446212 : List Nat := [2, 3, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_446212 : Nat := 118140960795 + 446212 * 2 ^ 59
def prefixEnd_446212 : Nat := 4983230072969 + 3 ^ 40 * 446212 * 2
def baseEnd_446212 : Nat := 152747486536075618131943

theorem tailTrace_446212 : CollatzResearch.WordTrace tailWord_446212 prefixEnd_446212 152747486536075618131943 := by
  unfold tailWord_446212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137344329728802893782445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10849792439638403858376593 8137344329728802893782445)
  ·
    refine ⟨3051504123648301085168417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8137344329728802893782445 3051504123648301085168417)
    ·
      refine ⟨2288628092736225813876313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3051504123648301085168417 2288628092736225813876313)
      ·
        refine ⟨1716471069552169360407235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288628092736225813876313 1716471069552169360407235)
        ·
          refine ⟨2574706604328254040610853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716471069552169360407235 2574706604328254040610853)
          ·
            refine ⟨482757488311547632614535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2574706604328254040610853 482757488311547632614535)
            ·
              refine ⟨724136232467321448921803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482757488311547632614535 724136232467321448921803)
              ·
                refine ⟨1086204348700982173382705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724136232467321448921803 1086204348700982173382705)
                ·
                  refine ⟨814653261525736630037029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086204348700982173382705 814653261525736630037029)
                  ·
                    refine ⟨152747486536075618131943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 814653261525736630037029 152747486536075618131943)
                    ·
                      rfl

theorem cell22_446212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_446212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446212 prefixEnd_446212 := by exact prefixLift 446212
  have htrace : WordTrace (prefixWord ++ tailWord_446212) baseStart_446212 baseEnd_446212 := by
    simpa [prefixWord, tailWord_446212, baseEnd_446212] using wordTrace_append hprefix tailTrace_446212
  have hstable : (prefixWord ++ tailWord_446212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446212).length < 2 ^ (prefixWord ++ tailWord_446212).sum := by decide
  have hdescent : baseEnd_446212 < baseStart_446212 := by decide
  rcases family_descends (prefixWord ++ tailWord_446212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446242 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 3, 3]
def baseStart_446242 : Nat := 118140960795 + 446242 * 2 ^ 59
def prefixEnd_446242 : Nat := 4983230072969 + 3 ^ 40 * 446242 * 2
def baseEnd_446242 : Nat := 152757756149165539881851

theorem tailTrace_446242 : CollatzResearch.WordTrace tailWord_446242 prefixEnd_446242 152757756149165539881851 := by
  unfold tailWord_446242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068945712337230227789245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10850521899565947274104653 4068945712337230227789245)
  ·
    refine ⟨1525854642126461335420967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4068945712337230227789245 1525854642126461335420967)
    ·
      refine ⟨2288781963189692003131451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525854642126461335420967 2288781963189692003131451)
      ·
        refine ⟨3433172944784538004697177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288781963189692003131451 3433172944784538004697177)
        ·
          refine ⟨2574879708588403503522883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3433172944784538004697177 2574879708588403503522883)
          ·
            refine ⟨3862319562882605255284325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574879708588403503522883 3862319562882605255284325)
            ·
              refine ⟨724184918040488485365811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3862319562882605255284325 724184918040488485365811)
              ·
                refine ⟨1086277377060732728048717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724184918040488485365811 1086277377060732728048717)
                ·
                  refine ⟨407354016397774773018269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1086277377060732728048717 407354016397774773018269)
                  ·
                    refine ⟨152757756149165539881851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407354016397774773018269 152757756149165539881851)
                    ·
                      rfl

theorem cell22_446242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_446242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446242 prefixEnd_446242 := by exact prefixLift 446242
  have htrace : WordTrace (prefixWord ++ tailWord_446242) baseStart_446242 baseEnd_446242 := by
    simpa [prefixWord, tailWord_446242, baseEnd_446242] using wordTrace_append hprefix tailTrace_446242
  have hstable : (prefixWord ++ tailWord_446242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446242).length < 2 ^ (prefixWord ++ tailWord_446242).sum := by decide
  have hdescent : baseEnd_446242 < baseStart_446242 := by decide
  rcases family_descends (prefixWord ++ tailWord_446242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446313 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_446313 : Nat := 118140960795 + 446313 * 2 ^ 59
def prefixEnd_446313 : Nat := 4983230072969 + 3 ^ 40 * 446313 * 2
def baseEnd_446313 : Nat := 152782060900145021356633

theorem tailTrace_446313 : CollatzResearch.WordTrace tailWord_446313 prefixEnd_446313 152782060900145021356633 := by
  unfold tailWord_446313
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278372432091700036991593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10852248288061133357994395 16278372432091700036991593)
  ·
    refine ⟨12208779324068775027743695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16278372432091700036991593 12208779324068775027743695)
    ·
      refine ⟨18313168986103162541615543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12208779324068775027743695 18313168986103162541615543)
      ·
        refine ⟨27469753479154743812423315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18313168986103162541615543 27469753479154743812423315)
        ·
          refine ⟨41204630218732115718634973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27469753479154743812423315 41204630218732115718634973)
          ·
            refine ⟨15451736332024543394488115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41204630218732115718634973 15451736332024543394488115)
            ·
              refine ⟨23177604498036815091732173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15451736332024543394488115 23177604498036815091732173)
              ·
                refine ⟨8691601686763805659399565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23177604498036815091732173 8691601686763805659399565)
                ·
                  refine ⟨3259350632536427122274837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8691601686763805659399565 3259350632536427122274837)
                  ·
                    refine ⟨152782060900145021356633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3259350632536427122274837 152782060900145021356633)
                    ·
                      rfl

theorem cell22_446313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_446313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446313 prefixEnd_446313 := by exact prefixLift 446313
  have htrace : WordTrace (prefixWord ++ tailWord_446313) baseStart_446313 baseEnd_446313 := by
    simpa [prefixWord, tailWord_446313, baseEnd_446313] using wordTrace_append hprefix tailTrace_446313
  have hstable : (prefixWord ++ tailWord_446313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446313).length < 2 ^ (prefixWord ++ tailWord_446313).sum := by decide
  have hdescent : baseEnd_446313 < baseStart_446313 := by decide
  rcases family_descends (prefixWord ++ tailWord_446313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446330 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_446330 : Nat := 118140960795 + 446330 * 2 ^ 59
def prefixEnd_446330 : Nat := 4983230072969 + 3 ^ 40 * 446330 * 2
def baseEnd_446330 : Nat := 152787880347562643681581

theorem tailTrace_446330 : CollatzResearch.WordTrace tailWord_446330 prefixEnd_446330 152787880347562643681581 := by
  unfold tailWord_446330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069748118257527985090111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10852661648686741293573629 4069748118257527985090111)
  ·
    refine ⟨6104622177386291977635167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069748118257527985090111 6104622177386291977635167)
    ·
      refine ⟨9156933266079437966452751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104622177386291977635167 9156933266079437966452751)
      ·
        refine ⟨13735399899119156949679127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9156933266079437966452751 13735399899119156949679127)
        ·
          refine ⟨20603099848678735424518691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13735399899119156949679127 20603099848678735424518691)
          ·
            refine ⟨30904649773018103136778037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20603099848678735424518691 30904649773018103136778037)
            ·
              refine ⟨2897310916220447169072941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30904649773018103136778037 2897310916220447169072941)
              ·
                refine ⟨1086491593582667688402353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897310916220447169072941 1086491593582667688402353)
                ·
                  refine ⟨814868695187000766301765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1086491593582667688402353 814868695187000766301765)
                  ·
                    refine ⟨152787880347562643681581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 814868695187000766301765 152787880347562643681581)
                    ·
                      rfl

theorem cell22_446330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_446330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446330 prefixEnd_446330 := by exact prefixLift 446330
  have htrace : WordTrace (prefixWord ++ tailWord_446330) baseStart_446330 baseEnd_446330 := by
    simpa [prefixWord, tailWord_446330, baseEnd_446330] using wordTrace_append hprefix tailTrace_446330
  have hstable : (prefixWord ++ tailWord_446330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446330).length < 2 ^ (prefixWord ++ tailWord_446330).sum := by decide
  have hdescent : baseEnd_446330 < baseStart_446330 := by decide
  rcases family_descends (prefixWord ++ tailWord_446330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446362 : List Nat := [3, 1, 1, 4, 2, 3, 1, 7]
def baseStart_446362 : Nat := 118140960795 + 446362 * 2 ^ 59
def prefixEnd_446362 : Nat := 4983230072969 + 3 ^ 40 * 446362 * 2
def baseEnd_446362 : Nat := 16977648289058358542387

theorem tailTrace_446362 : CollatzResearch.WordTrace tailWord_446362 prefixEnd_446362 16977648289058358542387 := by
  unfold tailWord_446362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070039902228545351381335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10853439739276120937016893 4070039902228545351381335)
  ·
    refine ⟨6105059853342818027072003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4070039902228545351381335 6105059853342818027072003)
    ·
      refine ⟨9157589780014227040608005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105059853342818027072003 9157589780014227040608005)
      ·
        refine ⟨1717048083752667570114001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9157589780014227040608005 1717048083752667570114001)
        ·
          refine ⟨1287786062814500677585501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717048083752667570114001 1287786062814500677585501)
          ·
            refine ⟨482919773555437754094563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1287786062814500677585501 482919773555437754094563)
            ·
              refine ⟨724379660333156631141845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482919773555437754094563 724379660333156631141845)
              ·
                refine ⟨16977648289058358542387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 724379660333156631141845 16977648289058358542387)
                ·
                  rfl

theorem cell22_446362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_446362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446362 prefixEnd_446362 := by exact prefixLift 446362
  have htrace : WordTrace (prefixWord ++ tailWord_446362) baseStart_446362 baseEnd_446362 := by
    simpa [prefixWord, tailWord_446362, baseEnd_446362] using wordTrace_append hprefix tailTrace_446362
  have hstable : (prefixWord ++ tailWord_446362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446362).length < 2 ^ (prefixWord ++ tailWord_446362).sum := by decide
  have hdescent : baseEnd_446362 < baseStart_446362 := by decide
  rcases family_descends (prefixWord ++ tailWord_446362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446366 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_446366 : Nat := 118140960795 + 446366 * 2 ^ 59
def prefixEnd_446366 : Nat := 4983230072969 + 3 ^ 40 * 446366 * 2
def baseEnd_446366 : Nat := 152800203883270549781471

theorem tailTrace_446366 : CollatzResearch.WordTrace tailWord_446366 prefixEnd_446366 152800203883270549781471 := by
  unfold tailWord_446366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035038187612461261083869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10853537000599793392447301 2035038187612461261083869)
  ·
    refine ⟨763139320354672972906451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2035038187612461261083869 763139320354672972906451)
    ·
      refine ⟨1144708980532009459359677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763139320354672972906451 1144708980532009459359677)
      ·
        refine ⟨429265867699503547259879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1144708980532009459359677 429265867699503547259879)
        ·
          refine ⟨643898801549255320889819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429265867699503547259879 643898801549255320889819)
          ·
            refine ⟨965848202323882981334729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643898801549255320889819 965848202323882981334729)
            ·
              refine ⟨724386151742912236001047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 965848202323882981334729 724386151742912236001047)
              ·
                refine ⟨1086579227614368354001571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724386151742912236001047 1086579227614368354001571)
                ·
                  refine ⟨1629868841421552531002357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086579227614368354001571 1629868841421552531002357)
                  ·
                    refine ⟨152800203883270549781471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1629868841421552531002357 152800203883270549781471)
                    ·
                      rfl

theorem cell22_446366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_446366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446366 prefixEnd_446366 := by exact prefixLift 446366
  have htrace : WordTrace (prefixWord ++ tailWord_446366) baseStart_446366 baseEnd_446366 := by
    simpa [prefixWord, tailWord_446366, baseEnd_446366] using wordTrace_append hprefix tailTrace_446366
  have hstable : (prefixWord ++ tailWord_446366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446366).length < 2 ^ (prefixWord ++ tailWord_446366).sum := by decide
  have hdescent : baseEnd_446366 < baseStart_446366 := by decide
  rcases family_descends (prefixWord ++ tailWord_446366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446445 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_446445 : Nat := 118140960795 + 446445 * 2 ^ 59
def prefixEnd_446445 : Nat := 4983230072969 + 3 ^ 40 * 446445 * 2
def baseEnd_446445 : Nat := 152827247197740677056229

theorem tailTrace_446445 : CollatzResearch.WordTrace tailWord_446445 prefixEnd_446445 152827247197740677056229 := by
  unfold tailWord_446445
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283186867613486580796789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10855457911742324387197859 16283186867613486580796789)
  ·
    refine ⟨1526548768838764366949699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16283186867613486580796789 1526548768838764366949699)
    ·
      refine ⟨2289823153258146550424549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526548768838764366949699 2289823153258146550424549)
      ·
        refine ⟨429341841235902478204603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2289823153258146550424549 429341841235902478204603)
        ·
          refine ⟨644012761853853717306905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429341841235902478204603 644012761853853717306905)
          ·
            refine ⟨483009571390390287980179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644012761853853717306905 483009571390390287980179)
            ·
              refine ⟨724514357085585431970269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483009571390390287980179 724514357085585431970269)
              ·
                refine ⟨271692883907094536988851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724514357085585431970269 271692883907094536988851)
                ·
                  refine ⟨407539325860641805483277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271692883907094536988851 407539325860641805483277)
                  ·
                    refine ⟨152827247197740677056229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407539325860641805483277 152827247197740677056229)
                    ·
                      rfl

theorem cell22_446445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_446445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446445 prefixEnd_446445 := by exact prefixLift 446445
  have htrace : WordTrace (prefixWord ++ tailWord_446445) baseStart_446445 baseEnd_446445 := by
    simpa [prefixWord, tailWord_446445, baseEnd_446445] using wordTrace_append hprefix tailTrace_446445
  have hstable : (prefixWord ++ tailWord_446445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446445).length < 2 ^ (prefixWord ++ tailWord_446445).sum := by decide
  have hdescent : baseEnd_446445 < baseStart_446445 := by decide
  rcases family_descends (prefixWord ++ tailWord_446445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446546 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 3, 3]
def baseStart_446546 : Nat := 118140960795 + 446546 * 2 ^ 59
def prefixEnd_446546 : Nat := 4983230072969 + 3 ^ 40 * 446546 * 2
def baseEnd_446546 : Nat := 152861821561810080280919

theorem tailTrace_446546 : CollatzResearch.WordTrace tailWord_446546 prefixEnd_446546 152861821561810080280919 := by
  unfold tailWord_446546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071717660061895207555873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10857913760165053886815661 4071717660061895207555873)
  ·
    refine ⟨3053788245046421405666905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4071717660061895207555873 3053788245046421405666905)
    ·
      refine ⟨2290341183784816054250179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053788245046421405666905 2290341183784816054250179)
      ·
        refine ⟨3435511775677224081375269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290341183784816054250179 3435511775677224081375269)
        ·
          refine ⟨644158457939479515257863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3435511775677224081375269 644158457939479515257863)
          ·
            refine ⟨966237686909219272886795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644158457939479515257863 966237686909219272886795)
            ·
              refine ⟨1449356530363828909330193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966237686909219272886795 1449356530363828909330193)
              ·
                refine ⟨1087017397772871681997645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449356530363828909330193 1087017397772871681997645)
                ·
                  refine ⟨407631524164826880749117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1087017397772871681997645 407631524164826880749117)
                  ·
                    refine ⟨152861821561810080280919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407631524164826880749117 152861821561810080280919)
                    ·
                      rfl

theorem cell22_446546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_446546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446546 prefixEnd_446546 := by exact prefixLift 446546
  have htrace : WordTrace (prefixWord ++ tailWord_446546) baseStart_446546 baseEnd_446546 := by
    simpa [prefixWord, tailWord_446546, baseEnd_446546] using wordTrace_append hprefix tailTrace_446546
  have hstable : (prefixWord ++ tailWord_446546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446546).length < 2 ^ (prefixWord ++ tailWord_446546).sum := by decide
  have hdescent : baseEnd_446546 < baseStart_446546 := by decide
  rcases family_descends (prefixWord ++ tailWord_446546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446617 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_446617 : Nat := 118140960795 + 446617 * 2 ^ 59
def prefixEnd_446617 : Nat := 4983230072969 + 3 ^ 40 * 446617 * 2
def baseEnd_446617 : Nat := 152886126312789561755701

theorem tailTrace_446617 : CollatzResearch.WordTrace tailWord_446617 prefixEnd_446617 152886126312789561755701 := by
  unfold tailWord_446617
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289460222990359956058105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10859640148660239970705403 16289460222990359956058105)
  ·
    refine ⟨12217095167242769967043579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16289460222990359956058105 12217095167242769967043579)
    ·
      refine ⟨18325642750864154950565369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217095167242769967043579 18325642750864154950565369)
      ·
        refine ⟨13744232063148116212924027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18325642750864154950565369 13744232063148116212924027)
        ·
          refine ⟨20616348094722174319386041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13744232063148116212924027 20616348094722174319386041)
          ·
            refine ⟨15462261071041630739539531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20616348094722174319386041 15462261071041630739539531)
            ·
              refine ⟨23193391606562446109309297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15462261071041630739539531 23193391606562446109309297)
              ·
                refine ⟨17395043704921834581981973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23193391606562446109309297 17395043704921834581981973)
                ·
                  refine ⟨815392673668210996030405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17395043704921834581981973 815392673668210996030405)
                  ·
                    refine ⟨152886126312789561755701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815392673668210996030405 152886126312789561755701)
                    ·
                      rfl

theorem cell22_446617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_446617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446617 prefixEnd_446617 := by exact prefixLift 446617
  have htrace : WordTrace (prefixWord ++ tailWord_446617) baseStart_446617 baseEnd_446617 := by
    simpa [prefixWord, tailWord_446617, baseEnd_446617] using wordTrace_append hprefix tailTrace_446617
  have hstable : (prefixWord ++ tailWord_446617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446617).length < 2 ^ (prefixWord ++ tailWord_446617).sum := by decide
  have hdescent : baseEnd_446617 < baseStart_446617 := by decide
  rcases family_descends (prefixWord ++ tailWord_446617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446621 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 4]
def baseStart_446621 : Nat := 118140960795 + 446621 * 2 ^ 59
def prefixEnd_446621 : Nat := 4983230072969 + 3 ^ 40 * 446621 * 2
def baseEnd_446621 : Nat := 50962498531511628218563

theorem tailTrace_446621 : CollatzResearch.WordTrace tailWord_446621 prefixEnd_446621 50962498531511628218563 := by
  unfold tailWord_446621
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289606114975868639203717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10859737409983912426135811 16289606114975868639203717)
  ·
    refine ⟨3054301146557975369850697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16289606114975868639203717 3054301146557975369850697)
    ·
      refine ⟨2290725859918481527388023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3054301146557975369850697 2290725859918481527388023)
      ·
        refine ⟨3436088789877722291082035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2290725859918481527388023 3436088789877722291082035)
        ·
          refine ⟨5154133184816583436623053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436088789877722291082035 5154133184816583436623053)
          ·
            refine ⟨1932799944306218788733645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5154133184816583436623053 1932799944306218788733645)
            ·
              refine ⟨724799979114832045775117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1932799944306218788733645 724799979114832045775117)
              ·
                refine ⟨271799992168062017165669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724799979114832045775117 271799992168062017165669)
                ·
                  refine ⟨50962498531511628218563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271799992168062017165669 50962498531511628218563)
                  ·
                    rfl

theorem cell22_446621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_446621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446621 prefixEnd_446621 := by exact prefixLift 446621
  have htrace : WordTrace (prefixWord ++ tailWord_446621) baseStart_446621 baseEnd_446621 := by
    simpa [prefixWord, tailWord_446621, baseEnd_446621] using wordTrace_append hprefix tailTrace_446621
  have hstable : (prefixWord ++ tailWord_446621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446621).length < 2 ^ (prefixWord ++ tailWord_446621).sum := by decide
  have hdescent : baseEnd_446621 < baseStart_446621 := by decide
  rcases family_descends (prefixWord ++ tailWord_446621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446644 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 5]
def baseStart_446644 : Nat := 118140960795 + 446644 * 2 ^ 59
def prefixEnd_446644 : Nat := 4983230072969 + 3 ^ 40 * 446644 * 2
def baseEnd_446644 : Nat := 50965122988190163776873

theorem tailTrace_446644 : CollatzResearch.WordTrace tailWord_446644 prefixEnd_446644 50965122988190163776873 := by
  unfold tailWord_446644
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145222496946271783645493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10860296662595029044860657 8145222496946271783645493)
  ·
    refine ⟨763614609088712979716765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8145222496946271783645493 763614609088712979716765)
    ·
      refine ⟨286355478408267367393787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 763614609088712979716765 286355478408267367393787)
      ·
        refine ⟨429533217612401051090681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286355478408267367393787 429533217612401051090681)
        ·
          refine ⟨322149913209300788318011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429533217612401051090681 322149913209300788318011)
          ·
            refine ⟨483224869813951182477017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322149913209300788318011 483224869813951182477017)
            ·
              refine ⟨362418652360463386857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483224869813951182477017 362418652360463386857763)
              ·
                refine ⟨543627978540695080286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362418652360463386857763 543627978540695080286645)
                ·
                  refine ⟨50965122988190163776873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 543627978540695080286645 50965122988190163776873)
                  ·
                    rfl

theorem cell22_446644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_446644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446644 prefixEnd_446644 := by exact prefixLift 446644
  have htrace : WordTrace (prefixWord ++ tailWord_446644) baseStart_446644 baseEnd_446644 := by
    simpa [prefixWord, tailWord_446644, baseEnd_446644] using wordTrace_append hprefix tailTrace_446644
  have hstable : (prefixWord ++ tailWord_446644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446644).length < 2 ^ (prefixWord ++ tailWord_446644).sum := by decide
  have hdescent : baseEnd_446644 < baseStart_446644 := by decide
  rcases family_descends (prefixWord ++ tailWord_446644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446664 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_446664 : Nat := 118140960795 + 446664 * 2 ^ 59
def prefixEnd_446664 : Nat := 4983230072969 + 3 ^ 40 * 446664 * 2
def baseEnd_446664 : Nat := 152902215373297105830557

theorem tailTrace_446664 : CollatzResearch.WordTrace tailWord_446664 prefixEnd_446664 152902215373297105830557 := by
  unfold tailWord_446664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145587226910043491509523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10860782969213391322012697 8145587226910043491509523)
  ·
    refine ⟨12218380840365065237264285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8145587226910043491509523 12218380840365065237264285)
    ·
      refine ⟨4581892815136899463974107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12218380840365065237264285 4581892815136899463974107)
      ·
        refine ⟨6872839222705349195961161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4581892815136899463974107 6872839222705349195961161)
        ·
          refine ⟨5154629417029011896970871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6872839222705349195961161 5154629417029011896970871)
          ·
            refine ⟨7731944125543517845456307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154629417029011896970871 7731944125543517845456307)
            ·
              refine ⟨11597916188315276768184461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7731944125543517845456307 11597916188315276768184461)
              ·
                refine ⟨4349218570618228788069173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11597916188315276768184461 4349218570618228788069173)
                ·
                  refine ⟨407739240995458948881485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4349218570618228788069173 407739240995458948881485)
                  ·
                    refine ⟨152902215373297105830557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407739240995458948881485 152902215373297105830557)
                    ·
                      rfl

theorem cell22_446664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_446664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446664 prefixEnd_446664 := by exact prefixLift 446664
  have htrace : WordTrace (prefixWord ++ tailWord_446664) baseStart_446664 baseEnd_446664 := by
    simpa [prefixWord, tailWord_446664, baseEnd_446664] using wordTrace_append hprefix tailTrace_446664
  have hstable : (prefixWord ++ tailWord_446664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446664).length < 2 ^ (prefixWord ++ tailWord_446664).sum := by decide
  have hdescent : baseEnd_446664 < baseStart_446664 := by decide
  rcases family_descends (prefixWord ++ tailWord_446664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446668 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_446668 : Nat := 118140960795 + 446668 * 2 ^ 59
def prefixEnd_446668 : Nat := 4983230072969 + 3 ^ 40 * 446668 * 2
def baseEnd_446668 : Nat := 152903584655042428730545

theorem tailTrace_446668 : CollatzResearch.WordTrace tailWord_446668 prefixEnd_446668 152903584655042428730545 := by
  unfold tailWord_446668
  simp only [CollatzResearch.WordTrace]
  refine ⟨8145660172902797833082329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10860880230537063777443105 8145660172902797833082329)
  ·
    refine ⟨6109245129677098374811747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8145660172902797833082329 6109245129677098374811747)
    ·
      refine ⟨9163867694515647562217621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109245129677098374811747 9163867694515647562217621)
      ·
        refine ⟨429556298180420979478951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9163867694515647562217621 429556298180420979478951)
        ·
          refine ⟨644334447270631469218427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429556298180420979478951 644334447270631469218427)
          ·
            refine ⟨966501670905947203827641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644334447270631469218427 966501670905947203827641)
            ·
              refine ⟨724876253179460402870731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966501670905947203827641 724876253179460402870731)
              ·
                refine ⟨1087314379769190604306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724876253179460402870731 1087314379769190604306097)
                ·
                  refine ⟨815485784826892953229573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087314379769190604306097 815485784826892953229573)
                  ·
                    refine ⟨152903584655042428730545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815485784826892953229573 152903584655042428730545)
                    ·
                      rfl

theorem cell22_446668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_446668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446668 prefixEnd_446668 := by exact prefixLift 446668
  have htrace : WordTrace (prefixWord ++ tailWord_446668) baseStart_446668 baseEnd_446668 := by
    simpa [prefixWord, tailWord_446668, baseEnd_446668] using wordTrace_append hprefix tailTrace_446668
  have hstable : (prefixWord ++ tailWord_446668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446668).length < 2 ^ (prefixWord ++ tailWord_446668).sum := by decide
  have hdescent : baseEnd_446668 < baseStart_446668 := by decide
  rcases family_descends (prefixWord ++ tailWord_446668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446698 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 1, 3]
def baseStart_446698 : Nat := 118140960795 + 446698 * 2 ^ 59
def prefixEnd_446698 : Nat := 4983230072969 + 3 ^ 40 * 446698 * 2
def baseEnd_446698 : Nat := 152913854268132350480453

theorem tailTrace_446698 : CollatzResearch.WordTrace tailWord_446698 prefixEnd_446698 152913854268132350480453 := by
  unfold tailWord_446698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073103633924227697439187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10861609690464607193171165 4073103633924227697439187)
  ·
    refine ⟨6109655450886341546158781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4073103633924227697439187 6109655450886341546158781)
    ·
      refine ⟨2291120794082378079809543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6109655450886341546158781 2291120794082378079809543)
      ·
        refine ⟨3436681191123567119714315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291120794082378079809543 3436681191123567119714315)
        ·
          refine ⟨5155021786685350679571473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436681191123567119714315 5155021786685350679571473)
          ·
            refine ⟨3866266340014013009678605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155021786685350679571473 3866266340014013009678605)
            ·
              refine ⟨1449849877505254878629477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3866266340014013009678605 1449849877505254878629477)
              ·
                refine ⟨271846852032235289743027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1449849877505254878629477 271846852032235289743027)
                ·
                  refine ⟨407770278048352934614541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271846852032235289743027 407770278048352934614541)
                  ·
                    refine ⟨152913854268132350480453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407770278048352934614541 152913854268132350480453)
                    ·
                      rfl

theorem cell22_446698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_446698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446698 prefixEnd_446698 := by exact prefixLift 446698
  have htrace : WordTrace (prefixWord ++ tailWord_446698) baseStart_446698 baseEnd_446698 := by
    simpa [prefixWord, tailWord_446698, baseEnd_446698] using wordTrace_append hprefix tailTrace_446698
  have hstable : (prefixWord ++ tailWord_446698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446698).length < 2 ^ (prefixWord ++ tailWord_446698).sum := by decide
  have hdescent : baseEnd_446698 < baseStart_446698 := by decide
  rcases family_descends (prefixWord ++ tailWord_446698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446756 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 6]
def baseStart_446756 : Nat := 118140960795 + 446756 * 2 ^ 59
def prefixEnd_446756 : Nat := 4983230072969 + 3 ^ 40 * 446756 * 2
def baseEnd_446756 : Nat := 50977902951146510843425

theorem tailTrace_446756 : CollatzResearch.WordTrace tailWord_446756 prefixEnd_446756 50977902951146510843425 := by
  unfold tailWord_446756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147264984743393347684061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10863019979657857796912081 8147264984743393347684061)
  ·
    refine ⟨3055224369278772505381523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8147264984743393347684061 3055224369278772505381523)
    ·
      refine ⟨4582836553918158758072285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055224369278772505381523 4582836553918158758072285)
      ·
        refine ⟨1718563707719309534277107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4582836553918158758072285 1718563707719309534277107)
        ·
          refine ⟨2577845561578964301415661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1718563707719309534277107 2577845561578964301415661)
          ·
            refine ⟨966692085592111613030873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2577845561578964301415661 966692085592111613030873)
            ·
              refine ⟨725019064194083709773155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966692085592111613030873 725019064194083709773155)
              ·
                refine ⟨1087528596291125564659733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725019064194083709773155 1087528596291125564659733)
                ·
                  refine ⟨50977902951146510843425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1087528596291125564659733 50977902951146510843425)
                  ·
                    rfl

theorem cell22_446756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_446756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446756 prefixEnd_446756 := by exact prefixLift 446756
  have htrace : WordTrace (prefixWord ++ tailWord_446756) baseStart_446756 baseEnd_446756 := by
    simpa [prefixWord, tailWord_446756, baseEnd_446756] using wordTrace_append hprefix tailTrace_446756
  have hstable : (prefixWord ++ tailWord_446756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446756).length < 2 ^ (prefixWord ++ tailWord_446756).sum := by decide
  have hdescent : baseEnd_446756 < baseStart_446756 := by decide
  rcases family_descends (prefixWord ++ tailWord_446756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446844 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_446844 : Nat := 118140960795 + 446844 * 2 ^ 59
def prefixEnd_446844 : Nat := 4983230072969 + 3 ^ 40 * 446844 * 2
def baseEnd_446844 : Nat := 152963833051836636330005

theorem tailTrace_446844 : CollatzResearch.WordTrace tailWord_446844 prefixEnd_446844 152963833051836636330005 := by
  unfold tailWord_446844
  simp only [CollatzResearch.WordTrace]
  refine ⟨8148869796583988862285793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10865159728778651816381057 8148869796583988862285793)
  ·
    refine ⟨6111652347437991646714345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8148869796583988862285793 6111652347437991646714345)
    ·
      refine ⟨4583739260578493735035759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6111652347437991646714345 4583739260578493735035759)
      ·
        refine ⟨6875608890867740602553639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583739260578493735035759 6875608890867740602553639)
        ·
          refine ⟨10313413336301610903830459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6875608890867740602553639 10313413336301610903830459)
          ·
            refine ⟨15470120004452416355745689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10313413336301610903830459 15470120004452416355745689)
            ·
              refine ⟨11602590003339312266809267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15470120004452416355745689 11602590003339312266809267)
              ·
                refine ⟨17403885005008968400213901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11602590003339312266809267 17403885005008968400213901)
                ·
                  refine ⟨6526456876878363150080213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17403885005008968400213901 6526456876878363150080213)
                  ·
                    refine ⟨152963833051836636330005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6526456876878363150080213 152963833051836636330005)
                    ·
                      rfl

theorem cell22_446844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_446844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446844 prefixEnd_446844 := by exact prefixLift 446844
  have htrace : WordTrace (prefixWord ++ tailWord_446844) baseStart_446844 baseEnd_446844 := by
    simpa [prefixWord, tailWord_446844, baseEnd_446844] using wordTrace_append hprefix tailTrace_446844
  have hstable : (prefixWord ++ tailWord_446844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446844).length < 2 ^ (prefixWord ++ tailWord_446844).sum := by decide
  have hdescent : baseEnd_446844 < baseStart_446844 := by decide
  rcases family_descends (prefixWord ++ tailWord_446844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446878 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_446878 : Nat := 118140960795 + 446878 * 2 ^ 59
def prefixEnd_446878 : Nat := 4983230072969 + 3 ^ 40 * 446878 * 2
def baseEnd_446878 : Nat := 152975471946671880979901

theorem tailTrace_446878 : CollatzResearch.WordTrace tailWord_446878 prefixEnd_446878 152975471946671880979901 := by
  unfold tailWord_446878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037372459380600191413661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10865986450029867687539525 2037372459380600191413661)
  ·
    refine ⟨764014672267725071780123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2037372459380600191413661 764014672267725071780123)
    ·
      refine ⟨1146022008401587607670185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764014672267725071780123 1146022008401587607670185)
      ·
        refine ⟨859516506301190705752639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146022008401587607670185 859516506301190705752639)
        ·
          refine ⟨1289274759451786058628959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859516506301190705752639 1289274759451786058628959)
          ·
            refine ⟨1933912139177679087943439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1289274759451786058628959 1933912139177679087943439)
            ·
              refine ⟨2900868208766518631915159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933912139177679087943439 2900868208766518631915159)
              ·
                refine ⟨4351302313149777947872739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2900868208766518631915159 4351302313149777947872739)
                ·
                  refine ⟨6526953469724666921809109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4351302313149777947872739 6526953469724666921809109)
                  ·
                    refine ⟨152975471946671880979901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6526953469724666921809109 152975471946671880979901)
                    ·
                      rfl

theorem cell22_446878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_446878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446878 prefixEnd_446878 := by exact prefixLift 446878
  have htrace : WordTrace (prefixWord ++ tailWord_446878) baseStart_446878 baseEnd_446878 := by
    simpa [prefixWord, tailWord_446878, baseEnd_446878] using wordTrace_append hprefix tailTrace_446878
  have hstable : (prefixWord ++ tailWord_446878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446878).length < 2 ^ (prefixWord ++ tailWord_446878).sum := by decide
  have hdescent : baseEnd_446878 < baseStart_446878 := by decide
  rcases family_descends (prefixWord ++ tailWord_446878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446910 : List Nat := [4, 2, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_446910 : Nat := 118140960795 + 446910 * 2 ^ 59
def prefixEnd_446910 : Nat := 4983230072969 + 3 ^ 40 * 446910 * 2
def baseEnd_446910 : Nat := 152986426200634464179803

theorem tailTrace_446910 : CollatzResearch.WordTrace tailWord_446910 prefixEnd_446910 152986426200634464179803 := by
  unfold tailWord_446910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037518351366108874559273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10866764540619247330982789 2037518351366108874559273)
  ·
    refine ⟨1528138763524581655919455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2037518351366108874559273 1528138763524581655919455)
    ·
      refine ⟨2292208145286872483879183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528138763524581655919455 2292208145286872483879183)
      ·
        refine ⟨3438312217930308725818775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2292208145286872483879183 3438312217930308725818775)
        ·
          refine ⟨5157468326895463088728163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3438312217930308725818775 5157468326895463088728163)
          ·
            refine ⟨7736202490343194633092245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5157468326895463088728163 7736202490343194633092245)
            ·
              refine ⟨362634491734837248426199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7736202490343194633092245 362634491734837248426199)
              ·
                refine ⟨543951737602255872639299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362634491734837248426199 543951737602255872639299)
                ·
                  refine ⟨815927606403383808958949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543951737602255872639299 815927606403383808958949)
                  ·
                    refine ⟨152986426200634464179803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815927606403383808958949 152986426200634464179803)
                    ·
                      rfl

theorem cell22_446910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_446910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446910 prefixEnd_446910 := by exact prefixLift 446910
  have htrace : WordTrace (prefixWord ++ tailWord_446910) baseStart_446910 baseEnd_446910 := by
    simpa [prefixWord, tailWord_446910, baseEnd_446910] using wordTrace_append hprefix tailTrace_446910
  have hstable : (prefixWord ++ tailWord_446910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446910).length < 2 ^ (prefixWord ++ tailWord_446910).sum := by decide
  have hdescent : baseEnd_446910 < baseStart_446910 := by decide
  rcases family_descends (prefixWord ++ tailWord_446910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446921 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_446921 : Nat := 118140960795 + 446921 * 2 ^ 59
def prefixEnd_446921 : Nat := 4983230072969 + 3 ^ 40 * 446921 * 2
def baseEnd_446921 : Nat := 152990191725434102154769

theorem tailTrace_446921 : CollatzResearch.WordTrace tailWord_446921 prefixEnd_446921 152990191725434102154769 := by
  unfold tailWord_446921
  simp only [CollatzResearch.WordTrace]
  refine ⟨16300548013889019875124617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10867032009259346583416411 16300548013889019875124617)
  ·
    refine ⟨12225411010416764906343463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16300548013889019875124617 12225411010416764906343463)
    ·
      refine ⟨18338116515625147359515195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12225411010416764906343463 18338116515625147359515195)
      ·
        refine ⟨27507174773437721039272793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18338116515625147359515195 27507174773437721039272793)
        ·
          refine ⟨20630381080078290779454595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27507174773437721039272793 20630381080078290779454595)
          ·
            refine ⟨30945571620117436169181893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20630381080078290779454595 30945571620117436169181893)
            ·
              refine ⟨5802294678772019281721605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30945571620117436169181893 5802294678772019281721605)
              ·
                refine ⟨1087930252269753615322801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5802294678772019281721605 1087930252269753615322801)
                ·
                  refine ⟨815947689202315211492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087930252269753615322801 815947689202315211492101)
                  ·
                    refine ⟨152990191725434102154769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 815947689202315211492101 152990191725434102154769)
                    ·
                      rfl

theorem cell22_446921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_446921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446921 prefixEnd_446921 := by exact prefixLift 446921
  have htrace : WordTrace (prefixWord ++ tailWord_446921) baseStart_446921 baseEnd_446921 := by
    simpa [prefixWord, tailWord_446921, baseEnd_446921] using wordTrace_append hprefix tailTrace_446921
  have hstable : (prefixWord ++ tailWord_446921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446921).length < 2 ^ (prefixWord ++ tailWord_446921).sum := by decide
  have hdescent : baseEnd_446921 < baseStart_446921 := by decide
  rcases family_descends (prefixWord ++ tailWord_446921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446951 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 7]
def baseStart_446951 : Nat := 118140960795 + 446951 * 2 ^ 59
def prefixEnd_446951 : Nat := 4983230072969 + 3 ^ 40 * 446951 * 2
def baseEnd_446951 : Nat := 153000461338524023904677

theorem tailTrace_446951 : CollatzResearch.WordTrace tailWord_446951 prefixEnd_446951 153000461338524023904677 := by
  unfold tailWord_446951
  simp only [CollatzResearch.WordTrace]
  refine ⟨16301642203780334998716707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10867761469186889999144471 16301642203780334998716707)
  ·
    refine ⟨24452463305670502498075061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16301642203780334998716707 24452463305670502498075061)
    ·
      refine ⟨2292418434906609609194537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24452463305670502498075061 2292418434906609609194537)
      ·
        refine ⟨1719313826179957206895903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2292418434906609609194537 1719313826179957206895903)
        ·
          refine ⟨2578970739269935810343855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719313826179957206895903 2578970739269935810343855)
          ·
            refine ⟨3868456108904903715515783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2578970739269935810343855 3868456108904903715515783)
            ·
              refine ⟨5802684163357355573273675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3868456108904903715515783 5802684163357355573273675)
              ·
                refine ⟨8704026245036033359910513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5802684163357355573273675 8704026245036033359910513)
                ·
                  refine ⟨6528019683777025019932885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8704026245036033359910513 6528019683777025019932885)
                  ·
                    refine ⟨153000461338524023904677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6528019683777025019932885 153000461338524023904677)
                    ·
                      rfl

theorem cell22_446951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_446951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446951 prefixEnd_446951 := by exact prefixLift 446951
  have htrace : WordTrace (prefixWord ++ tailWord_446951) baseStart_446951 baseEnd_446951 := by
    simpa [prefixWord, tailWord_446951, baseEnd_446951] using wordTrace_append hprefix tailTrace_446951
  have hstable : (prefixWord ++ tailWord_446951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446951).length < 2 ^ (prefixWord ++ tailWord_446951).sum := by decide
  have hdescent : baseEnd_446951 < baseStart_446951 := by decide
  rcases family_descends (prefixWord ++ tailWord_446951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_446981 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 7]
def baseStart_446981 : Nat := 118140960795 + 446981 * 2 ^ 59
def prefixEnd_446981 : Nat := 4983230072969 + 3 ^ 40 * 446981 * 2
def baseEnd_446981 : Nat := 51003576983871315218195

theorem tailTrace_446981 : CollatzResearch.WordTrace tailWord_446981 prefixEnd_446981 51003576983871315218195 := by
  unfold tailWord_446981
  simp only [CollatzResearch.WordTrace]
  refine ⟨16302736393671650122308797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10868490929114433414872531 16302736393671650122308797)
  ·
    refine ⟨6113526147626868795865799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16302736393671650122308797 6113526147626868795865799)
    ·
      refine ⟨9170289221440303193798699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6113526147626868795865799 9170289221440303193798699)
      ·
        refine ⟨13755433832160454790698049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9170289221440303193798699 13755433832160454790698049)
        ·
          refine ⟨10316575374120341093023537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13755433832160454790698049 10316575374120341093023537)
          ·
            refine ⟨7737431530590255819767653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10316575374120341093023537 7737431530590255819767653)
            ·
              refine ⟨1450768411985672966206435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7737431530590255819767653 1450768411985672966206435)
              ·
                refine ⟨2176152617978509449309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450768411985672966206435 2176152617978509449309653)
                ·
                  refine ⟨51003576983871315218195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2176152617978509449309653 51003576983871315218195)
                  ·
                    rfl

theorem cell22_446981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_446981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_446981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_446981 prefixEnd_446981 := by exact prefixLift 446981
  have htrace : WordTrace (prefixWord ++ tailWord_446981) baseStart_446981 baseEnd_446981 := by
    simpa [prefixWord, tailWord_446981, baseEnd_446981] using wordTrace_append hprefix tailTrace_446981
  have hstable : (prefixWord ++ tailWord_446981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_446981).length < 2 ^ (prefixWord ++ tailWord_446981).sum := by decide
  have hdescent : baseEnd_446981 < baseStart_446981 := by decide
  rcases family_descends (prefixWord ++ tailWord_446981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447071 : List Nat := [1, 1, 2, 3, 1, 1, 1, 12]
def baseStart_447071 : Nat := 118140960795 + 447071 * 2 ^ 59
def prefixEnd_447071 : Nat := 4983230072969 + 3 ^ 40 * 447071 * 2
def baseEnd_447071 : Nat := 17004615532320412322701

theorem tailTrace_447071 : CollatzResearch.WordTrace tailWord_447071 prefixEnd_447071 17004615532320412322701 := by
  unfold tailWord_447071
  simp only [CollatzResearch.WordTrace]
  refine ⟨16306018963345595493085067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10870679308897063662056711 16306018963345595493085067)
  ·
    refine ⟨24459028445018393239627601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16306018963345595493085067 24459028445018393239627601)
    ·
      refine ⟨18344271333763794929720701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24459028445018393239627601 18344271333763794929720701)
      ·
        refine ⟨6879101750161423098645263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18344271333763794929720701 6879101750161423098645263)
        ·
          refine ⟨10318652625242134647967895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879101750161423098645263 10318652625242134647967895)
          ·
            refine ⟨15477978937863201971951843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10318652625242134647967895 15477978937863201971951843)
            ·
              refine ⟨23216968406794802957927765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15477978937863201971951843 23216968406794802957927765)
              ·
                refine ⟨17004615532320412322701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 23216968406794802957927765 17004615532320412322701)
                ·
                  rfl

theorem cell22_447071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 12].length) (baseStart_447071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447071 prefixEnd_447071 := by exact prefixLift 447071
  have htrace : WordTrace (prefixWord ++ tailWord_447071) baseStart_447071 baseEnd_447071 := by
    simpa [prefixWord, tailWord_447071, baseEnd_447071] using wordTrace_append hprefix tailTrace_447071
  have hstable : (prefixWord ++ tailWord_447071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447071).length < 2 ^ (prefixWord ++ tailWord_447071).sum := by decide
  have hdescent : baseEnd_447071 < baseStart_447071 := by decide
  rcases family_descends (prefixWord ++ tailWord_447071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447073 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_447073 : Nat := 118140960795 + 447073 * 2 ^ 59
def prefixEnd_447073 : Nat := 4983230072969 + 3 ^ 40 * 447073 * 2
def baseEnd_447073 : Nat := 153042224431756372354303

theorem tailTrace_447073 : CollatzResearch.WordTrace tailWord_447073 prefixEnd_447073 153042224431756372354303 := by
  unfold tailWord_447073
  simp only [CollatzResearch.WordTrace]
  refine ⟨16306091909338349834657873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10870727939558899889771915 16306091909338349834657873)
  ·
    refine ⟨12229568932003762375993405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16306091909338349834657873 12229568932003762375993405)
    ·
      refine ⟨4586088349501410890997527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12229568932003762375993405 4586088349501410890997527)
      ·
        refine ⟨6879132524252116336496291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4586088349501410890997527 6879132524252116336496291)
        ·
          refine ⟨10318698786378174504744437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6879132524252116336496291 10318698786378174504744437)
          ·
            refine ⟨967378011222953859819791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10318698786378174504744437 967378011222953859819791)
            ·
              refine ⟨1451067016834430789729687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967378011222953859819791 1451067016834430789729687)
              ·
                refine ⟨2176600525251646184594531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1451067016834430789729687 2176600525251646184594531)
                ·
                  refine ⟨3264900787877469276891797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176600525251646184594531 3264900787877469276891797)
                  ·
                    refine ⟨153042224431756372354303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3264900787877469276891797 153042224431756372354303)
                    ·
                      rfl

theorem cell22_447073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_447073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447073 prefixEnd_447073 := by exact prefixLift 447073
  have htrace : WordTrace (prefixWord ++ tailWord_447073) baseStart_447073 baseEnd_447073 := by
    simpa [prefixWord, tailWord_447073, baseEnd_447073] using wordTrace_append hprefix tailTrace_447073
  have hstable : (prefixWord ++ tailWord_447073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447073).length < 2 ^ (prefixWord ++ tailWord_447073).sum := by decide
  have hdescent : baseEnd_447073 < baseStart_447073 := by decide
  rcases family_descends (prefixWord ++ tailWord_447073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447077 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 4]
def baseStart_447077 : Nat := 118140960795 + 447077 * 2 ^ 59
def prefixEnd_447077 : Nat := 4983230072969 + 3 ^ 40 * 447077 * 2
def baseEnd_447077 : Nat := 51014531237833898418097

theorem tailTrace_447077 : CollatzResearch.WordTrace tailWord_447077 prefixEnd_447077 51014531237833898418097 := by
  unfold tailWord_447077
  simp only [CollatzResearch.WordTrace]
  refine ⟨16306237801323858517803485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10870825200882572345202323 16306237801323858517803485)
  ·
    refine ⟨6114839175496446944176307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16306237801323858517803485 6114839175496446944176307)
    ·
      refine ⟨9172258763244670416264461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6114839175496446944176307 9172258763244670416264461)
      ·
        refine ⟨3439597036216751406099173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9172258763244670416264461 3439597036216751406099173)
        ·
          refine ⟨644924444290640888643595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3439597036216751406099173 644924444290640888643595)
          ·
            refine ⟨967386666435961332965393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644924444290640888643595 967386666435961332965393)
            ·
              refine ⟨725539999826970999724045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967386666435961332965393 725539999826970999724045)
              ·
                refine ⟨272077499935114124896517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725539999826970999724045 272077499935114124896517)
                ·
                  refine ⟨51014531237833898418097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272077499935114124896517 51014531237833898418097)
                  ·
                    rfl

theorem cell22_447077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_447077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447077 prefixEnd_447077 := by exact prefixLift 447077
  have htrace : WordTrace (prefixWord ++ tailWord_447077) baseStart_447077 baseEnd_447077 := by
    simpa [prefixWord, tailWord_447077, baseEnd_447077] using wordTrace_append hprefix tailTrace_447077
  have hstable : (prefixWord ++ tailWord_447077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447077).length < 2 ^ (prefixWord ++ tailWord_447077).sum := by decide
  have hdescent : baseEnd_447077 < baseStart_447077 := by decide
  rcases family_descends (prefixWord ++ tailWord_447077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447088 : List Nat := [2, 1, 1, 1, 7, 1, 9]
def baseStart_447088 : Nat := 118140960795 + 447088 * 2 ^ 59
def prefixEnd_447088 : Nat := 4983230072969 + 3 ^ 40 * 447088 * 2
def baseEnd_447088 : Nat := 5668420712529679008491

theorem tailTrace_447088 : CollatzResearch.WordTrace tailWord_447088 prefixEnd_447088 5668420712529679008491 := by
  unfold tailWord_447088
  simp only [CollatzResearch.WordTrace]
  refine ⟨8153319502142003698226959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10871092669522671597635945 8153319502142003698226959)
  ·
    refine ⟨12229979253213005547340439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8153319502142003698226959 12229979253213005547340439)
    ·
      refine ⟨18344968879819508321010659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12229979253213005547340439 18344968879819508321010659)
      ·
        refine ⟨27517453319729262481515989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18344968879819508321010659 27517453319729262481515989)
        ·
          refine ⟨644940312181154589410531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27517453319729262481515989 644940312181154589410531)
          ·
            refine ⟨967410468271731884115797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644940312181154589410531 967410468271731884115797)
            ·
              refine ⟨5668420712529679008491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 967410468271731884115797 5668420712529679008491)
              ·
                rfl

theorem cell22_447088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 9].length) (baseStart_447088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447088 prefixEnd_447088 := by exact prefixLift 447088
  have htrace : WordTrace (prefixWord ++ tailWord_447088) baseStart_447088 baseEnd_447088 := by
    simpa [prefixWord, tailWord_447088, baseEnd_447088] using wordTrace_append hprefix tailTrace_447088
  have hstable : (prefixWord ++ tailWord_447088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447088).length < 2 ^ (prefixWord ++ tailWord_447088).sum := by decide
  have hdescent : baseEnd_447088 < baseStart_447088 := by decide
  rcases family_descends (prefixWord ++ tailWord_447088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447122 : List Nat := [3, 2, 3, 1, 2, 3, 2, 6]
def baseStart_447122 : Nat := 118140960795 + 447122 * 2 ^ 59
def prefixEnd_447122 : Nat := 4983230072969 + 3 ^ 40 * 447122 * 2
def baseEnd_447122 : Nat := 17006555348126286431017

theorem tailTrace_447122 : CollatzResearch.WordTrace tailWord_447122 prefixEnd_447122 17006555348126286431017 := by
  unfold tailWord_447122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076969771540207800797905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10871919390773887468794413 4076969771540207800797905)
  ·
    refine ⟨3057727328655155850598429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4076969771540207800797905 3057727328655155850598429)
    ·
      refine ⟨1146647748245683443974411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3057727328655155850598429 1146647748245683443974411)
      ·
        refine ⟨1719971622368525165961617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146647748245683443974411 1719971622368525165961617)
        ·
          refine ⟨1289978716776393874471213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1719971622368525165961617 1289978716776393874471213)
          ·
            refine ⟨483742018791147702926705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1289978716776393874471213 483742018791147702926705)
            ·
              refine ⟨362806514093360777195029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483742018791147702926705 362806514093360777195029)
              ·
                refine ⟨17006555348126286431017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 362806514093360777195029 17006555348126286431017)
                ·
                  rfl

theorem cell22_447122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_447122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447122 prefixEnd_447122 := by exact prefixLift 447122
  have htrace : WordTrace (prefixWord ++ tailWord_447122) baseStart_447122 baseEnd_447122 := by
    simpa [prefixWord, tailWord_447122, baseEnd_447122] using wordTrace_append hprefix tailTrace_447122
  have hstable : (prefixWord ++ tailWord_447122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447122).length < 2 ^ (prefixWord ++ tailWord_447122).sum := by decide
  have hdescent : baseEnd_447122 < baseStart_447122 := by decide
  rcases family_descends (prefixWord ++ tailWord_447122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447133 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 7]
def baseStart_447133 : Nat := 118140960795 + 447133 * 2 ^ 59
def prefixEnd_447133 : Nat := 4983230072969 + 3 ^ 40 * 447133 * 2
def baseEnd_447133 : Nat := 51020921219312071951373

theorem tailTrace_447133 : CollatzResearch.WordTrace tailWord_447133 prefixEnd_447133 51020921219312071951373 := by
  unfold tailWord_447133
  simp only [CollatzResearch.WordTrace]
  refine ⟨16308280289120980081842053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10872186859413986721228035 16308280289120980081842053)
  ·
    refine ⟨3057802554210183765345385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16308280289120980081842053 3057802554210183765345385)
    ·
      refine ⟨2293351915657637824009039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3057802554210183765345385 2293351915657637824009039)
      ·
        refine ⟨3440027873486456736013559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2293351915657637824009039 3440027873486456736013559)
        ·
          refine ⟨5160041810229685104020339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440027873486456736013559 5160041810229685104020339)
          ·
            refine ⟨7740062715344527656030509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160041810229685104020339 7740062715344527656030509)
            ·
              refine ⟨2902523518254197871011441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7740062715344527656030509 2902523518254197871011441)
              ·
                refine ⟨2176892638690648403258581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902523518254197871011441 2176892638690648403258581)
                ·
                  refine ⟨51020921219312071951373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2176892638690648403258581 51020921219312071951373)
                  ·
                    rfl

theorem cell22_447133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_447133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447133 prefixEnd_447133 := by exact prefixLift 447133
  have htrace : WordTrace (prefixWord ++ tailWord_447133) baseStart_447133 baseEnd_447133 := by
    simpa [prefixWord, tailWord_447133, baseEnd_447133] using wordTrace_append hprefix tailTrace_447133
  have hstable : (prefixWord ++ tailWord_447133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447133).length < 2 ^ (prefixWord ++ tailWord_447133).sum := by decide
  have hdescent : baseEnd_447133 < baseStart_447133 := by decide
  rcases family_descends (prefixWord ++ tailWord_447133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447167 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 5]
def baseStart_447167 : Nat := 118140960795 + 447167 * 2 ^ 59
def prefixEnd_447167 : Nat := 4983230072969 + 3 ^ 40 * 447167 * 2
def baseEnd_447167 : Nat := 51024800850923820168005

theorem tailTrace_447167 : CollatzResearch.WordTrace tailWord_447167 prefixEnd_447167 51024800850923820168005 := by
  unfold tailWord_447167
  simp only [CollatzResearch.WordTrace]
  refine ⟨16309520370997803888579755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10873013580665202592386503 16309520370997803888579755)
  ·
    refine ⟨24464280556496705832869633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16309520370997803888579755 24464280556496705832869633)
    ·
      refine ⟨18348210417372529374652225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24464280556496705832869633 18348210417372529374652225)
      ·
        refine ⟨13761157813029397030989169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18348210417372529374652225 13761157813029397030989169)
        ·
          refine ⟨10320868359772047773241877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13761157813029397030989169 10320868359772047773241877)
          ·
            refine ⟨483790704364314739370713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10320868359772047773241877 483790704364314739370713)
            ·
              refine ⟨362843028273236054528035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483790704364314739370713 362843028273236054528035)
              ·
                refine ⟨544264542409854081792053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362843028273236054528035 544264542409854081792053)
                ·
                  refine ⟨51024800850923820168005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 544264542409854081792053 51024800850923820168005)
                  ·
                    rfl

theorem cell22_447167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 5].length) (baseStart_447167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447167 prefixEnd_447167 := by exact prefixLift 447167
  have htrace : WordTrace (prefixWord ++ tailWord_447167) baseStart_447167 baseEnd_447167 := by
    simpa [prefixWord, tailWord_447167, baseEnd_447167] using wordTrace_append hprefix tailTrace_447167
  have hstable : (prefixWord ++ tailWord_447167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447167).length < 2 ^ (prefixWord ++ tailWord_447167).sum := by decide
  have hdescent : baseEnd_447167 < baseStart_447167 := by decide
  rcases family_descends (prefixWord ++ tailWord_447167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447349 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_447349 : Nat := 118140960795 + 447349 * 2 ^ 59
def prefixEnd_447349 : Nat := 4983230072969 + 3 ^ 40 * 447349 * 2
def baseEnd_447349 : Nat := 153136704872183652453457

theorem tailTrace_447349 : CollatzResearch.WordTrace tailWord_447349 prefixEnd_447349 153136704872183652453457 := by
  unfold tailWord_447349
  simp only [CollatzResearch.WordTrace]
  refine ⟨16316158456338448971705101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10877438970892299314470067 16316158456338448971705101)
  ·
    refine ⟨6118559421126918364389413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16316158456338448971705101 6118559421126918364389413)
    ·
      refine ⟨1147229891461297193323015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6118559421126918364389413 1147229891461297193323015)
      ·
        refine ⟨1720844837191945789984523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147229891461297193323015 1720844837191945789984523)
        ·
          refine ⟨2581267255787918684976785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720844837191945789984523 2581267255787918684976785)
          ·
            refine ⟨1935950441840939013732589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2581267255787918684976785 1935950441840939013732589)
            ·
              refine ⟨725981415690352130149721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1935950441840939013732589 725981415690352130149721)
              ·
                refine ⟨544486061767764097612291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725981415690352130149721 544486061767764097612291)
                ·
                  refine ⟨816729092651646146418437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544486061767764097612291 816729092651646146418437)
                  ·
                    refine ⟨153136704872183652453457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816729092651646146418437 153136704872183652453457)
                    ·
                      rfl

theorem cell22_447349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_447349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447349 prefixEnd_447349 := by exact prefixLift 447349
  have htrace : WordTrace (prefixWord ++ tailWord_447349) baseStart_447349 baseEnd_447349 := by
    simpa [prefixWord, tailWord_447349, baseEnd_447349] using wordTrace_append hprefix tailTrace_447349
  have hstable : (prefixWord ++ tailWord_447349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447349).length < 2 ^ (prefixWord ++ tailWord_447349).sum := by decide
  have hdescent : baseEnd_447349 < baseStart_447349 := by decide
  rcases family_descends (prefixWord ++ tailWord_447349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447381 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 4]
def baseStart_447381 : Nat := 118140960795 + 447381 * 2 ^ 59
def prefixEnd_447381 : Nat := 4983230072969 + 3 ^ 40 * 447381 * 2
def baseEnd_447381 : Nat := 51049219708715411884453

theorem tailTrace_447381 : CollatzResearch.WordTrace tailWord_447381 prefixEnd_447381 51049219708715411884453 := by
  unfold tailWord_447381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16317325592222518436869997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10878217061481678957913331 16317325592222518436869997)
  ·
    refine ⟨6118997097083444413826249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16317325592222518436869997 6118997097083444413826249)
    ·
      refine ⟨4589247822812583310369687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6118997097083444413826249 4589247822812583310369687)
      ·
        refine ⟨6883871734218874965554531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589247822812583310369687 6883871734218874965554531)
        ·
          refine ⟨10325807601328312448331797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883871734218874965554531 10325807601328312448331797)
          ·
            refine ⟨484022231312264646015553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10325807601328312448331797 484022231312264646015553)
            ·
              refine ⟨363016673484198484511665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484022231312264646015553 363016673484198484511665)
              ·
                refine ⟨272262505113148863383749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363016673484198484511665 272262505113148863383749)
                ·
                  refine ⟨51049219708715411884453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272262505113148863383749 51049219708715411884453)
                  ·
                    rfl

theorem cell22_447381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_447381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447381 prefixEnd_447381 := by exact prefixLift 447381
  have htrace : WordTrace (prefixWord ++ tailWord_447381) baseStart_447381 baseEnd_447381 := by
    simpa [prefixWord, tailWord_447381, baseEnd_447381] using wordTrace_append hprefix tailTrace_447381
  have hstable : (prefixWord ++ tailWord_447381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447381).length < 2 ^ (prefixWord ++ tailWord_447381).sum := by decide
  have hdescent : baseEnd_447381 < baseStart_447381 := by decide
  rcases family_descends (prefixWord ++ tailWord_447381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447409 : List Nat := [1, 2, 2, 4, 3, 1, 3, 6]
def baseStart_447409 : Nat := 118140960795 + 447409 * 2 ^ 59
def prefixEnd_447409 : Nat := 4983230072969 + 3 ^ 40 * 447409 * 2
def baseEnd_447409 : Nat := 17017471566484832883697

theorem tailTrace_447409 : CollatzResearch.WordTrace tailWord_447409 prefixEnd_447409 17017471566484832883697 := by
  unfold tailWord_447409
  simp only [CollatzResearch.WordTrace]
  refine ⟨16318346836121079218889281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10878897890747386145926187 16318346836121079218889281)
  ·
    refine ⟨12238760127090809414166961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16318346836121079218889281 12238760127090809414166961)
    ·
      refine ⟨9179070095318107060625221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12238760127090809414166961 9179070095318107060625221)
      ·
        refine ⟨1721075642872145073867229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9179070095318107060625221 1721075642872145073867229)
        ·
          refine ⟨645403366077054402700211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1721075642872145073867229 645403366077054402700211)
          ·
            refine ⟨968105049115581604050317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645403366077054402700211 968105049115581604050317)
            ·
              refine ⟨363039393418343101518869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 968105049115581604050317 363039393418343101518869)
              ·
                refine ⟨17017471566484832883697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363039393418343101518869 17017471566484832883697)
                ·
                  rfl

theorem cell22_447409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 6].length) (baseStart_447409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447409 prefixEnd_447409 := by exact prefixLift 447409
  have htrace : WordTrace (prefixWord ++ tailWord_447409) baseStart_447409 baseEnd_447409 := by
    simpa [prefixWord, tailWord_447409, baseEnd_447409] using wordTrace_append hprefix tailTrace_447409
  have hstable : (prefixWord ++ tailWord_447409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447409).length < 2 ^ (prefixWord ++ tailWord_447409).sum := by decide
  have hdescent : baseEnd_447409 < baseStart_447409 := by decide
  rcases family_descends (prefixWord ++ tailWord_447409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447484 : List Nat := [2, 2, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_447484 : Nat := 118140960795 + 447484 * 2 ^ 59
def prefixEnd_447484 : Nat := 4983230072969 + 3 ^ 40 * 447484 * 2
def baseEnd_447484 : Nat := 153182918131088300328043

theorem tailTrace_447484 : CollatzResearch.WordTrace tailWord_447484 prefixEnd_447484 153182918131088300328043 := by
  unfold tailWord_447484
  simp only [CollatzResearch.WordTrace]
  refine ⟨8160541155424683513934753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10880721540566244685246337 8160541155424683513934753)
  ·
    refine ⟨6120405866568512635451065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8160541155424683513934753 6120405866568512635451065)
    ·
      refine ⟨4590304399926384476588299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6120405866568512635451065 4590304399926384476588299)
      ·
        refine ⟨6885456599889576714882449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590304399926384476588299 6885456599889576714882449)
        ·
          refine ⟨5164092449917182536161837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6885456599889576714882449 5164092449917182536161837)
          ·
            refine ⟨1936534668718943451060689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5164092449917182536161837 1936534668718943451060689)
            ·
              refine ⟨1452401001539207588295517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1936534668718943451060689 1452401001539207588295517)
              ·
                refine ⟨544650375577202845610819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1452401001539207588295517 544650375577202845610819)
                ·
                  refine ⟨816975563365804268416229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 544650375577202845610819 816975563365804268416229)
                  ·
                    refine ⟨153182918131088300328043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 816975563365804268416229 153182918131088300328043)
                    ·
                      rfl

theorem cell22_447484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_447484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447484 prefixEnd_447484 := by exact prefixLift 447484
  have htrace : WordTrace (prefixWord ++ tailWord_447484) baseStart_447484 baseEnd_447484 := by
    simpa [prefixWord, tailWord_447484, baseEnd_447484] using wordTrace_append hprefix tailTrace_447484
  have hstable : (prefixWord ++ tailWord_447484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447484).length < 2 ^ (prefixWord ++ tailWord_447484).sum := by decide
  have hdescent : baseEnd_447484 < baseStart_447484 := by decide
  rcases family_descends (prefixWord ++ tailWord_447484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447499 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 6]
def baseStart_447499 : Nat := 118140960795 + 447499 * 2 ^ 59
def prefixEnd_447499 : Nat := 4983230072969 + 3 ^ 40 * 447499 * 2
def baseEnd_447499 : Nat := 51062684312544420400999

theorem tailTrace_447499 : CollatzResearch.WordTrace tailWord_447499 prefixEnd_447499 51062684312544420400999 := by
  unfold tailWord_447499
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321629405795024589665551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10881086270530016393110367 16321629405795024589665551)
  ·
    refine ⟨24482444108692536884498327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16321629405795024589665551 24482444108692536884498327)
    ·
      refine ⟨36723666163038805326747491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24482444108692536884498327 36723666163038805326747491)
      ·
        refine ⟨55085499244558207990121237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36723666163038805326747491 55085499244558207990121237)
        ·
          refine ⟨2582132777088665999536933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55085499244558207990121237 2582132777088665999536933)
          ·
            refine ⟨484149895704124874913175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2582132777088665999536933 484149895704124874913175)
            ·
              refine ⟨726224843556187312369763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484149895704124874913175 726224843556187312369763)
              ·
                refine ⟨1089337265334280968554645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726224843556187312369763 1089337265334280968554645)
                ·
                  refine ⟨51062684312544420400999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1089337265334280968554645 51062684312544420400999)
                  ·
                    rfl

theorem cell22_447499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 6].length) (baseStart_447499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447499 prefixEnd_447499 := by exact prefixLift 447499
  have htrace : WordTrace (prefixWord ++ tailWord_447499) baseStart_447499 baseEnd_447499 := by
    simpa [prefixWord, tailWord_447499, baseEnd_447499] using wordTrace_append hprefix tailTrace_447499
  have hstable : (prefixWord ++ tailWord_447499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447499).length < 2 ^ (prefixWord ++ tailWord_447499).sum := by decide
  have hdescent : baseEnd_447499 < baseStart_447499 := by decide
  rcases family_descends (prefixWord ++ tailWord_447499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447550 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_447550 : Nat := 118140960795 + 447550 * 2 ^ 59
def prefixEnd_447550 : Nat := 4983230072969 + 3 ^ 40 * 447550 * 2
def baseEnd_447550 : Nat := 51068503759962042725947

theorem tailTrace_447550 : CollatzResearch.WordTrace tailWord_447550 prefixEnd_447550 51068503759962042725947 := by
  unfold tailWord_447550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040436191076282537471513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10882326352406840199848069 2040436191076282537471513)
  ·
    refine ⟨1530327143307211903103635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2040436191076282537471513 1530327143307211903103635)
    ·
      refine ⟨2295490714960817854655453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530327143307211903103635 2295490714960817854655453)
      ·
        refine ⟨860809018110306695495795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2295490714960817854655453 860809018110306695495795)
        ·
          refine ⟨1291213527165460043243693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860809018110306695495795 1291213527165460043243693)
          ·
            refine ⟨484205072687047516216385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291213527165460043243693 484205072687047516216385)
            ·
              refine ⟨363153804515285637162289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484205072687047516216385 363153804515285637162289)
              ·
                refine ⟨272365353386464227871717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363153804515285637162289 272365353386464227871717)
                ·
                  refine ⟨51068503759962042725947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272365353386464227871717 51068503759962042725947)
                  ·
                    rfl

theorem cell22_447550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_447550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447550 prefixEnd_447550 := by exact prefixLift 447550
  have htrace : WordTrace (prefixWord ++ tailWord_447550) baseStart_447550 baseEnd_447550 := by
    simpa [prefixWord, tailWord_447550, baseEnd_447550] using wordTrace_append hprefix tailTrace_447550
  have hstable : (prefixWord ++ tailWord_447550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447550).length < 2 ^ (prefixWord ++ tailWord_447550).sum := by decide
  have hdescent : baseEnd_447550 < baseStart_447550 := by decide
  rcases family_descends (prefixWord ++ tailWord_447550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447557 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_447557 : Nat := 118140960795 + 447557 * 2 ^ 59
def prefixEnd_447557 : Nat := 4983230072969 + 3 ^ 40 * 447557 * 2
def baseEnd_447557 : Nat := 153207907522940443252819

theorem tailTrace_447557 : CollatzResearch.WordTrace tailWord_447557 prefixEnd_447557 153207907522940443252819 := by
  unfold tailWord_447557
  simp only [CollatzResearch.WordTrace]
  refine ⟨16323744839584900495276925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10882496559723266996851283 16323744839584900495276925)
  ·
    refine ⟨6121404314844337685728847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16323744839584900495276925 6121404314844337685728847)
    ·
      refine ⟨9182106472266506528593271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121404314844337685728847 9182106472266506528593271)
      ·
        refine ⟨13773159708399759792889907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9182106472266506528593271 13773159708399759792889907)
        ·
          refine ⟨20659739562599639689334861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13773159708399759792889907 20659739562599639689334861)
          ·
            refine ⟨7747402335974864883500573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20659739562599639689334861 7747402335974864883500573)
            ·
              refine ⟨2905275875990574331312715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7747402335974864883500573 2905275875990574331312715)
              ·
                refine ⟨4357913813985861496969073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905275875990574331312715 4357913813985861496969073)
                ·
                  refine ⟨3268435360489396122726805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357913813985861496969073 3268435360489396122726805)
                  ·
                    refine ⟨153207907522940443252819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3268435360489396122726805 153207907522940443252819)
                    ·
                      rfl

theorem cell22_447557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_447557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447557 prefixEnd_447557 := by exact prefixLift 447557
  have htrace : WordTrace (prefixWord ++ tailWord_447557) baseStart_447557 baseEnd_447557 := by
    simpa [prefixWord, tailWord_447557, baseEnd_447557] using wordTrace_append hprefix tailTrace_447557
  have hstable : (prefixWord ++ tailWord_447557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447557).length < 2 ^ (prefixWord ++ tailWord_447557).sum := by decide
  have hdescent : baseEnd_447557 < baseStart_447557 := by decide
  rcases family_descends (prefixWord ++ tailWord_447557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447587 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 3, 7]
def baseStart_447587 : Nat := 118140960795 + 447587 * 2 ^ 59
def prefixEnd_447587 : Nat := 4983230072969 + 3 ^ 40 * 447587 * 2
def baseEnd_447587 : Nat := 153218177136030365002727

theorem tailTrace_447587 : CollatzResearch.WordTrace tailWord_447587 prefixEnd_447587 153218177136030365002727 := by
  unfold tailWord_447587
  simp only [CollatzResearch.WordTrace]
  refine ⟨16324839029476215618869015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10883226019650810412579343 16324839029476215618869015)
  ·
    refine ⟨24487258544214323428303523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16324839029476215618869015 24487258544214323428303523)
    ·
      refine ⟨36730887816321485142455285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24487258544214323428303523 36730887816321485142455285)
      ·
        refine ⟨3443520732780139232105183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36730887816321485142455285 3443520732780139232105183)
        ·
          refine ⟨5165281099170208848157775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443520732780139232105183 5165281099170208848157775)
          ·
            refine ⟨7747921648755313272236663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165281099170208848157775 7747921648755313272236663)
            ·
              refine ⟨11621882473132969908354995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747921648755313272236663 11621882473132969908354995)
              ·
                refine ⟨17432823709699454862532493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621882473132969908354995 17432823709699454862532493)
                ·
                  refine ⟨6537308891137295573449685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17432823709699454862532493 6537308891137295573449685)
                  ·
                    refine ⟨153218177136030365002727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6537308891137295573449685 153218177136030365002727)
                    ·
                      rfl

theorem cell22_447587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 7].length) (baseStart_447587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447587 prefixEnd_447587 := by exact prefixLift 447587
  have htrace : WordTrace (prefixWord ++ tailWord_447587) baseStart_447587 baseEnd_447587 := by
    simpa [prefixWord, tailWord_447587, baseEnd_447587] using wordTrace_append hprefix tailTrace_447587
  have hstable : (prefixWord ++ tailWord_447587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447587).length < 2 ^ (prefixWord ++ tailWord_447587).sum := by decide
  have hdescent : baseEnd_447587 < baseStart_447587 := by decide
  rcases family_descends (prefixWord ++ tailWord_447587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447593 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 1, 3]
def baseStart_447593 : Nat := 118140960795 + 447593 * 2 ^ 59
def prefixEnd_447593 : Nat := 4983230072969 + 3 ^ 40 * 447593 * 2
def baseEnd_447593 : Nat := 153220231058648349352709

theorem tailTrace_447593 : CollatzResearch.WordTrace tailWord_447593 prefixEnd_447593 153220231058648349352709 := by
  unfold tailWord_447593
  simp only [CollatzResearch.WordTrace]
  refine ⟨16325057867454478643587433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10883371911636319095724955 16325057867454478643587433)
  ·
    refine ⟨12243793400590858982690575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16325057867454478643587433 12243793400590858982690575)
    ·
      refine ⟨18365690100886288474035863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243793400590858982690575 18365690100886288474035863)
      ·
        refine ⟨27548535151329432711053795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365690100886288474035863 27548535151329432711053795)
        ·
          refine ⟨41322802726994149066580693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27548535151329432711053795 41322802726994149066580693)
          ·
            refine ⟨968503188913925368747985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41322802726994149066580693 968503188913925368747985)
            ·
              refine ⟨726377391685444026560989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968503188913925368747985 726377391685444026560989)
              ·
                refine ⟨272391521882041509960371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726377391685444026560989 272391521882041509960371)
                ·
                  refine ⟨408587282823062264940557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272391521882041509960371 408587282823062264940557)
                  ·
                    refine ⟨153220231058648349352709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408587282823062264940557 153220231058648349352709)
                    ·
                      rfl

theorem cell22_447593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_447593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447593 prefixEnd_447593 := by exact prefixLift 447593
  have htrace : WordTrace (prefixWord ++ tailWord_447593) baseStart_447593 baseEnd_447593 := by
    simpa [prefixWord, tailWord_447593, baseEnd_447593] using wordTrace_append hprefix tailTrace_447593
  have hstable : (prefixWord ++ tailWord_447593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447593).length < 2 ^ (prefixWord ++ tailWord_447593).sum := by decide
  have hdescent : baseEnd_447593 < baseStart_447593 := by decide
  rcases family_descends (prefixWord ++ tailWord_447593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447649 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_447649 : Nat := 118140960795 + 447649 * 2 ^ 59
def prefixEnd_447649 : Nat := 4983230072969 + 3 ^ 40 * 447649 * 2
def baseEnd_447649 : Nat := 153239401003082869952537

theorem tailTrace_447649 : CollatzResearch.WordTrace tailWord_447649 prefixEnd_447649 153239401003082869952537 := by
  unfold tailWord_447649
  simp only [CollatzResearch.WordTrace]
  refine ⟨16327100355251600207626001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10884733570167733471750667 16327100355251600207626001)
  ·
    refine ⟨12245325266438700155719501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16327100355251600207626001 12245325266438700155719501)
    ·
      refine ⟨4591996974914512558394813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12245325266438700155719501 4591996974914512558394813)
      ·
        refine ⟨1721998865592942209398055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4591996974914512558394813 1721998865592942209398055)
        ·
          refine ⟨2582998298389413314097083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1721998865592942209398055 2582998298389413314097083)
          ·
            refine ⟨3874497447584119971145625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582998298389413314097083 3874497447584119971145625)
            ·
              refine ⟨2905873085688089978359219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874497447584119971145625 2905873085688089978359219)
              ·
                refine ⟨4358809628532134967538829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2905873085688089978359219 4358809628532134967538829)
                ·
                  refine ⟨1634553610699550612827061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4358809628532134967538829 1634553610699550612827061)
                  ·
                    refine ⟨153239401003082869952537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1634553610699550612827061 153239401003082869952537)
                    ·
                      rfl

theorem cell22_447649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_447649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447649 prefixEnd_447649 := by exact prefixLift 447649
  have htrace : WordTrace (prefixWord ++ tailWord_447649) baseStart_447649 baseEnd_447649 := by
    simpa [prefixWord, tailWord_447649, baseEnd_447649] using wordTrace_append hprefix tailTrace_447649
  have hstable : (prefixWord ++ tailWord_447649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447649).length < 2 ^ (prefixWord ++ tailWord_447649).sum := by decide
  have hdescent : baseEnd_447649 < baseStart_447649 := by decide
  rcases family_descends (prefixWord ++ tailWord_447649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447664 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_447664 : Nat := 118140960795 + 447664 * 2 ^ 59
def prefixEnd_447664 : Nat := 4983230072969 + 3 ^ 40 * 447664 * 2
def baseEnd_447664 : Nat := 153244535809627830827491

theorem tailTrace_447664 : CollatzResearch.WordTrace tailWord_447664 prefixEnd_447664 153244535809627830827491 := by
  unfold tailWord_447664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163823725098628884711023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10885098300131505179614697 8163823725098628884711023)
  ·
    refine ⟨12245735587647943327066535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163823725098628884711023 12245735587647943327066535)
    ·
      refine ⟨18368603381471914990599803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12245735587647943327066535 18368603381471914990599803)
      ·
        refine ⟨27552905072207872485899705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18368603381471914990599803 27552905072207872485899705)
        ·
          refine ⟨20664678804155904364424779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27552905072207872485899705 20664678804155904364424779)
          ·
            refine ⟨30997018206233856546637169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20664678804155904364424779 30997018206233856546637169)
            ·
              refine ⟨23247763654675392409977877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30997018206233856546637169 23247763654675392409977877)
              ·
                refine ⟨1089738921312909019217713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23247763654675392409977877 1089738921312909019217713)
                ·
                  refine ⟨817304190984681764413285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1089738921312909019217713 817304190984681764413285)
                  ·
                    refine ⟨153244535809627830827491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817304190984681764413285 153244535809627830827491)
                    ·
                      rfl

theorem cell22_447664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_447664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447664 prefixEnd_447664 := by exact prefixLift 447664
  have htrace : WordTrace (prefixWord ++ tailWord_447664) baseStart_447664 baseEnd_447664 := by
    simpa [prefixWord, tailWord_447664, baseEnd_447664] using wordTrace_append hprefix tailTrace_447664
  have hstable : (prefixWord ++ tailWord_447664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447664).length < 2 ^ (prefixWord ++ tailWord_447664).sum := by decide
  have hdescent : baseEnd_447664 < baseStart_447664 := by decide
  rcases family_descends (prefixWord ++ tailWord_447664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447666 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_447666 : Nat := 118140960795 + 447666 * 2 ^ 59
def prefixEnd_447666 : Nat := 4983230072969 + 3 ^ 40 * 447666 * 2
def baseEnd_447666 : Nat := 153245220450500492277485

theorem tailTrace_447666 : CollatzResearch.WordTrace tailWord_447666 prefixEnd_447666 153245220450500492277485 := by
  unfold tailWord_447666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4081930099047503027748713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10885146930793341407329901 4081930099047503027748713)
  ·
    refine ⟨3061447574285627270811535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4081930099047503027748713 3061447574285627270811535)
    ·
      refine ⟨4592171361428440906217303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061447574285627270811535 4592171361428440906217303)
      ·
        refine ⟨6888257042142661359325955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592171361428440906217303 6888257042142661359325955)
        ·
          refine ⟨10332385563213992038988933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888257042142661359325955 10332385563213992038988933)
          ·
            refine ⟨1937322293102623507310425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10332385563213992038988933 1937322293102623507310425)
            ·
              refine ⟨1452991719826967630482819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937322293102623507310425 1452991719826967630482819)
              ·
                refine ⟨2179487579740451445724229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1452991719826967630482819 2179487579740451445724229)
                ·
                  refine ⟨408653921201334646073293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179487579740451445724229 408653921201334646073293)
                  ·
                    refine ⟨153245220450500492277485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408653921201334646073293 153245220450500492277485)
                    ·
                      rfl

theorem cell22_447666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_447666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447666 prefixEnd_447666 := by exact prefixLift 447666
  have htrace : WordTrace (prefixWord ++ tailWord_447666) baseStart_447666 baseEnd_447666 := by
    simpa [prefixWord, tailWord_447666, baseEnd_447666] using wordTrace_append hprefix tailTrace_447666
  have hstable : (prefixWord ++ tailWord_447666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447666).length < 2 ^ (prefixWord ++ tailWord_447666).sum := by decide
  have hdescent : baseEnd_447666 < baseStart_447666 := by decide
  rcases family_descends (prefixWord ++ tailWord_447666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447775 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 5]
def baseStart_447775 : Nat := 118140960795 + 447775 * 2 ^ 59
def prefixEnd_447775 : Nat := 4983230072969 + 3 ^ 40 * 447775 * 2
def baseEnd_447775 : Nat := 51094177792686847100717

theorem tailTrace_447775 : CollatzResearch.WordTrace tailWord_447775 prefixEnd_447775 51094177792686847100717 := by
  unfold tailWord_447775
  simp only [CollatzResearch.WordTrace]
  refine ⟨16331695952795123726712779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10887797301863415817808519 16331695952795123726712779)
  ·
    refine ⟨24497543929192685590069169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16331695952795123726712779 24497543929192685590069169)
    ·
      refine ⟨18373157946894514192551877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24497543929192685590069169 18373157946894514192551877)
      ·
        refine ⟨3444967115042721411103477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18373157946894514192551877 3444967115042721411103477)
        ·
          refine ⟨322965667035255132290951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3444967115042721411103477 322965667035255132290951)
          ·
            refine ⟨484448500552882698436427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322965667035255132290951 484448500552882698436427)
            ·
              refine ⟨726672750829324047654641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484448500552882698436427 726672750829324047654641)
              ·
                refine ⟨545004563121993035740981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726672750829324047654641 545004563121993035740981)
                ·
                  refine ⟨51094177792686847100717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 545004563121993035740981 51094177792686847100717)
                  ·
                    rfl

theorem cell22_447775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 5].length) (baseStart_447775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447775 prefixEnd_447775 := by exact prefixLift 447775
  have htrace : WordTrace (prefixWord ++ tailWord_447775) baseStart_447775 baseEnd_447775 := by
    simpa [prefixWord, tailWord_447775, baseEnd_447775] using wordTrace_append hprefix tailTrace_447775
  have hstable : (prefixWord ++ tailWord_447775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447775).length < 2 ^ (prefixWord ++ tailWord_447775).sum := by decide
  have hdescent : baseEnd_447775 < baseStart_447775 := by decide
  rcases family_descends (prefixWord ++ tailWord_447775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447816 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_447816 : Nat := 118140960795 + 447816 * 2 ^ 59
def prefixEnd_447816 : Nat := 4983230072969 + 3 ^ 40 * 447816 * 2
def baseEnd_447816 : Nat := 153296568515950101027025

theorem tailTrace_447816 : CollatzResearch.WordTrace tailWord_447816 prefixEnd_447816 153296568515950101027025 := by
  unfold tailWord_447816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166595672823293864477651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10888794230431058485970201 8166595672823293864477651)
  ·
    refine ⟨12249893509234940796716477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8166595672823293864477651 12249893509234940796716477)
    ·
      refine ⟨4593710065963102798768679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12249893509234940796716477 4593710065963102798768679)
      ·
        refine ⟨6890565098944654198153019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4593710065963102798768679 6890565098944654198153019)
        ·
          refine ⟨10335847648416981297229529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890565098944654198153019 10335847648416981297229529)
          ·
            refine ⟨7751885736312735972922147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10335847648416981297229529 7751885736312735972922147)
            ·
              refine ⟨11627828604469103959383221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751885736312735972922147 11627828604469103959383221)
              ·
                refine ⟨1090108931668978496192177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11627828604469103959383221 1090108931668978496192177)
                ·
                  refine ⟨817581698751733872144133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090108931668978496192177 817581698751733872144133)
                  ·
                    refine ⟨153296568515950101027025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817581698751733872144133 153296568515950101027025)
                    ·
                      rfl

theorem cell22_447816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_447816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447816 prefixEnd_447816 := by exact prefixLift 447816
  have htrace : WordTrace (prefixWord ++ tailWord_447816) baseStart_447816 baseEnd_447816 := by
    simpa [prefixWord, tailWord_447816, baseEnd_447816] using wordTrace_append hprefix tailTrace_447816
  have hstable : (prefixWord ++ tailWord_447816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447816).length < 2 ^ (prefixWord ++ tailWord_447816).sum := by decide
  have hdescent : baseEnd_447816 < baseStart_447816 := by decide
  rcases family_descends (prefixWord ++ tailWord_447816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447820 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 4]
def baseStart_447820 : Nat := 118140960795 + 447820 * 2 ^ 59
def prefixEnd_447820 : Nat := 4983230072969 + 3 ^ 40 * 447820 * 2
def baseEnd_447820 : Nat := 51099312599231807975671

theorem tailTrace_447820 : CollatzResearch.WordTrace tailWord_447820 prefixEnd_447820 51099312599231807975671 := by
  unfold tailWord_447820
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166668618816048206050457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10888891491754730941400609 8166668618816048206050457)
  ·
    refine ⟨6125001464112036154537843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8166668618816048206050457 6125001464112036154537843)
    ·
      refine ⟨9187502196168054231806765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125001464112036154537843 9187502196168054231806765)
      ·
        refine ⟨3445313323563020336927537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9187502196168054231806765 3445313323563020336927537)
        ·
          refine ⟨2583984992672265252695653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3445313323563020336927537 2583984992672265252695653)
          ·
            refine ⟨484497186126049734880435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2583984992672265252695653 484497186126049734880435)
            ·
              refine ⟨726745779189074602320653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484497186126049734880435 726745779189074602320653)
              ·
                refine ⟨272529667195902975870245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726745779189074602320653 272529667195902975870245)
                ·
                  refine ⟨51099312599231807975671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272529667195902975870245 51099312599231807975671)
                  ·
                    rfl

theorem cell22_447820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_447820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447820 prefixEnd_447820 := by exact prefixLift 447820
  have htrace : WordTrace (prefixWord ++ tailWord_447820) baseStart_447820 baseEnd_447820 := by
    simpa [prefixWord, tailWord_447820, baseEnd_447820] using wordTrace_append hprefix tailTrace_447820
  have hstable : (prefixWord ++ tailWord_447820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447820).length < 2 ^ (prefixWord ++ tailWord_447820).sum := by decide
  have hdescent : baseEnd_447820 < baseStart_447820 := by decide
  rcases family_descends (prefixWord ++ tailWord_447820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447831 : List Nat := [1, 1, 3, 2, 3, 4, 8]
def baseStart_447831 : Nat := 118140960795 + 447831 * 2 ^ 59
def prefixEnd_447831 : Nat := 4983230072969 + 3 ^ 40 * 447831 * 2
def baseEnd_447831 : Nat := 5677840863796113403777

theorem tailTrace_447831 : CollatzResearch.WordTrace tailWord_447831 prefixEnd_447831 5677840863796113403777 := by
  unfold tailWord_447831
  simp only [CollatzResearch.WordTrace]
  refine ⟨16333738440592245290751347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10889158960394830193834231 16333738440592245290751347)
  ·
    refine ⟨24500607660888367936127021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16333738440592245290751347 24500607660888367936127021)
    ·
      refine ⟨9187727872833137976047633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24500607660888367936127021 9187727872833137976047633)
      ·
        refine ⟨6890795904624853482035725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9187727872833137976047633 6890795904624853482035725)
        ·
          refine ⟨2584048464234320055763397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6890795904624853482035725 2584048464234320055763397)
          ·
            refine ⟨484509087043935010455637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2584048464234320055763397 484509087043935010455637)
            ·
              refine ⟨5677840863796113403777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 484509087043935010455637 5677840863796113403777)
              ·
                rfl

theorem cell22_447831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 8].length) (baseStart_447831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447831 prefixEnd_447831 := by exact prefixLift 447831
  have htrace : WordTrace (prefixWord ++ tailWord_447831) baseStart_447831 baseEnd_447831 := by
    simpa [prefixWord, tailWord_447831, baseEnd_447831] using wordTrace_append hprefix tailTrace_447831
  have hstable : (prefixWord ++ tailWord_447831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447831).length < 2 ^ (prefixWord ++ tailWord_447831).sum := by decide
  have hdescent : baseEnd_447831 < baseStart_447831 := by decide
  rcases family_descends (prefixWord ++ tailWord_447831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447848 : List Nat := [2, 1, 4, 2, 3, 1, 2, 7]
def baseStart_447848 : Nat := 118140960795 + 447848 * 2 ^ 59
def prefixEnd_447848 : Nat := 4983230072969 + 3 ^ 40 * 447848 * 2
def baseEnd_447848 : Nat := 17034169196656964914103

theorem tailTrace_447848 : CollatzResearch.WordTrace tailWord_447848 prefixEnd_447848 17034169196656964914103 := by
  unfold tailWord_447848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167179240765328597060099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10889572321020438129413465 8167179240765328597060099)
  ·
    refine ⟨12250768861147992895590149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8167179240765328597060099 12250768861147992895590149)
    ·
      refine ⟨2297019161465248667923153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12250768861147992895590149 2297019161465248667923153)
      ·
        refine ⟨1722764371098936500942365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2297019161465248667923153 1722764371098936500942365)
        ·
          refine ⟨646036639162101187853387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1722764371098936500942365 646036639162101187853387)
          ·
            refine ⟨969054958743151781780081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646036639162101187853387 969054958743151781780081)
            ·
              refine ⟨726791219057363836335061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969054958743151781780081 726791219057363836335061)
              ·
                refine ⟨17034169196656964914103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 726791219057363836335061 17034169196656964914103)
                ·
                  rfl

theorem cell22_447848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 7].length) (baseStart_447848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447848 prefixEnd_447848 := by exact prefixLift 447848
  have htrace : WordTrace (prefixWord ++ tailWord_447848) baseStart_447848 baseEnd_447848 := by
    simpa [prefixWord, tailWord_447848, baseEnd_447848] using wordTrace_append hprefix tailTrace_447848
  have hstable : (prefixWord ++ tailWord_447848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447848).length < 2 ^ (prefixWord ++ tailWord_447848).sum := by decide
  have hdescent : baseEnd_447848 < baseStart_447848 := by decide
  rcases family_descends (prefixWord ++ tailWord_447848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447852 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_447852 : Nat := 118140960795 + 447852 * 2 ^ 59
def prefixEnd_447852 : Nat := 4983230072969 + 3 ^ 40 * 447852 * 2
def baseEnd_447852 : Nat := 153308892051658007126915

theorem tailTrace_447852 : CollatzResearch.WordTrace tailWord_447852 prefixEnd_447852 153308892051658007126915 := by
  unfold tailWord_447852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167252186758082938632905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10889669582344110584843873 8167252186758082938632905)
  ·
    refine ⟨6125439140068562203974679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8167252186758082938632905 6125439140068562203974679)
    ·
      refine ⟨9188158710102843305962019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125439140068562203974679 9188158710102843305962019)
      ·
        refine ⟨13782238065154264958943029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188158710102843305962019 13782238065154264958943029)
        ·
          refine ⟨1292084818608212339900909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13782238065154264958943029 1292084818608212339900909)
          ·
            refine ⟨484531806978079627462841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1292084818608212339900909 484531806978079627462841)
            ·
              refine ⟨363398855233559720597131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484531806978079627462841 363398855233559720597131)
              ·
                refine ⟨545098282850339580895697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363398855233559720597131 545098282850339580895697)
                ·
                  refine ⟨408823712137754685671773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 545098282850339580895697 408823712137754685671773)
                  ·
                    refine ⟨153308892051658007126915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408823712137754685671773 153308892051658007126915)
                    ·
                      rfl

theorem cell22_447852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_447852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447852 prefixEnd_447852 := by exact prefixLift 447852
  have htrace : WordTrace (prefixWord ++ tailWord_447852) baseStart_447852 baseEnd_447852 := by
    simpa [prefixWord, tailWord_447852, baseEnd_447852] using wordTrace_append hprefix tailTrace_447852
  have hstable : (prefixWord ++ tailWord_447852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447852).length < 2 ^ (prefixWord ++ tailWord_447852).sum := by decide
  have hdescent : baseEnd_447852 < baseStart_447852 := by decide
  rcases family_descends (prefixWord ++ tailWord_447852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447897 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 1, 3]
def baseStart_447897 : Nat := 118140960795 + 447897 * 2 ^ 59
def prefixEnd_447897 : Nat := 4983230072969 + 3 ^ 40 * 447897 * 2
def baseEnd_447897 : Nat := 153324296471292889751777

theorem tailTrace_447897 : CollatzResearch.WordTrace tailWord_447897 prefixEnd_447897 153324296471292889751777 := by
  unfold tailWord_447897
  simp only [CollatzResearch.WordTrace]
  refine ⟨16336145658353138562653945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10890763772235425708435963 16336145658353138562653945)
  ·
    refine ⟨12252109243764853921990459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16336145658353138562653945 12252109243764853921990459)
    ·
      refine ⟨18378163865647280882985689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12252109243764853921990459 18378163865647280882985689)
      ·
        refine ⟨13783622899235460662239267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18378163865647280882985689 13783622899235460662239267)
        ·
          refine ⟨20675434348853190993358901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13783622899235460662239267 20675434348853190993358901)
          ·
            refine ⟨1938321970204986655627397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20675434348853190993358901 1938321970204986655627397)
            ·
              refine ⟨363435369413434997930137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1938321970204986655627397 363435369413434997930137)
              ·
                refine ⟨272576527060076248447603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363435369413434997930137 272576527060076248447603)
                ·
                  refine ⟨408864790590114372671405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272576527060076248447603 408864790590114372671405)
                  ·
                    refine ⟨153324296471292889751777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 408864790590114372671405 153324296471292889751777)
                    ·
                      rfl

theorem cell22_447897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_447897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447897 prefixEnd_447897 := by exact prefixLift 447897
  have htrace : WordTrace (prefixWord ++ tailWord_447897) baseStart_447897 baseEnd_447897 := by
    simpa [prefixWord, tailWord_447897, baseEnd_447897] using wordTrace_append hprefix tailTrace_447897
  have hstable : (prefixWord ++ tailWord_447897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447897).length < 2 ^ (prefixWord ++ tailWord_447897).sum := by decide
  have hdescent : baseEnd_447897 < baseStart_447897 := by decide
  rcases family_descends (prefixWord ++ tailWord_447897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447983 : List Nat := [1, 1, 2, 1, 4, 1, 6, 6]
def baseStart_447983 : Nat := 118140960795 + 447983 * 2 ^ 59
def prefixEnd_447983 : Nat := 4983230072969 + 3 ^ 40 * 447983 * 2
def baseEnd_447983 : Nat := 17039304003201925789057

theorem tailTrace_447983 : CollatzResearch.WordTrace tailWord_447983 prefixEnd_447983 17039304003201925789057 := by
  unfold tailWord_447983
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339282336041575250284603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10892854890694383500189735 16339282336041575250284603)
  ·
    refine ⟨24508923504062362875426905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16339282336041575250284603 24508923504062362875426905)
    ·
      refine ⟨18381692628046772156570179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24508923504062362875426905 18381692628046772156570179)
      ·
        refine ⟨27572538942070158234855269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18381692628046772156570179 27572538942070158234855269)
        ·
          refine ⟨5169851051638154669035363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27572538942070158234855269 5169851051638154669035363)
          ·
            refine ⟨7754776577457232003553045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169851051638154669035363 7754776577457232003553045)
            ·
              refine ⟨363505152068307750166549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7754776577457232003553045 363505152068307750166549)
              ·
                refine ⟨17039304003201925789057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363505152068307750166549 17039304003201925789057)
                ·
                  rfl

theorem cell22_447983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 6].length) (baseStart_447983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447983 prefixEnd_447983 := by exact prefixLift 447983
  have htrace : WordTrace (prefixWord ++ tailWord_447983) baseStart_447983 baseEnd_447983 := by
    simpa [prefixWord, tailWord_447983, baseEnd_447983] using wordTrace_append hprefix tailTrace_447983
  have hstable : (prefixWord ++ tailWord_447983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447983).length < 2 ^ (prefixWord ++ tailWord_447983).sum := by decide
  have hdescent : baseEnd_447983 < baseStart_447983 := by decide
  rcases family_descends (prefixWord ++ tailWord_447983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_447989 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 4]
def baseStart_447989 : Nat := 118140960795 + 447989 * 2 ^ 59
def prefixEnd_447989 : Nat := 4983230072969 + 3 ^ 40 * 447989 * 2
def baseEnd_447989 : Nat := 51118596650478438817165

theorem tailTrace_447989 : CollatzResearch.WordTrace tailWord_447989 prefixEnd_447989 51118596650478438817165 := by
  unfold tailWord_447989
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339501174019838275003021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10893000782679892183335347 16339501174019838275003021)
  ·
    refine ⟨6127312940257439353126133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16339501174019838275003021 6127312940257439353126133)
    ·
      refine ⟨574435588149134939355575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6127312940257439353126133 574435588149134939355575)
      ·
        refine ⟨861653382223702409033363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574435588149134939355575 861653382223702409033363)
        ·
          refine ⟨1292480073335553613550045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861653382223702409033363 1292480073335553613550045)
          ·
            refine ⟨484680027500832605081267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1292480073335553613550045 484680027500832605081267)
            ·
              refine ⟨727020041251248907621901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484680027500832605081267 727020041251248907621901)
              ·
                refine ⟨272632515469218340358213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727020041251248907621901 272632515469218340358213)
                ·
                  refine ⟨51118596650478438817165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272632515469218340358213 51118596650478438817165)
                  ·
                    rfl

theorem cell22_447989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_447989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_447989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_447989 prefixEnd_447989 := by exact prefixLift 447989
  have htrace : WordTrace (prefixWord ++ tailWord_447989) baseStart_447989 baseEnd_447989 := by
    simpa [prefixWord, tailWord_447989, baseEnd_447989] using wordTrace_append hprefix tailTrace_447989
  have hstable : (prefixWord ++ tailWord_447989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_447989).length < 2 ^ (prefixWord ++ tailWord_447989).sum := by decide
  have hdescent : baseEnd_447989 < baseStart_447989 := by decide
  rcases family_descends (prefixWord ++ tailWord_447989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448002 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_448002 : Nat := 118140960795 + 448002 * 2 ^ 59
def prefixEnd_448002 : Nat := 4983230072969 + 3 ^ 40 * 448002 * 2
def baseEnd_448002 : Nat := 153360240117107615876455

theorem tailTrace_448002 : CollatzResearch.WordTrace tailWord_448002 prefixEnd_448002 153360240117107615876455 := by
  unfold tailWord_448002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4084993830743185373806565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10893316881981827663484173 4084993830743185373806565)
  ·
    refine ⟨765936343264347257588731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4084993830743185373806565 765936343264347257588731)
    ·
      refine ⟨1148904514896520886383097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765936343264347257588731 1148904514896520886383097)
      ·
        refine ⟨861678386172390664787323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148904514896520886383097 861678386172390664787323)
        ·
          refine ⟨1292517579258585997180985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861678386172390664787323 1292517579258585997180985)
          ·
            refine ⟨969388184443939497885739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292517579258585997180985 969388184443939497885739)
            ·
              refine ⟨1454082276665909246828609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969388184443939497885739 1454082276665909246828609)
              ·
                refine ⟨1090561707499431935121457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1454082276665909246828609 1090561707499431935121457)
                ·
                  refine ⟨817921280624573951341093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1090561707499431935121457 817921280624573951341093)
                  ·
                    refine ⟨153360240117107615876455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 817921280624573951341093 153360240117107615876455)
                    ·
                      rfl

theorem cell22_448002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_448002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448002 prefixEnd_448002 := by exact prefixLift 448002
  have htrace : WordTrace (prefixWord ++ tailWord_448002) baseStart_448002 baseEnd_448002 := by
    simpa [prefixWord, tailWord_448002, baseEnd_448002] using wordTrace_append hprefix tailTrace_448002
  have hstable : (prefixWord ++ tailWord_448002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448002).length < 2 ^ (prefixWord ++ tailWord_448002).sum := by decide
  have hdescent : baseEnd_448002 < baseStart_448002 := by decide
  rcases family_descends (prefixWord ++ tailWord_448002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448006 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_448006 : Nat := 118140960795 + 448006 * 2 ^ 59
def prefixEnd_448006 : Nat := 4983230072969 + 3 ^ 40 * 448006 * 2
def baseEnd_448006 : Nat := 51120536466284312925481

theorem tailTrace_448006 : CollatzResearch.WordTrace tailWord_448006 prefixEnd_448006 51120536466284312925481 := by
  unfold tailWord_448006
  simp only [CollatzResearch.WordTrace]
  refine ⟨510628787967445318074121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10893414143305500118914581 510628787967445318074121)
  ·
    refine ⟨382971590975583988555591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 510628787967445318074121 382971590975583988555591)
    ·
      refine ⟨574457386463375982833387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382971590975583988555591 574457386463375982833387)
      ·
        refine ⟨861686079695063974250081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574457386463375982833387 861686079695063974250081)
        ·
          refine ⟨646264559771297980687561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861686079695063974250081 646264559771297980687561)
          ·
            refine ⟨484698419828473485515671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646264559771297980687561 484698419828473485515671)
            ·
              refine ⟨727047629742710228273507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484698419828473485515671 727047629742710228273507)
              ·
                refine ⟨1090571444614065342410261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727047629742710228273507 1090571444614065342410261)
                ·
                  refine ⟨51120536466284312925481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1090571444614065342410261 51120536466284312925481)
                  ·
                    rfl

theorem cell22_448006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_448006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448006 prefixEnd_448006 := by exact prefixLift 448006
  have htrace : WordTrace (prefixWord ++ tailWord_448006) baseStart_448006 baseEnd_448006 := by
    simpa [prefixWord, tailWord_448006, baseEnd_448006] using wordTrace_append hprefix tailTrace_448006
  have hstable : (prefixWord ++ tailWord_448006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448006).length < 2 ^ (prefixWord ++ tailWord_448006).sum := by decide
  have hdescent : baseEnd_448006 < baseStart_448006 := by decide
  rcases family_descends (prefixWord ++ tailWord_448006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448077 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_448077 : Nat := 118140960795 + 448077 * 2 ^ 59
def prefixEnd_448077 : Nat := 4983230072969 + 3 ^ 40 * 448077 * 2
def baseEnd_448077 : Nat := 153385914149832420251225

theorem tailTrace_448077 : CollatzResearch.WordTrace tailWord_448077 prefixEnd_448077 153385914149832420251225 := by
  unfold tailWord_448077
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342710797701029304206485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10895140531800686202804323 16342710797701029304206485)
  ·
    refine ⟨766064568642235748634679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16342710797701029304206485 766064568642235748634679)
    ·
      refine ⟨1149096852963353622952019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766064568642235748634679 1149096852963353622952019)
      ·
        refine ⟨1723645279445030434428029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149096852963353622952019 1723645279445030434428029)
        ·
          refine ⟨646366979791886412910511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1723645279445030434428029 646366979791886412910511)
          ·
            refine ⟨969550469687829619365767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646366979791886412910511 969550469687829619365767)
            ·
              refine ⟨1454325704531744429048651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 969550469687829619365767 1454325704531744429048651)
              ·
                refine ⟨2181488556797616643572977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1454325704531744429048651 2181488556797616643572977)
                ·
                  refine ⟨1636116417598212482679733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2181488556797616643572977 1636116417598212482679733)
                  ·
                    refine ⟨153385914149832420251225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1636116417598212482679733 153385914149832420251225)
                    ·
                      rfl

theorem cell22_448077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_448077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448077 prefixEnd_448077 := by exact prefixLift 448077
  have htrace : WordTrace (prefixWord ++ tailWord_448077) baseStart_448077 baseEnd_448077 := by
    simpa [prefixWord, tailWord_448077, baseEnd_448077] using wordTrace_append hprefix tailTrace_448077
  have hstable : (prefixWord ++ tailWord_448077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448077).length < 2 ^ (prefixWord ++ tailWord_448077).sum := by decide
  have hdescent : baseEnd_448077 < baseStart_448077 := by decide
  rcases family_descends (prefixWord ++ tailWord_448077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448152 : List Nat := [2, 1, 2, 4, 1, 4, 2, 6]
def baseStart_448152 : Nat := 118140960795 + 448152 * 2 ^ 59
def prefixEnd_448152 : Nat := 4983230072969 + 3 ^ 40 * 448152 * 2
def baseEnd_448152 : Nat := 17045732020284136069555

theorem tailTrace_448152 : CollatzResearch.WordTrace tailWord_448152 prefixEnd_448152 17045732020284136069555 := by
  unfold tailWord_448152
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172723136214658556593355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10896964181619544742124473 8172723136214658556593355)
  ·
    refine ⟨12259084704321987834890033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172723136214658556593355 12259084704321987834890033)
    ·
      refine ⟨9194313528241490876167525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12259084704321987834890033 9194313528241490876167525)
      ·
        refine ⟨1723933786545279539281411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9194313528241490876167525 1723933786545279539281411)
        ·
          refine ⟨2585900679817919308922117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1723933786545279539281411 2585900679817919308922117)
          ·
            refine ⟨484856377465859870422897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2585900679817919308922117 484856377465859870422897)
            ·
              refine ⟨363642283099394902817173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484856377465859870422897 363642283099394902817173)
              ·
                refine ⟨17045732020284136069555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363642283099394902817173 17045732020284136069555)
                ·
                  rfl

theorem cell22_448152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_448152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448152 prefixEnd_448152 := by exact prefixLift 448152
  have htrace : WordTrace (prefixWord ++ tailWord_448152) baseStart_448152 baseEnd_448152 := by
    simpa [prefixWord, tailWord_448152, baseEnd_448152] using wordTrace_append hprefix tailTrace_448152
  have hstable : (prefixWord ++ tailWord_448152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448152).length < 2 ^ (prefixWord ++ tailWord_448152).sum := by decide
  have hdescent : baseEnd_448152 < baseStart_448152 := by decide
  rcases family_descends (prefixWord ++ tailWord_448152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448163 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 9]
def baseStart_448163 : Nat := 118140960795 + 448163 * 2 ^ 59
def prefixEnd_448163 : Nat := 4983230072969 + 3 ^ 40 * 448163 * 2
def baseEnd_448163 : Nat := 51138451235785620866987

theorem tailTrace_448163 : CollatzResearch.WordTrace tailWord_448163 prefixEnd_448163 51138451235785620866987 := by
  unfold tailWord_448163
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345847475389465991837143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10897231650259643994558095 16345847475389465991837143)
  ·
    refine ⟨24518771213084198987755715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16345847475389465991837143 24518771213084198987755715)
    ·
      refine ⟨36778156819626298481633573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24518771213084198987755715 36778156819626298481633573)
      ·
        refine ⟨6895904403679930965306295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36778156819626298481633573 6895904403679930965306295)
        ·
          refine ⟨10343856605519896447959443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895904403679930965306295 10343856605519896447959443)
          ·
            refine ⟨15515784908279844671939165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343856605519896447959443 15515784908279844671939165)
            ·
              refine ⟨5818419340604941751977187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15515784908279844671939165 5818419340604941751977187)
              ·
                refine ⟨8727629010907412627965781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818419340604941751977187 8727629010907412627965781)
                ·
                  refine ⟨51138451235785620866987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8727629010907412627965781 51138451235785620866987)
                  ·
                    rfl

theorem cell22_448163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 9].length) (baseStart_448163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448163 prefixEnd_448163 := by exact prefixLift 448163
  have htrace : WordTrace (prefixWord ++ tailWord_448163) baseStart_448163 baseEnd_448163 := by
    simpa [prefixWord, tailWord_448163, baseEnd_448163] using wordTrace_append hprefix tailTrace_448163
  have hstable : (prefixWord ++ tailWord_448163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448163).length < 2 ^ (prefixWord ++ tailWord_448163).sum := by decide
  have hdescent : baseEnd_448163 < baseStart_448163 := by decide
  rcases family_descends (prefixWord ++ tailWord_448163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448255 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 4, 4]
def baseStart_448255 : Nat := 118140960795 + 448255 * 2 ^ 59
def prefixEnd_448255 : Nat := 4983230072969 + 3 ^ 40 * 448255 * 2
def baseEnd_448255 : Nat := 153446847187499289300679

theorem tailTrace_448255 : CollatzResearch.WordTrace tailWord_448255 prefixEnd_448255 153446847187499289300679 := by
  unfold tailWord_448255
  simp only [CollatzResearch.WordTrace]
  refine ⟨16349202991056165704186219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10899468660704110469457479 16349202991056165704186219)
  ·
    refine ⟨24523804486584248556279329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16349202991056165704186219 24523804486584248556279329)
    ·
      refine ⟨18392853364938186417209497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24523804486584248556279329 18392853364938186417209497)
      ·
        refine ⟨13794640023703639812907123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18392853364938186417209497 13794640023703639812907123)
        ·
          refine ⟨20691960035555459719360685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13794640023703639812907123 20691960035555459719360685)
          ·
            refine ⟨7759485013333297394760257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20691960035555459719360685 7759485013333297394760257)
            ·
              refine ⟨5819613759999973046070193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759485013333297394760257 5819613759999973046070193)
              ·
                refine ⟨4364710319999979784552645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5819613759999973046070193 4364710319999979784552645)
                ·
                  refine ⟨818383184999996209603621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4364710319999979784552645 818383184999996209603621)
                  ·
                    refine ⟨153446847187499289300679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 818383184999996209603621 153446847187499289300679)
                    ·
                      rfl

theorem cell22_448255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_448255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448255 prefixEnd_448255 := by exact prefixLift 448255
  have htrace : WordTrace (prefixWord ++ tailWord_448255) baseStart_448255 baseEnd_448255 := by
    simpa [prefixWord, tailWord_448255, baseEnd_448255] using wordTrace_append hprefix tailTrace_448255
  have hstable : (prefixWord ++ tailWord_448255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448255).length < 2 ^ (prefixWord ++ tailWord_448255).sum := by decide
  have hdescent : baseEnd_448255 < baseStart_448255 := by decide
  rcases family_descends (prefixWord ++ tailWord_448255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_448270 : List Nat := [4, 1, 1, 2, 1, 1, 2, 10]
def baseStart_448270 : Nat := 118140960795 + 448270 * 2 ^ 59
def prefixEnd_448270 : Nat := 4983230072969 + 3 ^ 40 * 448270 * 2
def baseEnd_448270 : Nat := 17050220221560472241737

theorem tailTrace_448270 : CollatzResearch.WordTrace tailWord_448270 prefixEnd_448270 17050220221560472241737 := by
  unfold tailWord_448270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043718760750227908247783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10899833390667882177321509 2043718760750227908247783)
  ·
    refine ⟨3065578141125341862371675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2043718760750227908247783 3065578141125341862371675)
    ·
      refine ⟨4598367211688012793557513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065578141125341862371675 4598367211688012793557513)
      ·
        refine ⟨3448775408766009595168135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4598367211688012793557513 3448775408766009595168135)
        ·
          refine ⟨5173163113149014392752203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448775408766009595168135 5173163113149014392752203)
          ·
            refine ⟨7759744669723521589128305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173163113149014392752203 7759744669723521589128305)
            ·
              refine ⟨5819808502292641191846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759744669723521589128305 5819808502292641191846229)
              ·
                refine ⟨17050220221560472241737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5819808502292641191846229 17050220221560472241737)
                ·
                  rfl

theorem cell22_448270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_448270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_448270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_448270 prefixEnd_448270 := by exact prefixLift 448270
  have htrace : WordTrace (prefixWord ++ tailWord_448270) baseStart_448270 baseEnd_448270 := by
    simpa [prefixWord, tailWord_448270, baseEnd_448270] using wordTrace_append hprefix tailTrace_448270
  have hstable : (prefixWord ++ tailWord_448270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_448270).length < 2 ^ (prefixWord ++ tailWord_448270).sum := by decide
  have hdescent : baseEnd_448270 < baseStart_448270 := by decide
  rcases family_descends (prefixWord ++ tailWord_448270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
