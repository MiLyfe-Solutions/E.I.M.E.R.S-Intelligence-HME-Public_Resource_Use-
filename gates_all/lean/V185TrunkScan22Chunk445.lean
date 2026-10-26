import V185TrunkScan22Chunk444

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3967370 : List Nat := [3, 1, 2, 5, 2, 9]
def baseStart_3967370 : Nat := 118140960795 + 3967370 * 2 ^ 59
def prefixEnd_3967370 : Nat := 4983230072969 + 3 ^ 40 * 3967370 * 2
def baseEnd_3967370 : Nat := 16766812709697513418349

theorem tailTrace_3967370 : CollatzResearch.WordTrace tailWord_3967370 prefixEnd_3967370 16766812709697513418349 := by
  unfold tailWord_3967370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36175467909225884424194891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96467914424602358464519709 36175467909225884424194891)
  ·
    refine ⟨54263201863838826636292337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36175467909225884424194891 54263201863838826636292337)
    ·
      refine ⟨40697401397879119977219253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54263201863838826636292337 40697401397879119977219253)
      ·
        refine ⟨3815381381051167497864305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40697401397879119977219253 3815381381051167497864305)
        ·
          refine ⟨2861536035788375623398229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815381381051167497864305 2861536035788375623398229)
          ·
            refine ⟨16766812709697513418349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2861536035788375623398229 16766812709697513418349)
            ·
              rfl

theorem cell22_3967370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 9].length) (baseStart_3967370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967370 prefixEnd_3967370 := by exact prefixLift 3967370
  have htrace : WordTrace (prefixWord ++ tailWord_3967370) baseStart_3967370 baseEnd_3967370 := by
    simpa [prefixWord, tailWord_3967370, baseEnd_3967370] using wordTrace_append hprefix tailTrace_3967370
  have hstable : (prefixWord ++ tailWord_3967370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967370).length < 2 ^ (prefixWord ++ tailWord_3967370).sum := by decide
  have hdescent : baseEnd_3967370 < baseStart_3967370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967473 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3967473 : Nat := 118140960795 + 3967473 * 2 ^ 59
def prefixEnd_3967473 : Nat := 4983230072969 + 3 ^ 40 * 3967473 * 2
def baseEnd_3967473 : Nat := 1358147088490440651560953

theorem tailTrace_3967473 : CollatzResearch.WordTrace tailWord_3967473 prefixEnd_3967473 1358147088490440651560953 := by
  unfold tailWord_3967473
  simp only [CollatzResearch.WordTrace]
  refine ⟨144705628355530386287779073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96470418903686924191852715 144705628355530386287779073)
  ·
    refine ⟨108529221266647789715834305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144705628355530386287779073 108529221266647789715834305)
    ·
      refine ⟨81396915949985842286875729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108529221266647789715834305 81396915949985842286875729)
      ·
        refine ⟨61047686962489381715156797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81396915949985842286875729 61047686962489381715156797)
        ·
          refine ⟨22892882610933518143183799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61047686962489381715156797 22892882610933518143183799)
          ·
            refine ⟨34339323916400277214775699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22892882610933518143183799 34339323916400277214775699)
            ·
              refine ⟨51508985874600415822163549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34339323916400277214775699 51508985874600415822163549)
              ·
                refine ⟨19315869702975155933311331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51508985874600415822163549 19315869702975155933311331)
                ·
                  refine ⟨28973804554462733899966997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19315869702975155933311331 28973804554462733899966997)
                  ·
                    refine ⟨1358147088490440651560953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28973804554462733899966997 1358147088490440651560953)
                    ·
                      rfl

theorem cell22_3967473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3967473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967473 prefixEnd_3967473 := by exact prefixLift 3967473
  have htrace : WordTrace (prefixWord ++ tailWord_3967473) baseStart_3967473 baseEnd_3967473 := by
    simpa [prefixWord, tailWord_3967473, baseEnd_3967473] using wordTrace_append hprefix tailTrace_3967473
  have hstable : (prefixWord ++ tailWord_3967473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967473).length < 2 ^ (prefixWord ++ tailWord_3967473).sum := by decide
  have hdescent : baseEnd_3967473 < baseStart_3967473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967492 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3967492 : Nat := 118140960795 + 3967492 * 2 ^ 59
def prefixEnd_3967492 : Nat := 4983230072969 + 3 ^ 40 * 3967492 * 2
def baseEnd_3967492 : Nat := 1358153592578730935335895

theorem tailTrace_3967492 : CollatzResearch.WordTrace tailWord_3967492 prefixEnd_3967492 1358153592578730935335895 := by
  unfold tailWord_3967492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72353160671230776266360365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96470880894974368355147153 72353160671230776266360365)
  ·
    refine ⟨27132435251711541099885137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72353160671230776266360365 27132435251711541099885137)
    ·
      refine ⟨20349326438783655824913853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27132435251711541099885137 20349326438783655824913853)
      ·
        refine ⟨7630997414543870934342695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20349326438783655824913853 7630997414543870934342695)
        ·
          refine ⟨11446496121815806401514043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7630997414543870934342695 11446496121815806401514043)
          ·
            refine ⟨17169744182723709602271065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11446496121815806401514043 17169744182723709602271065)
            ·
              refine ⟨12877308137042782201703299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17169744182723709602271065 12877308137042782201703299)
              ·
                refine ⟨19315962205564173302554949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12877308137042782201703299 19315962205564173302554949)
                ·
                  refine ⟨3621742913543282494229053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19315962205564173302554949 3621742913543282494229053)
                  ·
                    refine ⟨1358153592578730935335895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3621742913543282494229053 1358153592578730935335895)
                    ·
                      rfl

theorem cell22_3967492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3967492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967492 prefixEnd_3967492 := by exact prefixLift 3967492
  have htrace : WordTrace (prefixWord ++ tailWord_3967492) baseStart_3967492 baseEnd_3967492 := by
    simpa [prefixWord, tailWord_3967492, baseEnd_3967492] using wordTrace_append hprefix tailTrace_3967492
  have hstable : (prefixWord ++ tailWord_3967492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967492).length < 2 ^ (prefixWord ++ tailWord_3967492).sum := by decide
  have hdescent : baseEnd_3967492 < baseStart_3967492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967524 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3967524 : Nat := 118140960795 + 3967524 * 2 ^ 59
def prefixEnd_3967524 : Nat := 4983230072969 + 3 ^ 40 * 3967524 * 2
def baseEnd_3967524 : Nat := 1358164546832693518535797

theorem tailTrace_3967524 : CollatzResearch.WordTrace tailWord_3967524 prefixEnd_3967524 1358164546832693518535797 := by
  unfold tailWord_3967524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72353744239172810998942813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96471658985563747998590417 72353744239172810998942813)
  ·
    refine ⟨27132654089689804124603555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72353744239172810998942813 27132654089689804124603555)
    ·
      refine ⟨40698981134534706186905333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27132654089689804124603555 40698981134534706186905333)
      ·
        refine ⟨3815529481362628705022375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40698981134534706186905333 3815529481362628705022375)
        ·
          refine ⟨5723294222043943057533563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815529481362628705022375 5723294222043943057533563)
          ·
            refine ⟨8584941333065914586300345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723294222043943057533563 8584941333065914586300345)
            ·
              refine ⟨6438705999799435939725259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8584941333065914586300345 6438705999799435939725259)
              ·
                refine ⟨9658058999699153909587889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438705999799435939725259 9658058999699153909587889)
                ·
                  refine ⟨7243544249774365432190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658058999699153909587889 7243544249774365432190917)
                  ·
                    refine ⟨1358164546832693518535797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7243544249774365432190917 1358164546832693518535797)
                    ·
                      rfl

theorem cell22_3967524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3967524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967524 prefixEnd_3967524 := by exact prefixLift 3967524
  have htrace : WordTrace (prefixWord ++ tailWord_3967524) baseStart_3967524 baseEnd_3967524 := by
    simpa [prefixWord, tailWord_3967524, baseEnd_3967524] using wordTrace_append hprefix tailTrace_3967524
  have hstable : (prefixWord ++ tailWord_3967524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967524).length < 2 ^ (prefixWord ++ tailWord_3967524).sum := by decide
  have hdescent : baseEnd_3967524 < baseStart_3967524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967556 : List Nat := [2, 3, 5, 1, 1, 2, 1, 7]
def baseStart_3967556 : Nat := 118140960795 + 3967556 * 2 ^ 59
def prefixEnd_3967556 : Nat := 4983230072969 + 3 ^ 40 * 3967556 * 2
def baseEnd_3967556 : Nat := 150908389009628455748411

theorem tailTrace_3967556 : CollatzResearch.WordTrace tailWord_3967556 prefixEnd_3967556 150908389009628455748411 := by
  unfold tailWord_3967556
  simp only [CollatzResearch.WordTrace]
  refine ⟨72354327807114845731525261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96472437076153127642033681 72354327807114845731525261)
  ·
    refine ⟨27132872927668067149321973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72354327807114845731525261 27132872927668067149321973)
    ·
      refine ⟨2543706836968881295248935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27132872927668067149321973 2543706836968881295248935)
      ·
        refine ⟨3815560255453321942873403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543706836968881295248935 3815560255453321942873403)
        ·
          refine ⟨5723340383179982914310105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815560255453321942873403 5723340383179982914310105)
          ·
            refine ⟨4292505287384987185732579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723340383179982914310105 4292505287384987185732579)
            ·
              refine ⟨6438757931077480778598869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292505287384987185732579 6438757931077480778598869)
              ·
                refine ⟨150908389009628455748411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6438757931077480778598869 150908389009628455748411)
                ·
                  rfl

theorem cell22_3967556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_3967556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967556 prefixEnd_3967556 := by exact prefixLift 3967556
  have htrace : WordTrace (prefixWord ++ tailWord_3967556) baseStart_3967556 baseEnd_3967556 := by
    simpa [prefixWord, tailWord_3967556, baseEnd_3967556] using wordTrace_append hprefix tailTrace_3967556
  have hstable : (prefixWord ++ tailWord_3967556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967556).length < 2 ^ (prefixWord ++ tailWord_3967556).sum := by decide
  have hdescent : baseEnd_3967556 < baseStart_3967556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967612 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_3967612 : Nat := 118140960795 + 3967612 * 2 ^ 59
def prefixEnd_3967612 : Nat := 4983230072969 + 3 ^ 40 * 3967612 * 2
def baseEnd_3967612 : Nat := 452731557010363540778509

theorem tailTrace_3967612 : CollatzResearch.WordTrace tailWord_3967612 prefixEnd_3967612 452731557010363540778509 := by
  unfold tailWord_3967612
  simp only [CollatzResearch.WordTrace]
  refine ⟨72355349051013406513544545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96473798734684542018059393 72355349051013406513544545)
  ·
    refine ⟨54266511788260054885158409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72355349051013406513544545 54266511788260054885158409)
    ·
      refine ⟨40699883841195041163868807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54266511788260054885158409 40699883841195041163868807)
      ·
        refine ⟨61049825761792561745803211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40699883841195041163868807 61049825761792561745803211)
        ·
          refine ⟨91574738642688842618704817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61049825761792561745803211 91574738642688842618704817)
          ·
            refine ⟨68681053982016631964028613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91574738642688842618704817 68681053982016631964028613)
            ·
              refine ⟨12877697621628118493255365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68681053982016631964028613 12877697621628118493255365)
              ·
                refine ⟨2414568304055272217485381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12877697621628118493255365 2414568304055272217485381)
                ·
                  refine ⟨452731557010363540778509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414568304055272217485381 452731557010363540778509)
                  ·
                    rfl

theorem cell22_3967612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_3967612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967612 prefixEnd_3967612 := by exact prefixLift 3967612
  have htrace : WordTrace (prefixWord ++ tailWord_3967612) baseStart_3967612 baseEnd_3967612 := by
    simpa [prefixWord, tailWord_3967612, baseEnd_3967612] using wordTrace_append hprefix tailTrace_3967612
  have hstable : (prefixWord ++ tailWord_3967612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967612).length < 2 ^ (prefixWord ++ tailWord_3967612).sum := by decide
  have hdescent : baseEnd_3967612 < baseStart_3967612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967640 : List Nat := [2, 1, 2, 4, 1, 1, 3, 8]
def baseStart_3967640 : Nat := 118140960795 + 3967640 * 2 ^ 59
def prefixEnd_3967640 : Nat := 4983230072969 + 3 ^ 40 * 3967640 * 2
def baseEnd_3967640 : Nat := 150911584000367542515049

theorem tailTrace_3967640 : CollatzResearch.WordTrace tailWord_3967640 prefixEnd_3967640 150911584000367542515049 := by
  unfold tailWord_3967640
  simp only [CollatzResearch.WordTrace]
  refine ⟨72355859672962686904554187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96474479563950249206072249 72355859672962686904554187)
  ·
    refine ⟨108533789509444030356831281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72355859672962686904554187 108533789509444030356831281)
    ·
      refine ⟨81400342132083022767623461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108533789509444030356831281 81400342132083022767623461)
      ·
        refine ⟨15262564149765566768929399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81400342132083022767623461 15262564149765566768929399)
        ·
          refine ⟨22893846224648350153394099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15262564149765566768929399 22893846224648350153394099)
          ·
            refine ⟨34340769336972525230091149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22893846224648350153394099 34340769336972525230091149)
            ·
              refine ⟨12877788501364696961284181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34340769336972525230091149 12877788501364696961284181)
              ·
                refine ⟨150911584000367542515049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12877788501364696961284181 150911584000367542515049)
                ·
                  rfl

theorem cell22_3967640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_3967640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967640 prefixEnd_3967640 := by exact prefixLift 3967640
  have htrace : WordTrace (prefixWord ++ tailWord_3967640) baseStart_3967640 baseEnd_3967640 := by
    simpa [prefixWord, tailWord_3967640, baseEnd_3967640] using wordTrace_append hprefix tailTrace_3967640
  have hstable : (prefixWord ++ tailWord_3967640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967640).length < 2 ^ (prefixWord ++ tailWord_3967640).sum := by decide
  have hdescent : baseEnd_3967640 < baseStart_3967640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967777 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3967777 : Nat := 118140960795 + 3967777 * 2 ^ 59
def prefixEnd_3967777 : Nat := 4983230072969 + 3 ^ 40 * 3967777 * 2
def baseEnd_3967777 : Nat := 1358251153903085191960021

theorem tailTrace_3967777 : CollatzResearch.WordTrace tailWord_3967777 prefixEnd_3967777 1358251153903085191960021 := by
  unfold tailWord_3967777
  simp only [CollatzResearch.WordTrace]
  refine ⟨144716716146429046206845585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96477810764286030804563723 144716716146429046206845585)
  ·
    refine ⟨108537537109821784655134189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144716716146429046206845585 108537537109821784655134189)
    ·
      refine ⟨40701576416183169245675321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108537537109821784655134189 40701576416183169245675321)
      ·
        refine ⟨30526182312137376934256491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40701576416183169245675321 30526182312137376934256491)
        ·
          refine ⟨45789273468206065401384737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30526182312137376934256491 45789273468206065401384737)
          ·
            refine ⟨34341955101154549051038553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45789273468206065401384737 34341955101154549051038553)
            ·
              refine ⟨25756466325865911788278915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34341955101154549051038553 25756466325865911788278915)
              ·
                refine ⟨38634699488798867682418373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25756466325865911788278915 38634699488798867682418373)
                ·
                  refine ⟨7244006154149787690453445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38634699488798867682418373 7244006154149787690453445)
                  ·
                    refine ⟨1358251153903085191960021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244006154149787690453445 1358251153903085191960021)
                    ·
                      rfl

theorem cell22_3967777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3967777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967777 prefixEnd_3967777 := by exact prefixLift 3967777
  have htrace : WordTrace (prefixWord ++ tailWord_3967777) baseStart_3967777 baseEnd_3967777 := by
    simpa [prefixWord, tailWord_3967777, baseEnd_3967777] using wordTrace_append hprefix tailTrace_3967777
  have hstable : (prefixWord ++ tailWord_3967777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967777).length < 2 ^ (prefixWord ++ tailWord_3967777).sum := by decide
  have hdescent : baseEnd_3967777 < baseStart_3967777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967852 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_3967852 : Nat := 118140960795 + 3967852 * 2 ^ 59
def prefixEnd_3967852 : Nat := 4983230072969 + 3 ^ 40 * 3967852 * 2
def baseEnd_3967852 : Nat := 1358276827935809996334791

theorem tailTrace_3967852 : CollatzResearch.WordTrace tailWord_3967852 prefixEnd_3967852 1358276827935809996334791 := by
  unfold tailWord_3967852
  simp only [CollatzResearch.WordTrace]
  refine ⟨72359725810578667007912905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96479634414104889343883873 72359725810578667007912905)
  ·
    refine ⟨54269794357934000255934679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72359725810578667007912905 54269794357934000255934679)
    ·
      refine ⟨81404691536901000383902019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54269794357934000255934679 81404691536901000383902019)
      ·
        refine ⟨122107037305351500575853029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81404691536901000383902019 122107037305351500575853029)
        ·
          refine ⟨22895069494753406357972443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122107037305351500575853029 22895069494753406357972443)
          ·
            refine ⟨34342604242130109536958665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22895069494753406357972443 34342604242130109536958665)
            ·
              refine ⟨25756953181597582152718999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34342604242130109536958665 25756953181597582152718999)
              ·
                refine ⟨38635429772396373229078499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25756953181597582152718999 38635429772396373229078499)
                ·
                  refine ⟨57953144658594559843617749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38635429772396373229078499 57953144658594559843617749)
                  ·
                    refine ⟨1358276827935809996334791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57953144658594559843617749 1358276827935809996334791)
                    ·
                      rfl

theorem cell22_3967852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_3967852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967852 prefixEnd_3967852 := by exact prefixLift 3967852
  have htrace : WordTrace (prefixWord ++ tailWord_3967852) baseStart_3967852 baseEnd_3967852 := by
    simpa [prefixWord, tailWord_3967852, baseEnd_3967852] using wordTrace_append hprefix tailTrace_3967852
  have hstable : (prefixWord ++ tailWord_3967852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967852).length < 2 ^ (prefixWord ++ tailWord_3967852).sum := by decide
  have hdescent : baseEnd_3967852 < baseStart_3967852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967884 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_3967884 : Nat := 118140960795 + 3967884 * 2 ^ 59
def prefixEnd_3967884 : Nat := 4983230072969 + 3 ^ 40 * 3967884 * 2
def baseEnd_3967884 : Nat := 1358287782189772579534693

theorem tailTrace_3967884 : CollatzResearch.WordTrace tailWord_3967884 prefixEnd_3967884 1358287782189772579534693 := by
  unfold tailWord_3967884
  simp only [CollatzResearch.WordTrace]
  refine ⟨72360309378520701740495353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96480412504694268987327137 72360309378520701740495353)
  ·
    refine ⟨54270232033890526305371515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72360309378520701740495353 54270232033890526305371515)
    ·
      refine ⟨81405348050835789458057273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54270232033890526305371515 81405348050835789458057273)
      ·
        refine ⟨61054011038126842093542955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81405348050835789458057273 61054011038126842093542955)
        ·
          refine ⟨91581016557190263140314433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61054011038126842093542955 91581016557190263140314433)
          ·
            refine ⟨68685762417892697355235825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91581016557190263140314433 68685762417892697355235825)
            ·
              refine ⟨51514321813419523016426869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68685762417892697355235825 51514321813419523016426869)
              ·
                refine ⟨4829467670008080282790019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51514321813419523016426869 4829467670008080282790019)
                ·
                  refine ⟨7244201505012120424185029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829467670008080282790019 7244201505012120424185029)
                  ·
                    refine ⟨1358287782189772579534693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244201505012120424185029 1358287782189772579534693)
                    ·
                      rfl

theorem cell22_3967884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_3967884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967884 prefixEnd_3967884 := by exact prefixLift 3967884
  have htrace : WordTrace (prefixWord ++ tailWord_3967884) baseStart_3967884 baseEnd_3967884 := by
    simpa [prefixWord, tailWord_3967884, baseEnd_3967884] using wordTrace_append hprefix tailTrace_3967884
  have hstable : (prefixWord ++ tailWord_3967884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967884).length < 2 ^ (prefixWord ++ tailWord_3967884).sum := by decide
  have hdescent : baseEnd_3967884 < baseStart_3967884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967897 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_3967897 : Nat := 118140960795 + 3967897 * 2 ^ 59
def prefixEnd_3967897 : Nat := 4983230072969 + 3 ^ 40 * 3967897 * 2
def baseEnd_3967897 : Nat := 1358292232355444878959653

theorem tailTrace_3967897 : CollatzResearch.WordTrace tailWord_3967897 prefixEnd_3967897 1358292232355444878959653 := by
  unfold tailWord_3967897
  simp only [CollatzResearch.WordTrace]
  refine ⟨144721092905994306701213945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96480728603996204467475963 144721092905994306701213945)
  ·
    refine ⟨108540819679495730025910459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144721092905994306701213945 108540819679495730025910459)
    ·
      refine ⟨162811229519243595038865689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108540819679495730025910459 162811229519243595038865689)
      ·
        refine ⟨122108422139432696279149267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162811229519243595038865689 122108422139432696279149267)
        ·
          refine ⟨183162633209149044418723901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122108422139432696279149267 183162633209149044418723901)
          ·
            refine ⟨68685987453430891657021463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183162633209149044418723901 68685987453430891657021463)
            ·
              refine ⟨103028981180146337485532195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68685987453430891657021463 103028981180146337485532195)
              ·
                refine ⟨154543471770219506228298293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103028981180146337485532195 154543471770219506228298293)
                ·
                  refine ⟨14488450478458078708902965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154543471770219506228298293 14488450478458078708902965)
                  ·
                    refine ⟨1358292232355444878959653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14488450478458078708902965 1358292232355444878959653)
                    ·
                      rfl

theorem cell22_3967897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_3967897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967897 prefixEnd_3967897 := by exact prefixLift 3967897
  have htrace : WordTrace (prefixWord ++ tailWord_3967897) baseStart_3967897 baseEnd_3967897 := by
    simpa [prefixWord, tailWord_3967897, baseEnd_3967897] using wordTrace_append hprefix tailTrace_3967897
  have hstable : (prefixWord ++ tailWord_3967897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967897).length < 2 ^ (prefixWord ++ tailWord_3967897).sum := by decide
  have hdescent : baseEnd_3967897 < baseStart_3967897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967927 : List Nat := [1, 1, 3, 1, 3, 1, 2, 10]
def baseStart_3967927 : Nat := 118140960795 + 3967927 * 2 ^ 59
def prefixEnd_3967927 : Nat := 4983230072969 + 3 ^ 40 * 3967927 * 2
def baseEnd_3967927 : Nat := 150922500218726088967729

theorem tailTrace_3967927 : CollatzResearch.WordTrace tailWord_3967927 prefixEnd_3967927 150922500218726088967729 := by
  unfold tailWord_3967927
  simp only [CollatzResearch.WordTrace]
  refine ⟨144722187095885621824806035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96481458063923747883204023 144722187095885621824806035)
  ·
    refine ⟨217083280643828432737209053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144722187095885621824806035 217083280643828432737209053)
    ·
      refine ⟨81406230241435662276453395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217083280643828432737209053 81406230241435662276453395)
      ·
        refine ⟨122109345362153493414680093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81406230241435662276453395 122109345362153493414680093)
        ·
          refine ⟨45791004510807560030505035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122109345362153493414680093 45791004510807560030505035)
          ·
            refine ⟨68686506766211340045757553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45791004510807560030505035 68686506766211340045757553)
            ·
              refine ⟨51514880074658505034318165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68686506766211340045757553 51514880074658505034318165)
              ·
                refine ⟨150922500218726088967729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 51514880074658505034318165 150922500218726088967729)
                ·
                  rfl

theorem cell22_3967927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 10].length) (baseStart_3967927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967927 prefixEnd_3967927 := by exact prefixLift 3967927
  have htrace : WordTrace (prefixWord ++ tailWord_3967927) baseStart_3967927 baseEnd_3967927 := by
    simpa [prefixWord, tailWord_3967927, baseEnd_3967927] using wordTrace_append hprefix tailTrace_3967927
  have hstable : (prefixWord ++ tailWord_3967927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967927).length < 2 ^ (prefixWord ++ tailWord_3967927).sum := by decide
  have hdescent : baseEnd_3967927 < baseStart_3967927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967929 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_3967929 : Nat := 118140960795 + 3967929 * 2 ^ 59
def prefixEnd_3967929 : Nat := 4983230072969 + 3 ^ 40 * 3967929 * 2
def baseEnd_3967929 : Nat := 1358303186609407462159555

theorem tailTrace_3967929 : CollatzResearch.WordTrace tailWord_3967929 prefixEnd_3967929 1358303186609407462159555 := by
  unfold tailWord_3967929
  simp only [CollatzResearch.WordTrace]
  refine ⟨144722260041878376166378841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96481506694585584110919227 144722260041878376166378841)
  ·
    refine ⟨108541695031408782124784131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144722260041878376166378841 108541695031408782124784131)
    ·
      refine ⟨162812542547113173187176197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108541695031408782124784131 162812542547113173187176197)
      ·
        refine ⟨30527351727583719972595537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162812542547113173187176197 30527351727583719972595537)
        ·
          refine ⟨22895513795687789979446653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30527351727583719972595537 22895513795687789979446653)
          ·
            refine ⟨8585817673382921242292495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22895513795687789979446653 8585817673382921242292495)
            ·
              refine ⟨12878726510074381863438743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8585817673382921242292495 12878726510074381863438743)
              ·
                refine ⟨19318089765111572795158115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12878726510074381863438743 19318089765111572795158115)
                ·
                  refine ⟨28977134647667359192737173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19318089765111572795158115 28977134647667359192737173)
                  ·
                    refine ⟨1358303186609407462159555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28977134647667359192737173 1358303186609407462159555)
                    ·
                      rfl

theorem cell22_3967929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_3967929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967929 prefixEnd_3967929 := by exact prefixLift 3967929
  have htrace : WordTrace (prefixWord ++ tailWord_3967929) baseStart_3967929 baseEnd_3967929 := by
    simpa [prefixWord, tailWord_3967929, baseEnd_3967929] using wordTrace_append hprefix tailTrace_3967929
  have hstable : (prefixWord ++ tailWord_3967929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967929).length < 2 ^ (prefixWord ++ tailWord_3967929).sum := by decide
  have hdescent : baseEnd_3967929 < baseStart_3967929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967933 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 4]
def baseStart_3967933 : Nat := 118140960795 + 3967933 * 2 ^ 59
def prefixEnd_3967933 : Nat := 4983230072969 + 3 ^ 40 * 3967933 * 2
def baseEnd_3967933 : Nat := 452768185297050928353181

theorem tailTrace_3967933 : CollatzResearch.WordTrace tailWord_3967933 prefixEnd_3967933 452768185297050928353181 := by
  unfold tailWord_3967933
  simp only [CollatzResearch.WordTrace]
  refine ⟨144722405933863884849524453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96481603955909256566349635 144722405933863884849524453)
  ·
    refine ⟨27135451112599478409285835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144722405933863884849524453 27135451112599478409285835)
    ·
      refine ⟨40703176668899217613928753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27135451112599478409285835 40703176668899217613928753)
      ·
        refine ⟨30527382501674413210446565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40703176668899217613928753 30527382501674413210446565)
        ·
          refine ⟨5723884219063952476958731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30527382501674413210446565 5723884219063952476958731)
          ·
            refine ⟨8585826328595928715438097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723884219063952476958731 8585826328595928715438097)
            ·
              refine ⟨6439369746446946536578573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585826328595928715438097 6439369746446946536578573)
              ·
                refine ⟨2414763654917604951216965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6439369746446946536578573 2414763654917604951216965)
                ·
                  refine ⟨452768185297050928353181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414763654917604951216965 452768185297050928353181)
                  ·
                    rfl

theorem cell22_3967933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_3967933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967933 prefixEnd_3967933 := by exact prefixLift 3967933
  have htrace : WordTrace (prefixWord ++ tailWord_3967933) baseStart_3967933 baseEnd_3967933 := by
    simpa [prefixWord, tailWord_3967933, baseEnd_3967933] using wordTrace_append hprefix tailTrace_3967933
  have hstable : (prefixWord ++ tailWord_3967933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967933).length < 2 ^ (prefixWord ++ tailWord_3967933).sum := by decide
  have hdescent : baseEnd_3967933 < baseStart_3967933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967944 : List Nat := [2, 1, 3, 1, 5, 1, 9]
def baseStart_3967944 : Nat := 118140960795 + 3967944 * 2 ^ 59
def prefixEnd_3967944 : Nat := 4983230072969 + 3 ^ 40 * 3967944 * 2
def baseEnd_3967944 : Nat := 50307715607998237890167

theorem tailTrace_3967944 : CollatzResearch.WordTrace tailWord_3967944 prefixEnd_3967944 50307715607998237890167 := by
  unfold tailWord_3967944
  simp only [CollatzResearch.WordTrace]
  refine ⟨72361403568412016864087443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96481871424549355818783257 72361403568412016864087443)
  ·
    refine ⟨108542105352618025296131165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72361403568412016864087443 108542105352618025296131165)
    ·
      refine ⟨40703289507231759486049187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108542105352618025296131165 40703289507231759486049187)
      ·
        refine ⟨61054934260847639229073781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40703289507231759486049187 61054934260847639229073781)
        ·
          refine ⟨5723900086954466177725667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61054934260847639229073781 5723900086954466177725667)
          ·
            refine ⟨8585850130431699266588501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723900086954466177725667 8585850130431699266588501)
            ·
              refine ⟨50307715607998237890167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8585850130431699266588501 50307715607998237890167)
              ·
                rfl

theorem cell22_3967944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 9].length) (baseStart_3967944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967944 prefixEnd_3967944 := by exact prefixLift 3967944
  have htrace : WordTrace (prefixWord ++ tailWord_3967944) baseStart_3967944 baseEnd_3967944 := by
    simpa [prefixWord, tailWord_3967944, baseEnd_3967944] using wordTrace_append hprefix tailTrace_3967944
  have hstable : (prefixWord ++ tailWord_3967944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967944).length < 2 ^ (prefixWord ++ tailWord_3967944).sum := by decide
  have hdescent : baseEnd_3967944 < baseStart_3967944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967965 : List Nat := [1, 4, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3967965 : Nat := 118140960795 + 3967965 * 2 ^ 59
def prefixEnd_3967965 : Nat := 4983230072969 + 3 ^ 40 * 3967965 * 2
def baseEnd_3967965 : Nat := 1358315510145115368259445

theorem tailTrace_3967965 : CollatzResearch.WordTrace tailWord_3967965 prefixEnd_3967965 1358315510145115368259445 := by
  unfold tailWord_3967965
  simp only [CollatzResearch.WordTrace]
  refine ⟨144723573069747954314689349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96482382046498636209792899 144723573069747954314689349)
  ·
    refine ⟨27135669950577741434004253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144723573069747954314689349 27135669950577741434004253)
    ·
      refine ⟨10175876231466653037751595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27135669950577741434004253 10175876231466653037751595)
      ·
        refine ⟨15263814347199979556627393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10175876231466653037751595 15263814347199979556627393)
        ·
          refine ⟨11447860760399984667470545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15263814347199979556627393 11447860760399984667470545)
          ·
            refine ⟨8585895570299988500602909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11447860760399984667470545 8585895570299988500602909)
            ·
              refine ⟨3219710838862495687726091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8585895570299988500602909 3219710838862495687726091)
              ·
                refine ⟨4829566258293743531589137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219710838862495687726091 4829566258293743531589137)
                ·
                  refine ⟨3622174693720307648691853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829566258293743531589137 3622174693720307648691853)
                  ·
                    refine ⟨1358315510145115368259445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622174693720307648691853 1358315510145115368259445)
                    ·
                      rfl

theorem cell22_3967965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3967965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967965 prefixEnd_3967965 := by exact prefixLift 3967965
  have htrace : WordTrace (prefixWord ++ tailWord_3967965) baseStart_3967965 baseEnd_3967965 := by
    simpa [prefixWord, tailWord_3967965, baseEnd_3967965] using wordTrace_append hprefix tailTrace_3967965
  have hstable : (prefixWord ++ tailWord_3967965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967965).length < 2 ^ (prefixWord ++ tailWord_3967965).sum := by decide
  have hdescent : baseEnd_3967965 < baseStart_3967965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3967976 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3967976 : Nat := 118140960795 + 3967976 * 2 ^ 59
def prefixEnd_3967976 : Nat := 4983230072969 + 3 ^ 40 * 3967976 * 2
def baseEnd_3967976 : Nat := 1358319275669915006234411

theorem tailTrace_3967976 : CollatzResearch.WordTrace tailWord_3967976 prefixEnd_3967976 1358319275669915006234411 := by
  unfold tailWord_3967976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72361987136354051596669891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96482649515138735462226521 72361987136354051596669891)
  ·
    refine ⟨108542980704531077395004837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72361987136354051596669891 108542980704531077395004837)
    ·
      refine ⟨20351808882099577011563407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108542980704531077395004837 20351808882099577011563407)
      ·
        refine ⟨30527713323149365517345111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20351808882099577011563407 30527713323149365517345111)
        ·
          refine ⟨45791569984724048276017667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30527713323149365517345111 45791569984724048276017667)
          ·
            refine ⟨68687354977086072414026501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45791569984724048276017667 68687354977086072414026501)
            ·
              refine ⟨12878879058203638577629969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68687354977086072414026501 12878879058203638577629969)
              ·
                refine ⟨9659159293652728933222477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12878879058203638577629969 9659159293652728933222477)
                ·
                  refine ⟨3622184735119773349958429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9659159293652728933222477 3622184735119773349958429)
                  ·
                    refine ⟨1358319275669915006234411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622184735119773349958429 1358319275669915006234411)
                    ·
                      rfl

theorem cell22_3967976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3967976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3967976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3967976 prefixEnd_3967976 := by exact prefixLift 3967976
  have htrace : WordTrace (prefixWord ++ tailWord_3967976) baseStart_3967976 baseEnd_3967976 := by
    simpa [prefixWord, tailWord_3967976, baseEnd_3967976] using wordTrace_append hprefix tailTrace_3967976
  have hstable : (prefixWord ++ tailWord_3967976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3967976).length < 2 ^ (prefixWord ++ tailWord_3967976).sum := by decide
  have hdescent : baseEnd_3967976 < baseStart_3967976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3967976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968019 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_3968019 : Nat := 118140960795 + 3968019 * 2 ^ 59
def prefixEnd_3968019 : Nat := 4983230072969 + 3 ^ 40 * 3968019 * 2
def baseEnd_3968019 : Nat := 1358333995448677227409279

theorem tailTrace_3968019 : CollatzResearch.WordTrace tailWord_3968019 prefixEnd_3968019 1358333995448677227409279 := by
  unfold tailWord_3968019
  simp only [CollatzResearch.WordTrace]
  refine ⟨144725542611552321537155111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96483695074368214358103407 144725542611552321537155111)
  ·
    refine ⟨217088313917328482305732667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144725542611552321537155111 217088313917328482305732667)
    ·
      refine ⟨325632470875992723458599001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217088313917328482305732667 325632470875992723458599001)
      ·
        refine ⟨244224353156994542593949251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325632470875992723458599001 244224353156994542593949251)
        ·
          refine ⟨366336529735491813890923877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244224353156994542593949251 366336529735491813890923877)
          ·
            refine ⟨68688099325404715104548227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366336529735491813890923877 68688099325404715104548227)
            ·
              refine ⟨103032148988107072656822341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68688099325404715104548227 103032148988107072656822341)
              ·
                refine ⟨19318527935270076123154189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103032148988107072656822341 19318527935270076123154189)
                ·
                  refine ⟨7244447975726278546182821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19318527935270076123154189 7244447975726278546182821)
                  ·
                    refine ⟨1358333995448677227409279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244447975726278546182821 1358333995448677227409279)
                    ·
                      rfl

theorem cell22_3968019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_3968019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968019 prefixEnd_3968019 := by exact prefixLift 3968019
  have htrace : WordTrace (prefixWord ++ tailWord_3968019) baseStart_3968019 baseEnd_3968019 := by
    simpa [prefixWord, tailWord_3968019, baseEnd_3968019] using wordTrace_append hprefix tailTrace_3968019
  have hstable : (prefixWord ++ tailWord_3968019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968019).length < 2 ^ (prefixWord ++ tailWord_3968019).sum := by decide
  have hdescent : baseEnd_3968019 < baseStart_3968019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968023 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 5]
def baseStart_3968023 : Nat := 118140960795 + 3968023 * 2 ^ 59
def prefixEnd_3968023 : Nat := 4983230072969 + 3 ^ 40 * 3968023 * 2
def baseEnd_3968023 : Nat := 452778454910140850103089

theorem tailTrace_3968023 : CollatzResearch.WordTrace tailWord_3968023 prefixEnd_3968023 452778454910140850103089 := by
  unfold tailWord_3968023
  simp only [CollatzResearch.WordTrace]
  refine ⟨144725688503537830220300723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96483792335691886813533815 144725688503537830220300723)
  ·
    refine ⟨217088532755306745330451085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144725688503537830220300723 217088532755306745330451085)
    ·
      refine ⟨81408199783240029498919157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217088532755306745330451085 81408199783240029498919157)
      ·
        refine ⟨7632018729678752765523671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81408199783240029498919157 7632018729678752765523671)
        ·
          refine ⟨11448028094518129148285507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632018729678752765523671 11448028094518129148285507)
          ·
            refine ⟨17172042141777193722428261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448028094518129148285507 17172042141777193722428261)
            ·
              refine ⟨3219757901583223822955299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17172042141777193722428261 3219757901583223822955299)
              ·
                refine ⟨4829636852374835734432949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219757901583223822955299 4829636852374835734432949)
                ·
                  refine ⟨452778454910140850103089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4829636852374835734432949 452778454910140850103089)
                  ·
                    rfl

theorem cell22_3968023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 5].length) (baseStart_3968023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968023 prefixEnd_3968023 := by exact prefixLift 3968023
  have htrace : WordTrace (prefixWord ++ tailWord_3968023) baseStart_3968023 baseEnd_3968023 := by
    simpa [prefixWord, tailWord_3968023, baseEnd_3968023] using wordTrace_append hprefix tailTrace_3968023
  have hstable : (prefixWord ++ tailWord_3968023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968023).length < 2 ^ (prefixWord ++ tailWord_3968023).sum := by decide
  have hdescent : baseEnd_3968023 < baseStart_3968023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968051 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 4]
def baseStart_3968051 : Nat := 118140960795 + 3968051 * 2 ^ 59
def prefixEnd_3968051 : Nat := 4983230072969 + 3 ^ 40 * 3968051 * 2
def baseEnd_3968051 : Nat := 452781649900879936869727

theorem tailTrace_3968051 : CollatzResearch.WordTrace tailWord_3968051 prefixEnd_3968051 452781649900879936869727 := by
  unfold tailWord_3968051
  simp only [CollatzResearch.WordTrace]
  refine ⟨144726709747436391002320007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96484473164957594001546671 144726709747436391002320007)
  ·
    refine ⟨217090064621154586503480011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144726709747436391002320007 217090064621154586503480011)
    ·
      refine ⟨325635096931731879755220017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217090064621154586503480011 325635096931731879755220017)
      ·
        refine ⟨244226322698798909816415013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 325635096931731879755220017 244226322698798909816415013)
        ·
          refine ⟨45792435506024795590577815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244226322698798909816415013 45792435506024795590577815)
          ·
            refine ⟨68688653259037193385866723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45792435506024795590577815 68688653259037193385866723)
            ·
              refine ⟨103032979888555790078800085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68688653259037193385866723 103032979888555790078800085)
              ·
                refine ⟨2414835466138026329971877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103032979888555790078800085 2414835466138026329971877)
                ·
                  refine ⟨452781649900879936869727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414835466138026329971877 452781649900879936869727)
                  ·
                    rfl

theorem cell22_3968051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 4].length) (baseStart_3968051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968051 prefixEnd_3968051 := by exact prefixLift 3968051
  have htrace : WordTrace (prefixWord ++ tailWord_3968051) baseStart_3968051 baseEnd_3968051 := by
    simpa [prefixWord, tailWord_3968051, baseEnd_3968051] using wordTrace_append hprefix tailTrace_3968051
  have hstable : (prefixWord ++ tailWord_3968051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968051).length < 2 ^ (prefixWord ++ tailWord_3968051).sum := by decide
  have hdescent : baseEnd_3968051 < baseStart_3968051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968096 : List Nat := [2, 1, 1, 3, 2, 2, 5, 6]
def baseStart_3968096 : Nat := 118140960795 + 3968096 * 2 ^ 59
def prefixEnd_3968096 : Nat := 4983230072969 + 3 ^ 40 * 3968096 * 2
def baseEnd_3968096 : Nat := 150928928235808299248227

theorem tailTrace_3968096 : CollatzResearch.WordTrace tailWord_3968096 prefixEnd_3968096 150928928235808299248227 := by
  unfold tailWord_3968096
  simp only [CollatzResearch.WordTrace]
  refine ⟨72364175516136681843854071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96485567354848909125138761 72364175516136681843854071)
  ·
    refine ⟨108546263274205022765781107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72364175516136681843854071 108546263274205022765781107)
    ·
      refine ⟨162819394911307534148671661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108546263274205022765781107 162819394911307534148671661)
      ·
        refine ⟨61057273091740325305751873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162819394911307534148671661 61057273091740325305751873)
        ·
          refine ⟨45792954818805243979313905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61057273091740325305751873 45792954818805243979313905)
          ·
            refine ⟨34344716114103932984485429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45792954818805243979313905 34344716114103932984485429)
            ·
              refine ⟨3219817135697243717295509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34344716114103932984485429 3219817135697243717295509)
              ·
                refine ⟨150928928235808299248227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3219817135697243717295509 150928928235808299248227)
                ·
                  rfl

theorem cell22_3968096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_3968096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968096 prefixEnd_3968096 := by exact prefixLift 3968096
  have htrace : WordTrace (prefixWord ++ tailWord_3968096) baseStart_3968096 baseEnd_3968096 := by
    simpa [prefixWord, tailWord_3968096, baseEnd_3968096] using wordTrace_append hprefix tailTrace_3968096
  have hstable : (prefixWord ++ tailWord_3968096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968096).length < 2 ^ (prefixWord ++ tailWord_3968096).sum := by decide
  have hdescent : baseEnd_3968096 < baseStart_3968096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968098 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3968098 : Nat := 118140960795 + 3968098 * 2 ^ 59
def prefixEnd_3968098 : Nat := 4983230072969 + 3 ^ 40 * 3968098 * 2
def baseEnd_3968098 : Nat := 1358361038763147354684037

theorem tailTrace_3968098 : CollatzResearch.WordTrace tailWord_3968098 prefixEnd_3968098 1358361038763147354684037 := by
  unfold tailWord_3968098
  simp only [CollatzResearch.WordTrace]
  refine ⟨36182105994566529507320237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96485615985510745352853965 36182105994566529507320237)
  ·
    refine ⟨13568289747962448565245089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36182105994566529507320237 13568289747962448565245089)
    ·
      refine ⟨10176217310971836423933817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13568289747962448565245089 10176217310971836423933817)
      ·
        refine ⟨7632162983228877317950363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10176217310971836423933817 7632162983228877317950363)
        ·
          refine ⟨11448244474843315976925545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7632162983228877317950363 11448244474843315976925545)
          ·
            refine ⟨8586183356132486982694159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11448244474843315976925545 8586183356132486982694159)
            ·
              refine ⟨12879275034198730474041239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8586183356132486982694159 12879275034198730474041239)
              ·
                refine ⟨19318912551298095711061859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12879275034198730474041239 19318912551298095711061859)
                ·
                  refine ⟨28978368826947143566592789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19318912551298095711061859 28978368826947143566592789)
                  ·
                    refine ⟨1358361038763147354684037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28978368826947143566592789 1358361038763147354684037)
                    ·
                      rfl

theorem cell22_3968098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3968098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968098 prefixEnd_3968098 := by exact prefixLift 3968098
  have htrace : WordTrace (prefixWord ++ tailWord_3968098) baseStart_3968098 baseEnd_3968098 := by
    simpa [prefixWord, tailWord_3968098, baseEnd_3968098] using wordTrace_append hprefix tailTrace_3968098
  have hstable : (prefixWord ++ tailWord_3968098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968098).length < 2 ^ (prefixWord ++ tailWord_3968098).sum := by decide
  have hdescent : baseEnd_3968098 < baseStart_3968098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968104 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3968104 : Nat := 118140960795 + 3968104 * 2 ^ 59
def prefixEnd_3968104 : Nat := 4983230072969 + 3 ^ 40 * 3968104 * 2
def baseEnd_3968104 : Nat := 1358363092685765339034019

theorem tailTrace_3968104 : CollatzResearch.WordTrace tailWord_3968104 prefixEnd_3968104 1358363092685765339034019 := by
  unfold tailWord_3968104
  simp only [CollatzResearch.WordTrace]
  refine ⟨72364321408122190526999683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96485761877496254035999577 72364321408122190526999683)
  ·
    refine ⟨108546482112183285790499525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72364321408122190526999683 108546482112183285790499525)
    ·
      refine ⟨20352465396034366085718661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108546482112183285790499525 20352465396034366085718661)
      ·
        refine ⟨3816087261756443641072249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20352465396034366085718661 3816087261756443641072249)
        ·
          refine ⟨2862065446317332730804187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3816087261756443641072249 2862065446317332730804187)
          ·
            refine ⟨4293098169475999096206281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862065446317332730804187 4293098169475999096206281)
            ·
              refine ⟨3219823627106999322154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293098169475999096206281 3219823627106999322154711)
              ·
                refine ⟨4829735440660498983232067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219823627106999322154711 4829735440660498983232067)
                ·
                  refine ⟨7244603160990748474848101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4829735440660498983232067 7244603160990748474848101)
                  ·
                    refine ⟨1358363092685765339034019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7244603160990748474848101 1358363092685765339034019)
                    ·
                      rfl

theorem cell22_3968104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3968104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968104 prefixEnd_3968104 := by exact prefixLift 3968104
  have htrace : WordTrace (prefixWord ++ tailWord_3968104) baseStart_3968104 baseEnd_3968104 := by
    simpa [prefixWord, tailWord_3968104, baseEnd_3968104] using wordTrace_append hprefix tailTrace_3968104
  have hstable : (prefixWord ++ tailWord_3968104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968104).length < 2 ^ (prefixWord ++ tailWord_3968104).sum := by decide
  have hdescent : baseEnd_3968104 < baseStart_3968104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968111 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 5, 3]
def baseStart_3968111 : Nat := 118140960795 + 3968111 * 2 ^ 59
def prefixEnd_3968111 : Nat := 4983230072969 + 3 ^ 40 * 3968111 * 2
def baseEnd_3968111 : Nat := 1358365488928819654108997

theorem tailTrace_3968111 : CollatzResearch.WordTrace tailWord_3968111 prefixEnd_3968111 1358365488928819654108997 := by
  unfold tailWord_3968111
  simp only [CollatzResearch.WordTrace]
  refine ⟨144728898127219021249504187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96485932084812680833002791 144728898127219021249504187)
  ·
    refine ⟨217093347190828531874256281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144728898127219021249504187 217093347190828531874256281)
    ·
      refine ⟨162820010393121398905692211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217093347190828531874256281 162820010393121398905692211)
      ·
        refine ⟨244230015589682098358538317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162820010393121398905692211 244230015589682098358538317)
        ·
          refine ⟨91586255846130786884451869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244230015589682098358538317 91586255846130786884451869)
          ·
            refine ⟨34344845942299045081669451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91586255846130786884451869 34344845942299045081669451)
            ·
              refine ⟨51517268913448567622504177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34344845942299045081669451 51517268913448567622504177)
              ·
                refine ⟨38637951685086425716878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51517268913448567622504177 38637951685086425716878133)
                ·
                  refine ⟨3622307970476852410957325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38637951685086425716878133 3622307970476852410957325)
                  ·
                    refine ⟨1358365488928819654108997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622307970476852410957325 1358365488928819654108997)
                    ·
                      rfl

theorem cell22_3968111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_3968111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968111 prefixEnd_3968111 := by exact prefixLift 3968111
  have htrace : WordTrace (prefixWord ++ tailWord_3968111) baseStart_3968111 baseEnd_3968111 := by
    simpa [prefixWord, tailWord_3968111, baseEnd_3968111] using wordTrace_append hprefix tailTrace_3968111
  have hstable : (prefixWord ++ tailWord_3968111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968111).length < 2 ^ (prefixWord ++ tailWord_3968111).sum := by decide
  have hdescent : baseEnd_3968111 < baseStart_3968111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968158 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3968158 : Nat := 118140960795 + 3968158 * 2 ^ 59
def prefixEnd_3968158 : Nat := 4983230072969 + 3 ^ 40 * 3968158 * 2
def baseEnd_3968158 : Nat := 452793859329775732727951

theorem tailTrace_3968158 : CollatzResearch.WordTrace tailWord_3968158 prefixEnd_3968158 452793859329775732727951 := by
  unfold tailWord_3968158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18091326544756093534558141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96487074905365832184310085 18091326544756093534558141)
  ·
    refine ⟨6784247454283535075459303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18091326544756093534558141 6784247454283535075459303)
    ·
      refine ⟨10176371181425302613188955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6784247454283535075459303 10176371181425302613188955)
      ·
        refine ⟨15264556772137953919783433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10176371181425302613188955 15264556772137953919783433)
        ·
          refine ⟨11448417579103465439837575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15264556772137953919783433 11448417579103465439837575)
          ·
            refine ⟨17172626368655198159756363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448417579103465439837575 17172626368655198159756363)
            ·
              refine ⟨25758939552982797239634545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17172626368655198159756363 25758939552982797239634545)
              ·
                refine ⟨19319204664737097929725909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25758939552982797239634545 19319204664737097929725909)
                ·
                  refine ⟨452793859329775732727951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19319204664737097929725909 452793859329775732727951)
                  ·
                    rfl

theorem cell22_3968158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3968158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968158 prefixEnd_3968158 := by exact prefixLift 3968158
  have htrace : WordTrace (prefixWord ++ tailWord_3968158) baseStart_3968158 baseEnd_3968158 := by
    simpa [prefixWord, tailWord_3968158, baseEnd_3968158] using wordTrace_append hprefix tailTrace_3968158
  have hstable : (prefixWord ++ tailWord_3968158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968158).length < 2 ^ (prefixWord ++ tailWord_3968158).sum := by decide
  have hdescent : baseEnd_3968158 < baseStart_3968158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968192 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_3968192 : Nat := 118140960795 + 3968192 * 2 ^ 59
def prefixEnd_3968192 : Nat := 4983230072969 + 3 ^ 40 * 3968192 * 2
def baseEnd_3968192 : Nat := 452797738961387480944583

theorem tailTrace_3968192 : CollatzResearch.WordTrace tailWord_3968192 prefixEnd_3968192 452797738961387480944583 := by
  unfold tailWord_3968192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72365926219962786041601415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96487901626617048055468553 72365926219962786041601415)
  ·
    refine ⟨108548889329944179062402123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72365926219962786041601415 108548889329944179062402123)
    ·
      refine ⟨162823333994916268593603185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108548889329944179062402123 162823333994916268593603185)
      ·
        refine ⟨122117500496187201445202389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162823333994916268593603185 122117500496187201445202389)
        ·
          refine ⟨2862128917879387533871931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 122117500496187201445202389 2862128917879387533871931)
          ·
            refine ⟨4293193376819081300807897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862128917879387533871931 4293193376819081300807897)
            ·
              refine ⟨3219895032614310975605923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293193376819081300807897 3219895032614310975605923)
              ·
                refine ⟨4829842548921466463408885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219895032614310975605923 4829842548921466463408885)
                ·
                  refine ⟨452797738961387480944583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4829842548921466463408885 452797738961387480944583)
                  ·
                    rfl

theorem cell22_3968192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_3968192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968192 prefixEnd_3968192 := by exact prefixLift 3968192
  have htrace : WordTrace (prefixWord ++ tailWord_3968192) baseStart_3968192 baseEnd_3968192 := by
    simpa [prefixWord, tailWord_3968192, baseEnd_3968192] using wordTrace_append hprefix tailTrace_3968192
  have hstable : (prefixWord ++ tailWord_3968192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968192).length < 2 ^ (prefixWord ++ tailWord_3968192).sum := by decide
  have hdescent : baseEnd_3968192 < baseStart_3968192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968231 : List Nat := [1, 1, 5, 3, 12]
def baseStart_3968231 : Nat := 118140960795 + 3968231 * 2 ^ 59
def prefixEnd_3968231 : Nat := 4983230072969 + 3 ^ 40 * 3968231 * 2
def baseEnd_3968231 : Nat := 5590150483050120745303

theorem tailTrace_3968231 : CollatzResearch.WordTrace tailWord_3968231 prefixEnd_3968231 5590150483050120745303 := by
  unfold tailWord_3968231
  simp only [CollatzResearch.WordTrace]
  refine ⟨144733274886784281743872547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96488849924522854495915031 144733274886784281743872547)
  ·
    refine ⟨217099912330176422615808821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144733274886784281743872547 217099912330176422615808821)
    ·
      refine ⟨20353116780954039620232077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217099912330176422615808821 20353116780954039620232077)
      ·
        refine ⟨7632418792857764857587029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20353116780954039620232077 7632418792857764857587029)
        ·
          refine ⟨5590150483050120745303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7632418792857764857587029 5590150483050120745303)
          ·
            rfl

theorem cell22_3968231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 12].length) (baseStart_3968231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968231 prefixEnd_3968231 := by exact prefixLift 3968231
  have htrace : WordTrace (prefixWord ++ tailWord_3968231) baseStart_3968231 baseEnd_3968231 := by
    simpa [prefixWord, tailWord_3968231, baseEnd_3968231] using wordTrace_append hprefix tailTrace_3968231
  have hstable : (prefixWord ++ tailWord_3968231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968231).length < 2 ^ (prefixWord ++ tailWord_3968231).sum := by decide
  have hdescent : baseEnd_3968231 < baseStart_3968231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968235 : List Nat := [1, 1, 1, 1, 2, 7, 2, 2, 2, 3]
def baseStart_3968235 : Nat := 118140960795 + 3968235 * 2 ^ 59
def prefixEnd_3968235 : Nat := 4983230072969 + 3 ^ 40 * 3968235 * 2
def baseEnd_3968235 : Nat := 1358407936662924664008617

theorem tailTrace_3968235 : CollatzResearch.WordTrace tailWord_3968235 prefixEnd_3968235 1358407936662924664008617 := by
  unfold tailWord_3968235
  simp only [CollatzResearch.WordTrace]
  refine ⟨144733420778769790427018159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96488947185846526951345439 144733420778769790427018159)
  ·
    refine ⟨217100131168154685640527239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144733420778769790427018159 217100131168154685640527239)
    ·
      refine ⟨325650196752232028460790859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217100131168154685640527239 325650196752232028460790859)
      ·
        refine ⟨488475295128348042691186289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325650196752232028460790859 488475295128348042691186289)
        ·
          refine ⟨366356471346261032018389717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488475295128348042691186289 366356471346261032018389717)
          ·
            refine ⟨8586479797177992937931009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 366356471346261032018389717 8586479797177992937931009)
            ·
              refine ⟨6439859847883494703448257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586479797177992937931009 6439859847883494703448257)
              ·
                refine ⟨4829894885912621027586193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439859847883494703448257 4829894885912621027586193)
                ·
                  refine ⟨3622421164434465770689645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829894885912621027586193 3622421164434465770689645)
                  ·
                    refine ⟨1358407936662924664008617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622421164434465770689645 1358407936662924664008617)
                    ·
                      rfl

theorem cell22_3968235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3].length) (baseStart_3968235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968235 prefixEnd_3968235 := by exact prefixLift 3968235
  have htrace : WordTrace (prefixWord ++ tailWord_3968235) baseStart_3968235 baseEnd_3968235 := by
    simpa [prefixWord, tailWord_3968235, baseEnd_3968235] using wordTrace_append hprefix tailTrace_3968235
  have hstable : (prefixWord ++ tailWord_3968235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968235).length < 2 ^ (prefixWord ++ tailWord_3968235).sum := by decide
  have hdescent : baseEnd_3968235 < baseStart_3968235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968237 : List Nat := [1, 5, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3968237 : Nat := 118140960795 + 3968237 * 2 ^ 59
def prefixEnd_3968237 : Nat := 4983230072969 + 3 ^ 40 * 3968237 * 2
def baseEnd_3968237 : Nat := 452802873767932441819537

theorem tailTrace_3968237 : CollatzResearch.WordTrace tailWord_3968237 prefixEnd_3968237 452802873767932441819537 := by
  unfold tailWord_3968237
  simp only [CollatzResearch.WordTrace]
  refine ⟨144733493724762544768590965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96488995816508363179060643 144733493724762544768590965)
  ·
    refine ⟨13568765036696488572055403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144733493724762544768590965 13568765036696488572055403)
    ·
      refine ⟨20353147555044732858083105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13568765036696488572055403 20353147555044732858083105)
      ·
        refine ⟨15264860666283549643562329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20353147555044732858083105 15264860666283549643562329)
        ·
          refine ⟨11448645499712662232671747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15264860666283549643562329 11448645499712662232671747)
          ·
            refine ⟨17172968249568993349007621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11448645499712662232671747 17172968249568993349007621)
            ·
              refine ⟨3219931546794186252938929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17172968249568993349007621 3219931546794186252938929)
              ·
                refine ⟨2414948660095639689704197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219931546794186252938929 2414948660095639689704197)
                ·
                  refine ⟨452802873767932441819537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2414948660095639689704197 452802873767932441819537)
                  ·
                    rfl

theorem cell22_3968237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3968237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968237 prefixEnd_3968237 := by exact prefixLift 3968237
  have htrace : WordTrace (prefixWord ++ tailWord_3968237) baseStart_3968237 baseEnd_3968237 := by
    simpa [prefixWord, tailWord_3968237, baseEnd_3968237] using wordTrace_append hprefix tailTrace_3968237
  have hstable : (prefixWord ++ tailWord_3968237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968237).length < 2 ^ (prefixWord ++ tailWord_3968237).sum := by decide
  have hdescent : baseEnd_3968237 < baseStart_3968237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968261 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_3968261 : Nat := 118140960795 + 3968261 * 2 ^ 59
def prefixEnd_3968261 : Nat := 4983230072969 + 3 ^ 40 * 3968261 * 2
def baseEnd_3968261 : Nat := 1358416836994269262858537

theorem tailTrace_3968261 : CollatzResearch.WordTrace tailWord_3968261 prefixEnd_3968261 1358416836994269262858537 := by
  unfold tailWord_3968261
  simp only [CollatzResearch.WordTrace]
  refine ⟨144734369076675596867464637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96489579384450397911643091 144734369076675596867464637)
  ·
    refine ⟨54275388403753348825299239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144734369076675596867464637 54275388403753348825299239)
    ·
      refine ⟨81413082605630023237948859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54275388403753348825299239 81413082605630023237948859)
      ·
        refine ⟨122119623908445034856923289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81413082605630023237948859 122119623908445034856923289)
        ·
          refine ⟨91589717931333776142692467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122119623908445034856923289 91589717931333776142692467)
          ·
            refine ⟨137384576897000664214038701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91589717931333776142692467 137384576897000664214038701)
            ·
              refine ⟨51519216336375249080264513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137384576897000664214038701 51519216336375249080264513)
              ·
                refine ⟨38639412252281436810198385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51519216336375249080264513 38639412252281436810198385)
                ·
                  refine ⟨28979559189211077607648789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38639412252281436810198385 28979559189211077607648789)
                  ·
                    refine ⟨1358416836994269262858537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28979559189211077607648789 1358416836994269262858537)
                    ·
                      rfl

theorem cell22_3968261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_3968261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968261 prefixEnd_3968261 := by exact prefixLift 3968261
  have htrace : WordTrace (prefixWord ++ tailWord_3968261) baseStart_3968261 baseEnd_3968261 := by
    simpa [prefixWord, tailWord_3968261, baseEnd_3968261] using wordTrace_append hprefix tailTrace_3968261
  have hstable : (prefixWord ++ tailWord_3968261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968261).length < 2 ^ (prefixWord ++ tailWord_3968261).sum := by decide
  have hdescent : baseEnd_3968261 < baseStart_3968261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968286 : List Nat := [4, 3, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3968286 : Nat := 118140960795 + 3968286 * 2 ^ 59
def prefixEnd_3968286 : Nat := 4983230072969 + 3 ^ 40 * 3968286 * 2
def baseEnd_3968286 : Nat := 1358425395005177530983461

theorem tailTrace_3968286 : CollatzResearch.WordTrace tailWord_3968286 prefixEnd_3968286 1358425395005177530983461 := by
  unfold tailWord_3968286
  simp only [CollatzResearch.WordTrace]
  refine ⟨18091910112698128267140589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96490187267723350758083141 18091910112698128267140589)
  ·
    refine ⟨6784466292261798100177721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18091910112698128267140589 6784466292261798100177721)
    ·
      refine ⟨5088349719196348575133291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6784466292261798100177721 5088349719196348575133291)
      ·
        refine ⟨7632524578794522862699937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088349719196348575133291 7632524578794522862699937)
        ·
          refine ⟨5724393434095892147024953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7632524578794522862699937 5724393434095892147024953)
          ·
            refine ⟨4293295075571919110268715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5724393434095892147024953 4293295075571919110268715)
            ·
              refine ⟨6439942613357878665403073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293295075571919110268715 6439942613357878665403073)
              ·
                refine ⟨4829956960018408999052305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439942613357878665403073 4829956960018408999052305)
                ·
                  refine ⟨3622467720013806749289229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829956960018408999052305 3622467720013806749289229)
                  ·
                    refine ⟨1358425395005177530983461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622467720013806749289229 1358425395005177530983461)
                    ·
                      rfl

theorem cell22_3968286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3968286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968286 prefixEnd_3968286 := by exact prefixLift 3968286
  have htrace : WordTrace (prefixWord ++ tailWord_3968286) baseStart_3968286 baseEnd_3968286 := by
    simpa [prefixWord, tailWord_3968286, baseEnd_3968286] using wordTrace_append hprefix tailTrace_3968286
  have hstable : (prefixWord ++ tailWord_3968286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968286).length < 2 ^ (prefixWord ++ tailWord_3968286).sum := by decide
  have hdescent : baseEnd_3968286 < baseStart_3968286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968293 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 7]
def baseStart_3968293 : Nat := 118140960795 + 3968293 * 2 ^ 59
def prefixEnd_3968293 : Nat := 4983230072969 + 3 ^ 40 * 3968293 * 2
def baseEnd_3968293 : Nat := 452809263749410615352813

theorem tailTrace_3968293 : CollatzResearch.WordTrace tailWord_3968293 prefixEnd_3968293 452809263749410615352813 := by
  unfold tailWord_3968293
  simp only [CollatzResearch.WordTrace]
  refine ⟨144735536212559666332629533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96490357475039777555086355 144735536212559666332629533)
  ·
    refine ⟨54275826079709874874736075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144735536212559666332629533 54275826079709874874736075)
    ·
      refine ⟨81413739119564812312104113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54275826079709874874736075 81413739119564812312104113)
      ·
        refine ⟨61060304339673609234078085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81413739119564812312104113 61060304339673609234078085)
        ·
          refine ⟨11448807063688801731389641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61060304339673609234078085 11448807063688801731389641)
          ·
            refine ⟨8586605297766601298542231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11448807063688801731389641 8586605297766601298542231)
            ·
              refine ⟨12879907946649901947813347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8586605297766601298542231 12879907946649901947813347)
              ·
                refine ⟨19319861919974852921720021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12879907946649901947813347 19319861919974852921720021)
                ·
                  refine ⟨452809263749410615352813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19319861919974852921720021 452809263749410615352813)
                  ·
                    rfl

theorem cell22_3968293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_3968293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968293 prefixEnd_3968293 := by exact prefixLift 3968293
  have htrace : WordTrace (prefixWord ++ tailWord_3968293) baseStart_3968293 baseEnd_3968293 := by
    simpa [prefixWord, tailWord_3968293, baseEnd_3968293] using wordTrace_append hprefix tailTrace_3968293
  have hstable : (prefixWord ++ tailWord_3968293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968293).length < 2 ^ (prefixWord ++ tailWord_3968293).sum := by decide
  have hdescent : baseEnd_3968293 < baseStart_3968293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968340 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_3968340 : Nat := 118140960795 + 3968340 * 2 ^ 59
def prefixEnd_3968340 : Nat := 4983230072969 + 3 ^ 40 * 3968340 * 2
def baseEnd_3968340 : Nat := 1358443880308739390133295

theorem tailTrace_3968340 : CollatzResearch.WordTrace tailWord_3968340 prefixEnd_3968340 1358443880308739390133295 := by
  unfold tailWord_3968340
  simp only [CollatzResearch.WordTrace]
  refine ⟨72368625221694696679795237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96491500295592928906393649 72368625221694696679795237)
  ·
    refine ⟨13569117229067755627461607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72368625221694696679795237 13569117229067755627461607)
    ·
      refine ⟨20353675843601633441192411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569117229067755627461607 20353675843601633441192411)
      ·
        refine ⟨30530513765402450161788617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20353675843601633441192411 30530513765402450161788617)
        ·
          refine ⟨22897885324051837621341463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30530513765402450161788617 22897885324051837621341463)
          ·
            refine ⟨34346827986077756432012195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22897885324051837621341463 34346827986077756432012195)
            ·
              refine ⟨51520241979116634648018293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34346827986077756432012195 51520241979116634648018293)
              ·
                refine ⟨4830022685542184498251715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51520241979116634648018293 4830022685542184498251715)
                ·
                  refine ⟨7245034028313276747377573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4830022685542184498251715 7245034028313276747377573)
                  ·
                    refine ⟨1358443880308739390133295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7245034028313276747377573 1358443880308739390133295)
                    ·
                      rfl

theorem cell22_3968340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_3968340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968340 prefixEnd_3968340 := by exact prefixLift 3968340
  have htrace : WordTrace (prefixWord ++ tailWord_3968340) baseStart_3968340 baseEnd_3968340 := by
    simpa [prefixWord, tailWord_3968340, baseEnd_3968340] using wordTrace_append hprefix tailTrace_3968340
  have hstable : (prefixWord ++ tailWord_3968340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968340).length < 2 ^ (prefixWord ++ tailWord_3968340).sum := by decide
  have hdescent : baseEnd_3968340 < baseStart_3968340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968355 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 6]
def baseStart_3968355 : Nat := 118140960795 + 3968355 * 2 ^ 59
def prefixEnd_3968355 : Nat := 4983230072969 + 3 ^ 40 * 3968355 * 2
def baseEnd_3968355 : Nat := 452816338371761450336083

theorem tailTrace_3968355 : CollatzResearch.WordTrace tailWord_3968355 prefixEnd_3968355 452816338371761450336083 := by
  unfold tailWord_3968355
  simp only [CollatzResearch.WordTrace]
  refine ⟨144737797538335050921386519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96491865025556700614257679 144737797538335050921386519)
  ·
    refine ⟨217106696307502576382079779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144737797538335050921386519 217106696307502576382079779)
    ·
      refine ⟨325660044461253864573119669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217106696307502576382079779 325660044461253864573119669)
      ·
        refine ⟨30530629168242549803729969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325660044461253864573119669 30530629168242549803729969)
        ·
          refine ⟨22897971876181912352797477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30530629168242549803729969 22897971876181912352797477)
          ·
            refine ⟨4293369726784108566149527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22897971876181912352797477 4293369726784108566149527)
            ·
              refine ⟨6440054590176162849224291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293369726784108566149527 6440054590176162849224291)
              ·
                refine ⟨9660081885264244273836437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440054590176162849224291 9660081885264244273836437)
                ·
                  refine ⟨452816338371761450336083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9660081885264244273836437 452816338371761450336083)
                  ·
                    rfl

theorem cell22_3968355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 6].length) (baseStart_3968355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968355 prefixEnd_3968355 := by exact prefixLift 3968355
  have htrace : WordTrace (prefixWord ++ tailWord_3968355) baseStart_3968355 baseEnd_3968355 := by
    simpa [prefixWord, tailWord_3968355, baseEnd_3968355] using wordTrace_append hprefix tailTrace_3968355
  have hstable : (prefixWord ++ tailWord_3968355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968355).length < 2 ^ (prefixWord ++ tailWord_3968355).sum := by decide
  have hdescent : baseEnd_3968355 < baseStart_3968355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968368 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_3968368 : Nat := 118140960795 + 3968368 * 2 ^ 59
def prefixEnd_3968368 : Nat := 4983230072969 + 3 ^ 40 * 3968368 * 2
def baseEnd_3968368 : Nat := 1358453465280956650433209

theorem tailTrace_3968368 : CollatzResearch.WordTrace tailWord_3968368 prefixEnd_3968368 1358453465280956650433209 := by
  unfold tailWord_3968368
  simp only [CollatzResearch.WordTrace]
  refine ⟨72369135843643977070804879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96492181124858636094406505 72369135843643977070804879)
  ·
    refine ⟨108553703765465965606207319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72369135843643977070804879 108553703765465965606207319)
    ·
      refine ⟨162830555648198948409310979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108553703765465965606207319 162830555648198948409310979)
      ·
        refine ⟨244245833472298422613966469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162830555648198948409310979 244245833472298422613966469)
        ·
          refine ⟨45796093776055954240118713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244245833472298422613966469 45796093776055954240118713)
          ·
            refine ⟨34347070332041965680089035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45796093776055954240118713 34347070332041965680089035)
            ·
              refine ⟨51520605498062948520133553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34347070332041965680089035 51520605498062948520133553)
              ·
                refine ⟨38640454123547211390100165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51520605498062948520133553 38640454123547211390100165)
                ·
                  refine ⟨7245085148165102135643781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38640454123547211390100165 7245085148165102135643781)
                  ·
                    refine ⟨1358453465280956650433209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7245085148165102135643781 1358453465280956650433209)
                    ·
                      rfl

theorem cell22_3968368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_3968368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968368 prefixEnd_3968368 := by exact prefixLift 3968368
  have htrace : WordTrace (prefixWord ++ tailWord_3968368) baseStart_3968368 baseEnd_3968368 := by
    simpa [prefixWord, tailWord_3968368, baseEnd_3968368] using wordTrace_append hprefix tailTrace_3968368
  have hstable : (prefixWord ++ tailWord_3968368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968368).length < 2 ^ (prefixWord ++ tailWord_3968368).sum := by decide
  have hdescent : baseEnd_3968368 < baseStart_3968368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968404 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_3968404 : Nat := 118140960795 + 3968404 * 2 ^ 59
def prefixEnd_3968404 : Nat := 4983230072969 + 3 ^ 40 * 3968404 * 2
def baseEnd_3968404 : Nat := 1358465788816664556533099

theorem tailTrace_3968404 : CollatzResearch.WordTrace tailWord_3968404 prefixEnd_3968404 1358465788816664556533099 := by
  unfold tailWord_3968404
  simp only [CollatzResearch.WordTrace]
  refine ⟨72369792357578766144960133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96493056476771688193280177 72369792357578766144960133)
  ·
    refine ⟨13569336067046018652180025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72369792357578766144960133 13569336067046018652180025)
    ·
      refine ⟨10177002050284513989135019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13569336067046018652180025 10177002050284513989135019)
      ·
        refine ⟨15265503075426770983702529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177002050284513989135019 15265503075426770983702529)
        ·
          refine ⟨11449127306570078237776897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15265503075426770983702529 11449127306570078237776897)
          ·
            refine ⟨8586845479927558678332673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11449127306570078237776897 8586845479927558678332673)
            ·
              refine ⟨6440134109945669008749505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586845479927558678332673 6440134109945669008749505)
              ·
                refine ⟨4830100582459251756562129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440134109945669008749505 4830100582459251756562129)
                ·
                  refine ⟨3622575436844438817421597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830100582459251756562129 3622575436844438817421597)
                  ·
                    refine ⟨1358465788816664556533099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622575436844438817421597 1358465788816664556533099)
                    ·
                      rfl

theorem cell22_3968404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_3968404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968404 prefixEnd_3968404 := by exact prefixLift 3968404
  have htrace : WordTrace (prefixWord ++ tailWord_3968404) baseStart_3968404 baseEnd_3968404 := by
    simpa [prefixWord, tailWord_3968404, baseEnd_3968404] using wordTrace_append hprefix tailTrace_3968404
  have hstable : (prefixWord ++ tailWord_3968404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968404).length < 2 ^ (prefixWord ++ tailWord_3968404).sum := by decide
  have hdescent : baseEnd_3968404 < baseStart_3968404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968460 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_3968460 : Nat := 118140960795 + 3968460 * 2 ^ 59
def prefixEnd_3968460 : Nat := 4983230072969 + 3 ^ 40 * 3968460 * 2
def baseEnd_3968460 : Nat := 1358484958761099077132927

theorem tailTrace_3968460 : CollatzResearch.WordTrace tailWord_3968460 prefixEnd_3968460 1358484958761099077132927 := by
  unfold tailWord_3968460
  simp only [CollatzResearch.WordTrace]
  refine ⟨72370813601477326926979417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96494418135303102569305889 72370813601477326926979417)
  ·
    refine ⟨54278110201107995195234563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72370813601477326926979417 54278110201107995195234563)
    ·
      refine ⟨81417165301661992792851845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54278110201107995195234563 81417165301661992792851845)
      ·
        refine ⟨15265718494061623648659721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81417165301661992792851845 15265718494061623648659721)
        ·
          refine ⟨11449288870546217736494791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15265718494061623648659721 11449288870546217736494791)
          ·
            refine ⟨17173933305819326604742187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449288870546217736494791 17173933305819326604742187)
            ·
              refine ⟨25760899958728989907113281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17173933305819326604742187 25760899958728989907113281)
              ·
                refine ⟨19320674969046742430334961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25760899958728989907113281 19320674969046742430334961)
                ·
                  refine ⟨14490506226785056822751221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19320674969046742430334961 14490506226785056822751221)
                  ·
                    refine ⟨1358484958761099077132927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14490506226785056822751221 1358484958761099077132927)
                    ·
                      rfl

theorem cell22_3968460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_3968460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968460 prefixEnd_3968460 := by exact prefixLift 3968460
  have htrace : WordTrace (prefixWord ++ tailWord_3968460) baseStart_3968460 baseEnd_3968460 := by
    simpa [prefixWord, tailWord_3968460, baseEnd_3968460] using wordTrace_append hprefix tailTrace_3968460
  have hstable : (prefixWord ++ tailWord_3968460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968460).length < 2 ^ (prefixWord ++ tailWord_3968460).sum := by decide
  have hdescent : baseEnd_3968460 < baseStart_3968460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968520 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3968520 : Nat := 118140960795 + 3968520 * 2 ^ 59
def prefixEnd_3968520 : Nat := 4983230072969 + 3 ^ 40 * 3968520 * 2
def baseEnd_3968520 : Nat := 1358505497987278920632743

theorem tailTrace_3968520 : CollatzResearch.WordTrace tailWord_3968520 prefixEnd_3968520 1358505497987278920632743 := by
  unfold tailWord_3968520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72371907791368642050571507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96495877055158189400762009 72371907791368642050571507)
  ·
    refine ⟨108557861687052963075857261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72371907791368642050571507 108557861687052963075857261)
    ·
      refine ⟨40709198132644861153446473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108557861687052963075857261 40709198132644861153446473)
      ·
        refine ⟨30531898599483645865084855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40709198132644861153446473 30531898599483645865084855)
        ·
          refine ⟨45797847899225468797627283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30531898599483645865084855 45797847899225468797627283)
          ·
            refine ⟨68696771848838203196440925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45797847899225468797627283 68696771848838203196440925)
            ·
              refine ⟨25761289443314326198665347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68696771848838203196440925 25761289443314326198665347)
              ·
                refine ⟨38641934164971489297998021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25761289443314326198665347 38641934164971489297998021)
                ·
                  refine ⟨7245362655932154243374629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38641934164971489297998021 7245362655932154243374629)
                  ·
                    refine ⟨1358505497987278920632743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7245362655932154243374629 1358505497987278920632743)
                    ·
                      rfl

theorem cell22_3968520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3968520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968520 prefixEnd_3968520 := by exact prefixLift 3968520
  have htrace : WordTrace (prefixWord ++ tailWord_3968520) baseStart_3968520 baseEnd_3968520 := by
    simpa [prefixWord, tailWord_3968520, baseEnd_3968520] using wordTrace_append hprefix tailTrace_3968520
  have hstable : (prefixWord ++ tailWord_3968520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968520).length < 2 ^ (prefixWord ++ tailWord_3968520).sum := by decide
  have hdescent : baseEnd_3968520 < baseStart_3968520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968522 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_3968522 : Nat := 118140960795 + 3968522 * 2 ^ 59
def prefixEnd_3968522 : Nat := 4983230072969 + 3 ^ 40 * 3968522 * 2
def baseEnd_3968522 : Nat := 1358506182628151582082737

theorem tailTrace_3968522 : CollatzResearch.WordTrace tailWord_3968522 prefixEnd_3968522 1358506182628151582082737 := by
  unfold tailWord_3968522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36185972132182509610678955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96495925685820025628477213 36185972132182509610678955)
  ·
    refine ⟨54278958198273764416018433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36185972132182509610678955 54278958198273764416018433)
    ·
      refine ⟨40709218648705323312013825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54278958198273764416018433 40709218648705323312013825)
      ·
        refine ⟨30531913986528992484010369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40709218648705323312013825 30531913986528992484010369)
        ·
          refine ⟨22898935489896744363007777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30531913986528992484010369 22898935489896744363007777)
          ·
            refine ⟨17174201617422558272255833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22898935489896744363007777 17174201617422558272255833)
            ·
              refine ⟨12880651213066918704191875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17174201617422558272255833 12880651213066918704191875)
              ·
                refine ⟨19320976819600378056287813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12880651213066918704191875 19320976819600378056287813)
                ·
                  refine ⟨3622683153675070885553965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19320976819600378056287813 3622683153675070885553965)
                  ·
                    refine ⟨1358506182628151582082737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622683153675070885553965 1358506182628151582082737)
                    ·
                      rfl

theorem cell22_3968522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_3968522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968522 prefixEnd_3968522 := by exact prefixLift 3968522
  have htrace : WordTrace (prefixWord ++ tailWord_3968522) baseStart_3968522 baseEnd_3968522 := by
    simpa [prefixWord, tailWord_3968522, baseEnd_3968522] using wordTrace_append hprefix tailTrace_3968522
  have hstable : (prefixWord ++ tailWord_3968522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968522).length < 2 ^ (prefixWord ++ tailWord_3968522).sum := by decide
  have hdescent : baseEnd_3968522 < baseStart_3968522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968524 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_3968524 : Nat := 118140960795 + 3968524 * 2 ^ 59
def prefixEnd_3968524 : Nat := 4983230072969 + 3 ^ 40 * 3968524 * 2
def baseEnd_3968524 : Nat := 452835622423008081177577

theorem tailTrace_3968524 : CollatzResearch.WordTrace tailWord_3968524 prefixEnd_3968524 452835622423008081177577 := by
  unfold tailWord_3968524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72371980737361396392144313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96495974316481861856192417 72371980737361396392144313)
  ·
    refine ⟨54278985553021047294108235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72371980737361396392144313 54278985553021047294108235)
    ·
      refine ⟨81418478329531570941162353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54278985553021047294108235 81418478329531570941162353)
      ·
        refine ⟨61063858747148678205871765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81418478329531570941162353 61063858747148678205871765)
        ·
          refine ⟨2862368378772594290900239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61063858747148678205871765 2862368378772594290900239)
          ·
            refine ⟨4293552568158891436350359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862368378772594290900239 4293552568158891436350359)
            ·
              refine ⟨6440328852238337154525539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293552568158891436350359 6440328852238337154525539)
              ·
                refine ⟨9660493278357505731788309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440328852238337154525539 9660493278357505731788309)
                ·
                  refine ⟨452835622423008081177577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9660493278357505731788309 452835622423008081177577)
                  ·
                    rfl

theorem cell22_3968524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_3968524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968524 prefixEnd_3968524 := by exact prefixLift 3968524
  have htrace : WordTrace (prefixWord ++ tailWord_3968524) baseStart_3968524 baseEnd_3968524 := by
    simpa [prefixWord, tailWord_3968524, baseEnd_3968524] using wordTrace_append hprefix tailTrace_3968524
  have hstable : (prefixWord ++ tailWord_3968524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968524).length < 2 ^ (prefixWord ++ tailWord_3968524).sum := by decide
  have hdescent : baseEnd_3968524 < baseStart_3968524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968672 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_3968672 : Nat := 118140960795 + 3968672 * 2 ^ 59
def prefixEnd_3968672 : Nat := 4983230072969 + 3 ^ 40 * 3968672 * 2
def baseEnd_3968672 : Nat := 1358557530693601190832277

theorem tailTrace_3968672 : CollatzResearch.WordTrace tailWord_3968672 prefixEnd_3968672 1358557530693601190832277 := by
  unfold tailWord_3968672
  simp only [CollatzResearch.WordTrace]
  refine ⟨72374679739093307030338135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96499572985457742707117513 72374679739093307030338135)
  ·
    refine ⟨108562019608639960545507203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72374679739093307030338135 108562019608639960545507203)
    ·
      refine ⟨162843029412959940818260805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108562019608639960545507203 162843029412959940818260805)
      ·
        refine ⟨30533068014929988903423901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162843029412959940818260805 30533068014929988903423901)
        ·
          refine ⟨11449900505598745838783963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30533068014929988903423901 11449900505598745838783963)
          ·
            refine ⟨17174850758398118758175945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11449900505598745838783963 17174850758398118758175945)
            ·
              refine ⟨12881138068798589068631959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17174850758398118758175945 12881138068798589068631959)
              ·
                refine ⟨19321707103197883602947939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12881138068798589068631959 19321707103197883602947939)
                ·
                  refine ⟨28982560654796825404421909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19321707103197883602947939 28982560654796825404421909)
                  ·
                    refine ⟨1358557530693601190832277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28982560654796825404421909 1358557530693601190832277)
                    ·
                      rfl

theorem cell22_3968672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_3968672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968672 prefixEnd_3968672 := by exact prefixLift 3968672
  have htrace : WordTrace (prefixWord ++ tailWord_3968672) baseStart_3968672 baseEnd_3968672 := by
    simpa [prefixWord, tailWord_3968672, baseEnd_3968672] using wordTrace_append hprefix tailTrace_3968672
  have hstable : (prefixWord ++ tailWord_3968672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968672).length < 2 ^ (prefixWord ++ tailWord_3968672).sum := by decide
  have hdescent : baseEnd_3968672 < baseStart_3968672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968676 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3968676 : Nat := 118140960795 + 3968676 * 2 ^ 59
def prefixEnd_3968676 : Nat := 4983230072969 + 3 ^ 40 * 3968676 * 2
def baseEnd_3968676 : Nat := 452852966658448837910755

theorem tailTrace_3968676 : CollatzResearch.WordTrace tailWord_3968676 prefixEnd_3968676 452852966658448837910755 := by
  unfold tailWord_3968676
  simp only [CollatzResearch.WordTrace]
  refine ⟨72374752685086061371910941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96499670246781415162547921 72374752685086061371910941)
  ·
    refine ⟨27140532256907273014466603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72374752685086061371910941 27140532256907273014466603)
    ·
      refine ⟨40710798385360909521699905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27140532256907273014466603 40710798385360909521699905)
      ·
        refine ⟨30533098789020682141274929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40710798385360909521699905 30533098789020682141274929)
        ·
          refine ⟨22899824091765511605956197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30533098789020682141274929 22899824091765511605956197)
          ·
            refine ⟨4293717017206033426116787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22899824091765511605956197 4293717017206033426116787)
            ·
              refine ⟨6440575525809050139175181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293717017206033426116787 6440575525809050139175181)
              ·
                refine ⟨2415215822178393802190693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6440575525809050139175181 2415215822178393802190693)
                ·
                  refine ⟨452852966658448837910755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415215822178393802190693 452852966658448837910755)
                  ·
                    rfl

theorem cell22_3968676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3968676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968676 prefixEnd_3968676 := by exact prefixLift 3968676
  have htrace : WordTrace (prefixWord ++ tailWord_3968676) baseStart_3968676 baseEnd_3968676 := by
    simpa [prefixWord, tailWord_3968676, baseEnd_3968676] using wordTrace_append hprefix tailTrace_3968676
  have hstable : (prefixWord ++ tailWord_3968676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968676).length < 2 ^ (prefixWord ++ tailWord_3968676).sum := by decide
  have hdescent : baseEnd_3968676 < baseStart_3968676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968693 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 4]
def baseStart_3968693 : Nat := 118140960795 + 3968693 * 2 ^ 59
def prefixEnd_3968693 : Nat := 4983230072969 + 3 ^ 40 * 3968693 * 2
def baseEnd_3968693 : Nat := 452854906474254712019071

theorem tailTrace_3968693 : CollatzResearch.WordTrace tailWord_3968693 prefixEnd_3968693 452854906474254712019071 := by
  unfold tailWord_3968693
  simp only [CollatzResearch.WordTrace]
  refine ⟨144750125411110534647190733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96500083607407023098127155 144750125411110534647190733)
  ·
    refine ⟨54281297029166450492696525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144750125411110534647190733 54281297029166450492696525)
    ·
      refine ⟨20355486385937418934761197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54281297029166450492696525 20355486385937418934761197)
      ·
        refine ⟨7633307394726532100535449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20355486385937418934761197 7633307394726532100535449)
        ·
          refine ⟨5724980546044899075401587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633307394726532100535449 5724980546044899075401587)
          ·
            refine ⟨8587470819067348613102381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724980546044899075401587 8587470819067348613102381)
            ·
              refine ⟨3220301557150255729913393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8587470819067348613102381 3220301557150255729913393)
              ·
                refine ⟨2415226167862691797435045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220301557150255729913393 2415226167862691797435045)
                ·
                  refine ⟨452854906474254712019071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415226167862691797435045 452854906474254712019071)
                  ·
                    rfl

theorem cell22_3968693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_3968693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968693 prefixEnd_3968693 := by exact prefixLift 3968693
  have htrace : WordTrace (prefixWord ++ tailWord_3968693) baseStart_3968693 baseEnd_3968693 := by
    simpa [prefixWord, tailWord_3968693, baseEnd_3968693] using wordTrace_append hprefix tailTrace_3968693
  have hstable : (prefixWord ++ tailWord_3968693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968693).length < 2 ^ (prefixWord ++ tailWord_3968693).sum := by decide
  have hdescent : baseEnd_3968693 < baseStart_3968693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968749 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3968749 : Nat := 118140960795 + 3968749 * 2 ^ 59
def prefixEnd_3968749 : Nat := 4983230072969 + 3 ^ 40 * 3968749 * 2
def baseEnd_3968749 : Nat := 452861296455732885552347

theorem tailTrace_3968749 : CollatzResearch.WordTrace tailWord_3968749 prefixEnd_3968749 452861296455732885552347 := by
  unfold tailWord_3968749
  simp only [CollatzResearch.WordTrace]
  refine ⟨144752167898907656211229301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96501445265938437474152867 144752167898907656211229301)
  ·
    refine ⟨13570515740522592769802747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144752167898907656211229301 13570515740522592769802747)
    ·
      refine ⟨20355773610783889154704121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13570515740522592769802747 20355773610783889154704121)
      ·
        refine ⟨15266830208087916866028091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20355773610783889154704121 15266830208087916866028091)
        ·
          refine ⟨22900245312131875299042137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15266830208087916866028091 22900245312131875299042137)
          ·
            refine ⟨17175183984098906474281603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22900245312131875299042137 17175183984098906474281603)
            ·
              refine ⟨25762775976148359711422405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17175183984098906474281603 25762775976148359711422405)
              ·
                refine ⟨4830520495527817445891701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25762775976148359711422405 4830520495527817445891701)
                ·
                  refine ⟨452861296455732885552347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4830520495527817445891701 452861296455732885552347)
                  ·
                    rfl

theorem cell22_3968749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3968749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968749 prefixEnd_3968749 := by exact prefixLift 3968749
  have htrace : WordTrace (prefixWord ++ tailWord_3968749) baseStart_3968749 baseEnd_3968749 := by
    simpa [prefixWord, tailWord_3968749, baseEnd_3968749] using wordTrace_append hprefix tailTrace_3968749
  have hstable : (prefixWord ++ tailWord_3968749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968749).length < 2 ^ (prefixWord ++ tailWord_3968749).sum := by decide
  have hdescent : baseEnd_3968749 < baseStart_3968749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968753 : List Nat := [1, 2, 2, 2, 2, 3, 4, 2, 1, 3]
def baseStart_3968753 : Nat := 118140960795 + 3968753 * 2 ^ 59
def prefixEnd_3968753 : Nat := 4983230072969 + 3 ^ 40 * 3968753 * 2
def baseEnd_3968753 : Nat := 1358585258648943979557029

theorem tailTrace_3968753 : CollatzResearch.WordTrace tailWord_3968753 prefixEnd_3968753 1358585258648943979557029 := by
  unfold tailWord_3968753
  simp only [CollatzResearch.WordTrace]
  refine ⟨144752313790893164894374913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96501542527262109929583275 144752313790893164894374913)
  ·
    refine ⟨108564235343169873670781185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144752313790893164894374913 108564235343169873670781185)
    ·
      refine ⟨81423176507377405253085889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108564235343169873670781185 81423176507377405253085889)
      ·
        refine ⟨61067382380533053939814417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81423176507377405253085889 61067382380533053939814417)
        ·
          refine ⟨45800536785399790454860813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61067382380533053939814417 45800536785399790454860813)
          ·
            refine ⟨17175201294524921420572805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45800536785399790454860813 17175201294524921420572805)
            ·
              refine ⟨3220350242723422766357401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17175201294524921420572805 3220350242723422766357401)
              ·
                refine ⟨2415262682042567074768051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220350242723422766357401 2415262682042567074768051)
                ·
                  refine ⟨3622894023063850612152077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415262682042567074768051 3622894023063850612152077)
                  ·
                    refine ⟨1358585258648943979557029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3622894023063850612152077 1358585258648943979557029)
                    ·
                      rfl

theorem cell22_3968753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_3968753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968753 prefixEnd_3968753 := by exact prefixLift 3968753
  have htrace : WordTrace (prefixWord ++ tailWord_3968753) baseStart_3968753 baseEnd_3968753 := by
    simpa [prefixWord, tailWord_3968753, baseEnd_3968753] using wordTrace_append hprefix tailTrace_3968753
  have hstable : (prefixWord ++ tailWord_3968753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968753).length < 2 ^ (prefixWord ++ tailWord_3968753).sum := by decide
  have hdescent : baseEnd_3968753 < baseStart_3968753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968774 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3968774 : Nat := 118140960795 + 3968774 * 2 ^ 59
def prefixEnd_3968774 : Nat := 4983230072969 + 3 ^ 40 * 3968774 * 2
def baseEnd_3968774 : Nat := 1358592447378106924781965

theorem tailTrace_3968774 : CollatzResearch.WordTrace tailWord_3968774 prefixEnd_3968774 1358592447378106924781965 := by
  unfold tailWord_3968774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523533741369283921277793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96502053149211390320592917 4523533741369283921277793)
  ·
    refine ⟨3392650306026962940958345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4523533741369283921277793 3392650306026962940958345)
    ·
      refine ⟨2544487729520222205718759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3392650306026962940958345 2544487729520222205718759)
      ·
        refine ⟨3816731594280333308578139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544487729520222205718759 3816731594280333308578139)
        ·
          refine ⟨5725097391420499962867209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3816731594280333308578139 5725097391420499962867209)
          ·
            refine ⟨4293823043565374972150407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5725097391420499962867209 4293823043565374972150407)
            ·
              refine ⟨6440734565348062458225611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293823043565374972150407 6440734565348062458225611)
              ·
                refine ⟨9661101848022093687338417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440734565348062458225611 9661101848022093687338417)
                ·
                  refine ⟨7245826386016570265503813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9661101848022093687338417 7245826386016570265503813)
                  ·
                    refine ⟨1358592447378106924781965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7245826386016570265503813 1358592447378106924781965)
                    ·
                      rfl

theorem cell22_3968774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3968774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968774 prefixEnd_3968774 := by exact prefixLift 3968774
  have htrace : WordTrace (prefixWord ++ tailWord_3968774) baseStart_3968774 baseEnd_3968774 := by
    simpa [prefixWord, tailWord_3968774, baseEnd_3968774] using wordTrace_append hprefix tailTrace_3968774
  have hstable : (prefixWord ++ tailWord_3968774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968774).length < 2 ^ (prefixWord ++ tailWord_3968774).sum := by decide
  have hdescent : baseEnd_3968774 < baseStart_3968774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968826 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 1, 5]
def baseStart_3968826 : Nat := 118140960795 + 3968826 * 2 ^ 59
def prefixEnd_3968826 : Nat := 4983230072969 + 3 ^ 40 * 3968826 * 2
def baseEnd_3968826 : Nat := 1358610248040796122481805

theorem tailTrace_3968826 : CollatzResearch.WordTrace tailWord_3968826 prefixEnd_3968826 1358610248040796122481805 := by
  unfold tailWord_3968826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36188744079907174590445583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96503317546419132241188221 36188744079907174590445583)
  ·
    refine ⟨54283116119860761885668375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36188744079907174590445583 54283116119860761885668375)
    ·
      refine ⟨81424674179791142828502563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54283116119860761885668375 81424674179791142828502563)
      ·
        refine ⟨122137011269686714242753845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81424674179791142828502563 122137011269686714242753845)
        ·
          refine ⟨11450344806533129460258173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122137011269686714242753845 11450344806533129460258173)
          ·
            refine ⟨4293879302449923547596815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11450344806533129460258173 4293879302449923547596815)
            ·
              refine ⟨6440818953674885321395223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293879302449923547596815 6440818953674885321395223)
              ·
                refine ⟨9661228430512327982092835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440818953674885321395223 9661228430512327982092835)
                ·
                  refine ⟨14491842645768491973139253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661228430512327982092835 14491842645768491973139253)
                  ·
                    refine ⟨1358610248040796122481805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14491842645768491973139253 1358610248040796122481805)
                    ·
                      rfl

theorem cell22_3968826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 5].length) (baseStart_3968826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968826 prefixEnd_3968826 := by exact prefixLift 3968826
  have htrace : WordTrace (prefixWord ++ tailWord_3968826) baseStart_3968826 baseEnd_3968826 := by
    simpa [prefixWord, tailWord_3968826, baseEnd_3968826] using wordTrace_append hprefix tailTrace_3968826
  have hstable : (prefixWord ++ tailWord_3968826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968826).length < 2 ^ (prefixWord ++ tailWord_3968826).sum := by decide
  have hdescent : baseEnd_3968826 < baseStart_3968826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968837 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_3968837 : Nat := 118140960795 + 3968837 * 2 ^ 59
def prefixEnd_3968837 : Nat := 4983230072969 + 3 ^ 40 * 3968837 * 2
def baseEnd_3968837 : Nat := 1358614013565595760456771

theorem tailTrace_3968837 : CollatzResearch.WordTrace tailWord_3968837 prefixEnd_3968837 1358614013565595760456771 := by
  unfold tailWord_3968837
  simp only [CollatzResearch.WordTrace]
  refine ⟨144755377522588847240432765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96503585015059231493621843 144755377522588847240432765)
  ·
    refine ⟨54283266570970817715162287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144755377522588847240432765 54283266570970817715162287)
    ·
      refine ⟨81424899856456226572743431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54283266570970817715162287 81424899856456226572743431)
      ·
        refine ⟨122137349784684339859115147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81424899856456226572743431 122137349784684339859115147)
        ·
          refine ⟨183206024677026509788672721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122137349784684339859115147 183206024677026509788672721)
          ·
            refine ⟨137404518507769882341504541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183206024677026509788672721 137404518507769882341504541)
            ·
              refine ⟨51526694440413705878064203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137404518507769882341504541 51526694440413705878064203)
              ·
                refine ⟨77290041660620558817096305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51526694440413705878064203 77290041660620558817096305)
                ·
                  refine ⟨57967531245465419112822229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77290041660620558817096305 57967531245465419112822229)
                  ·
                    refine ⟨1358614013565595760456771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57967531245465419112822229 1358614013565595760456771)
                    ·
                      rfl

theorem cell22_3968837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_3968837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968837 prefixEnd_3968837 := by exact prefixLift 3968837
  have htrace : WordTrace (prefixWord ++ tailWord_3968837) baseStart_3968837 baseEnd_3968837 := by
    simpa [prefixWord, tailWord_3968837, baseEnd_3968837] using wordTrace_append hprefix tailTrace_3968837
  have hstable : (prefixWord ++ tailWord_3968837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968837).length < 2 ^ (prefixWord ++ tailWord_3968837).sum := by decide
  have hdescent : baseEnd_3968837 < baseStart_3968837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968839 : List Nat := [1, 1, 4, 1, 2, 1, 6, 6]
def baseStart_3968839 : Nat := 118140960795 + 3968839 * 2 ^ 59
def prefixEnd_3968839 : Nat := 4983230072969 + 3 ^ 40 * 3968839 * 2
def baseEnd_3968839 : Nat := 150957188689607602434085

theorem tailTrace_3968839 : CollatzResearch.WordTrace tailWord_3968839 prefixEnd_3968839 150957188689607602434085 := by
  unfold tailWord_3968839
  simp only [CollatzResearch.WordTrace]
  refine ⟨144755450468581601582005571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96503633645721067721337047 144755450468581601582005571)
  ·
    refine ⟨217133175702872402373008357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144755450468581601582005571 217133175702872402373008357)
    ·
      refine ⟨40712470444288575444939067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217133175702872402373008357 40712470444288575444939067)
      ·
        refine ⟨61068705666432863167408601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40712470444288575444939067 61068705666432863167408601)
        ·
          refine ⟨45801529249824647375556451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61068705666432863167408601 45801529249824647375556451)
          ·
            refine ⟨68702293874736971063334677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45801529249824647375556451 68702293874736971063334677)
            ·
              refine ⟨3220420025378295518593813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68702293874736971063334677 3220420025378295518593813)
              ·
                refine ⟨150957188689607602434085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3220420025378295518593813 150957188689607602434085)
                ·
                  rfl

theorem cell22_3968839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 6].length) (baseStart_3968839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968839 prefixEnd_3968839 := by exact prefixLift 3968839
  have htrace : WordTrace (prefixWord ++ tailWord_3968839) baseStart_3968839 baseEnd_3968839 := by
    simpa [prefixWord, tailWord_3968839, baseEnd_3968839] using wordTrace_append hprefix tailTrace_3968839
  have hstable : (prefixWord ++ tailWord_3968839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968839).length < 2 ^ (prefixWord ++ tailWord_3968839).sum := by decide
  have hdescent : baseEnd_3968839 < baseStart_3968839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968845 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3968845 : Nat := 118140960795 + 3968845 * 2 ^ 59
def prefixEnd_3968845 : Nat := 4983230072969 + 3 ^ 40 * 3968845 * 2
def baseEnd_3968845 : Nat := 452872250709695468752249

theorem tailTrace_3968845 : CollatzResearch.WordTrace tailWord_3968845 prefixEnd_3968845 452872250709695468752249 := by
  unfold tailWord_3968845
  simp only [CollatzResearch.WordTrace]
  refine ⟨144755669306559864606723989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96503779537706576404482659 144755669306559864606723989)
  ·
    refine ⟨6785421998744993653440187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144755669306559864606723989 6785421998744993653440187)
    ·
      refine ⟨10178132998117490480160281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6785421998744993653440187 10178132998117490480160281)
      ·
        refine ⟨7633599748588117860120211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10178132998117490480160281 7633599748588117860120211)
        ·
          refine ⟨11450399622882176790180317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7633599748588117860120211 11450399622882176790180317)
          ·
            refine ⟨4293899858580816296317619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11450399622882176790180317 4293899858580816296317619)
            ·
              refine ⟨6440849787871224444476429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293899858580816296317619 6440849787871224444476429)
              ·
                refine ⟨2415318670451709166678661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6440849787871224444476429 2415318670451709166678661)
                ·
                  refine ⟨452872250709695468752249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415318670451709166678661 452872250709695468752249)
                  ·
                    rfl

theorem cell22_3968845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3968845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968845 prefixEnd_3968845 := by exact prefixLift 3968845
  have htrace : WordTrace (prefixWord ++ tailWord_3968845) baseStart_3968845 baseEnd_3968845 := by
    simpa [prefixWord, tailWord_3968845, baseEnd_3968845] using wordTrace_append hprefix tailTrace_3968845
  have hstable : (prefixWord ++ tailWord_3968845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968845).length < 2 ^ (prefixWord ++ tailWord_3968845).sum := by decide
  have hdescent : baseEnd_3968845 < baseStart_3968845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968922 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 1, 3]
def baseStart_3968922 : Nat := 118140960795 + 3968922 * 2 ^ 59
def prefixEnd_3968922 : Nat := 4983230072969 + 3 ^ 40 * 3968922 * 2
def baseEnd_3968922 : Nat := 1358643110802683872081511

theorem tailTrace_3968922 : CollatzResearch.WordTrace tailWord_3968922 prefixEnd_3968922 1358643110802683872081511 := by
  unfold tailWord_3968922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36189619431820226689319255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96505651818187271171518013 36189619431820226689319255)
  ·
    refine ⟨54284429147730340033978883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36189619431820226689319255 54284429147730340033978883)
    ·
      refine ⟨81426643721595510050968325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54284429147730340033978883 81426643721595510050968325)
      ·
        refine ⟨15267495697799158134556561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81426643721595510050968325 15267495697799158134556561)
        ·
          refine ⟨11450621773349368600917421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15267495697799158134556561 11450621773349368600917421)
          ·
            refine ⟨4293983165006013225344033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11450621773349368600917421 4293983165006013225344033)
            ·
              refine ⟨3220487373754509919008025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4293983165006013225344033 3220487373754509919008025)
              ·
                refine ⟨2415365530315882439256019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220487373754509919008025 2415365530315882439256019)
                ·
                  refine ⟨3623048295473823658884029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415365530315882439256019 3623048295473823658884029)
                  ·
                    refine ⟨1358643110802683872081511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623048295473823658884029 1358643110802683872081511)
                    ·
                      rfl

theorem cell22_3968922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 3].length) (baseStart_3968922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968922 prefixEnd_3968922 := by exact prefixLift 3968922
  have htrace : WordTrace (prefixWord ++ tailWord_3968922) baseStart_3968922 baseEnd_3968922 := by
    simpa [prefixWord, tailWord_3968922, baseEnd_3968922] using wordTrace_append hprefix tailTrace_3968922
  have hstable : (prefixWord ++ tailWord_3968922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968922).length < 2 ^ (prefixWord ++ tailWord_3968922).sum := by decide
  have hdescent : baseEnd_3968922 < baseStart_3968922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968959 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_3968959 : Nat := 118140960795 + 3968959 * 2 ^ 59
def prefixEnd_3968959 : Nat := 4983230072969 + 3 ^ 40 * 3968959 * 2
def baseEnd_3968959 : Nat := 1358655776658828108906397

theorem tailTrace_3968959 : CollatzResearch.WordTrace tailWord_3968959 prefixEnd_3968959 1358655776658828108906397 := by
  unfold tailWord_3968959
  simp only [CollatzResearch.WordTrace]
  refine ⟨144759827228146862076373931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96506551485431241384249287 144759827228146862076373931)
  ·
    refine ⟨217139740842220293114560897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144759827228146862076373931 217139740842220293114560897)
    ·
      refine ⟨162854805631665219835920673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217139740842220293114560897 162854805631665219835920673)
      ·
        refine ⟨122141104223748914876940505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162854805631665219835920673 122141104223748914876940505)
        ·
          refine ⟨91605828167811686157705379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122141104223748914876940505 91605828167811686157705379)
          ·
            refine ⟨137408742251717529236558069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91605828167811686157705379 137408742251717529236558069)
            ·
              refine ⟨12882069586098518365927319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137408742251717529236558069 12882069586098518365927319)
              ·
                refine ⟨19323104379147777548890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12882069586098518365927319 19323104379147777548890979)
                ·
                  refine ⟨28984656568721666323336469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19323104379147777548890979 28984656568721666323336469)
                  ·
                    refine ⟨1358655776658828108906397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28984656568721666323336469 1358655776658828108906397)
                    ·
                      rfl

theorem cell22_3968959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_3968959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968959 prefixEnd_3968959 := by exact prefixLift 3968959
  have htrace : WordTrace (prefixWord ++ tailWord_3968959) baseStart_3968959 baseEnd_3968959 := by
    simpa [prefixWord, tailWord_3968959, baseEnd_3968959] using wordTrace_append hprefix tailTrace_3968959
  have hstable : (prefixWord ++ tailWord_3968959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968959).length < 2 ^ (prefixWord ++ tailWord_3968959).sum := by decide
  have hdescent : baseEnd_3968959 < baseStart_3968959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968974 : List Nat := [4, 1, 1, 1, 2, 2, 11]
def baseStart_3968974 : Nat := 118140960795 + 3968974 * 2 ^ 59
def prefixEnd_3968974 : Nat := 4983230072969 + 3 ^ 40 * 3968974 * 2
def baseEnd_3968974 : Nat := 50320774498717521103013

theorem tailTrace_3968974 : CollatzResearch.WordTrace tailWord_3968974 prefixEnd_3968974 50320774498717521103013 := by
  unfold tailWord_3968974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18095046790386564954771247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96506916215395013092113317 18095046790386564954771247)
  ·
    refine ⟨27142570185579847432156871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18095046790386564954771247 27142570185579847432156871)
    ·
      refine ⟨40713855278369771148235307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27142570185579847432156871 40713855278369771148235307)
      ·
        refine ⟨61070782917554656722352961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40713855278369771148235307 61070782917554656722352961)
        ·
          refine ⟨45803087188165992541764721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61070782917554656722352961 45803087188165992541764721)
          ·
            refine ⟨34352315391124494406323541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45803087188165992541764721 34352315391124494406323541)
            ·
              refine ⟨50320774498717521103013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34352315391124494406323541 50320774498717521103013)
              ·
                rfl

theorem cell22_3968974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 11].length) (baseStart_3968974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968974 prefixEnd_3968974 := by exact prefixLift 3968974
  have htrace : WordTrace (prefixWord ++ tailWord_3968974) baseStart_3968974 baseEnd_3968974 := by
    simpa [prefixWord, tailWord_3968974, baseEnd_3968974] using wordTrace_append hprefix tailTrace_3968974
  have hstable : (prefixWord ++ tailWord_3968974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968974).length < 2 ^ (prefixWord ++ tailWord_3968974).sum := by decide
  have hdescent : baseEnd_3968974 < baseStart_3968974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3968995 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 2, 3]
def baseStart_3968995 : Nat := 118140960795 + 3968995 * 2 ^ 59
def prefixEnd_3968995 : Nat := 4983230072969 + 3 ^ 40 * 3968995 * 2
def baseEnd_3968995 : Nat := 1358668100194536015006287

theorem tailTrace_3968995 : CollatzResearch.WordTrace tailWord_3968995 prefixEnd_3968995 1358668100194536015006287 := by
  unfold tailWord_3968995
  simp only [CollatzResearch.WordTrace]
  refine ⟨144761140256016440224684439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96507426837344293483122959 144761140256016440224684439)
  ·
    refine ⟨217141710384024660337026659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144761140256016440224684439 217141710384024660337026659)
    ·
      refine ⟨325712565576036990505539989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217141710384024660337026659 325712565576036990505539989)
      ·
        refine ⟨15267776511376733929947187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 325712565576036990505539989 15267776511376733929947187)
        ·
          refine ⟨22901664767065100894920781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15267776511376733929947187 22901664767065100894920781)
          ·
            refine ⟨8588124287649412835595293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22901664767065100894920781 8588124287649412835595293)
            ·
              refine ⟨3220546607868529813348235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8588124287649412835595293 3220546607868529813348235)
              ·
                refine ⟨4830819911802794720022353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3220546607868529813348235 4830819911802794720022353)
                ·
                  refine ⟨3623114933852096040016765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830819911802794720022353 3623114933852096040016765)
                  ·
                    refine ⟨1358668100194536015006287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623114933852096040016765 1358668100194536015006287)
                    ·
                      rfl

theorem cell22_3968995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 3].length) (baseStart_3968995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3968995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3968995 prefixEnd_3968995 := by exact prefixLift 3968995
  have htrace : WordTrace (prefixWord ++ tailWord_3968995) baseStart_3968995 baseEnd_3968995 := by
    simpa [prefixWord, tailWord_3968995, baseEnd_3968995] using wordTrace_append hprefix tailTrace_3968995
  have hstable : (prefixWord ++ tailWord_3968995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3968995).length < 2 ^ (prefixWord ++ tailWord_3968995).sum := by decide
  have hdescent : baseEnd_3968995 < baseStart_3968995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3968995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969004 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_3969004 : Nat := 118140960795 + 3969004 * 2 ^ 59
def prefixEnd_3969004 : Nat := 4983230072969 + 3 ^ 40 * 3969004 * 2
def baseEnd_3969004 : Nat := 1358671181078462991531259

theorem tailTrace_3969004 : CollatzResearch.WordTrace tailWord_3969004 prefixEnd_3969004 1358671181078462991531259 := by
  unfold tailWord_3969004
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380734256491917380881033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96507645675322556507841377 72380734256491917380881033)
  ·
    refine ⟨54285550692368938035660775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72380734256491917380881033 54285550692368938035660775)
    ·
      refine ⟨81428326038553407053491163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54285550692368938035660775 81428326038553407053491163)
      ·
        refine ⟨122142489057830110580236745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81428326038553407053491163 122142489057830110580236745)
        ·
          refine ⟨91606866793372582935177559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122142489057830110580236745 91606866793372582935177559)
          ·
            refine ⟨137410300190058874402766339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91606866793372582935177559 137410300190058874402766339)
            ·
              refine ⟨206115450285088311604149509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137410300190058874402766339 206115450285088311604149509)
              ·
                refine ⟨38646646928454058425778033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206115450285088311604149509 38646646928454058425778033)
                ·
                  refine ⟨28984985196340543819333525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38646646928454058425778033 28984985196340543819333525)
                  ·
                    refine ⟨1358671181078462991531259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28984985196340543819333525 1358671181078462991531259)
                    ·
                      rfl

theorem cell22_3969004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_3969004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969004 prefixEnd_3969004 := by exact prefixLift 3969004
  have htrace : WordTrace (prefixWord ++ tailWord_3969004) baseStart_3969004 baseEnd_3969004 := by
    simpa [prefixWord, tailWord_3969004, baseEnd_3969004] using wordTrace_append hprefix tailTrace_3969004
  have hstable : (prefixWord ++ tailWord_3969004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969004).length < 2 ^ (prefixWord ++ tailWord_3969004).sum := by decide
  have hdescent : baseEnd_3969004 < baseStart_3969004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969019 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 7]
def baseStart_3969019 : Nat := 118140960795 + 3969019 * 2 ^ 59
def prefixEnd_3969019 : Nat := 4983230072969 + 3 ^ 40 * 3969019 * 2
def baseEnd_3969019 : Nat := 452892105295002650802071

theorem tailTrace_3969019 : CollatzResearch.WordTrace tailWord_3969019 prefixEnd_3969019 452892105295002650802071 := by
  unfold tailWord_3969019
  simp only [CollatzResearch.WordTrace]
  refine ⟨144762015607929492323558111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96508010405286328215705407 144762015607929492323558111)
  ·
    refine ⟨217143023411894238485337167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144762015607929492323558111 217143023411894238485337167)
    ·
      refine ⟨325714535117841357728005751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217143023411894238485337167 325714535117841357728005751)
      ·
        refine ⟨488571802676762036592008627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325714535117841357728005751 488571802676762036592008627)
        ·
          refine ⟨732857704015143054888012941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488571802676762036592008627 732857704015143054888012941)
          ·
            refine ⟨274821639005678645583004853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 732857704015143054888012941 274821639005678645583004853)
            ·
              refine ⟨25764528656782373023406705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 274821639005678645583004853 25764528656782373023406705)
              ·
                refine ⟨19323396492586779767555029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25764528656782373023406705 19323396492586779767555029)
                ·
                  refine ⟨452892105295002650802071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19323396492586779767555029 452892105295002650802071)
                  ·
                    rfl

theorem cell22_3969019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_3969019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969019 prefixEnd_3969019 := by exact prefixLift 3969019
  have htrace : WordTrace (prefixWord ++ tailWord_3969019) baseStart_3969019 baseEnd_3969019 := by
    simpa [prefixWord, tailWord_3969019, baseEnd_3969019] using wordTrace_append hprefix tailTrace_3969019
  have hstable : (prefixWord ++ tailWord_3969019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969019).length < 2 ^ (prefixWord ++ tailWord_3969019).sum := by decide
  have hdescent : baseEnd_3969019 < baseStart_3969019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969036 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_3969036 : Nat := 118140960795 + 3969036 * 2 ^ 59
def prefixEnd_3969036 : Nat := 4983230072969 + 3 ^ 40 * 3969036 * 2
def baseEnd_3969036 : Nat := 452894045110808524910387

theorem tailTrace_3969036 : CollatzResearch.WordTrace tailWord_3969036 prefixEnd_3969036 452894045110808524910387 := by
  unfold tailWord_3969036
  simp only [CollatzResearch.WordTrace]
  refine ⟨72381317824433952113463481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96508423765911936151284641 72381317824433952113463481)
  ·
    refine ⟨54285988368325464085097611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72381317824433952113463481 54285988368325464085097611)
    ·
      refine ⟨81428982552488196127646417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54285988368325464085097611 81428982552488196127646417)
      ·
        refine ⟨61071736914366147095734813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81428982552488196127646417 61071736914366147095734813)
        ·
          refine ⟨22901901342887305160900555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61071736914366147095734813 22901901342887305160900555)
          ·
            refine ⟨34352852014330957741350833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22901901342887305160900555 34352852014330957741350833)
            ·
              refine ⟨25764639010748218306013125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34352852014330957741350833 25764639010748218306013125)
              ·
                refine ⟨4830869814515290932377461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25764639010748218306013125 4830869814515290932377461)
                ·
                  refine ⟨452894045110808524910387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4830869814515290932377461 452894045110808524910387)
                  ·
                    rfl

theorem cell22_3969036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_3969036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969036 prefixEnd_3969036 := by exact prefixLift 3969036
  have htrace : WordTrace (prefixWord ++ tailWord_3969036) baseStart_3969036 baseEnd_3969036 := by
    simpa [prefixWord, tailWord_3969036, baseEnd_3969036] using wordTrace_append hprefix tailTrace_3969036
  have hstable : (prefixWord ++ tailWord_3969036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969036).length < 2 ^ (prefixWord ++ tailWord_3969036).sum := by decide
  have hdescent : baseEnd_3969036 < baseStart_3969036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969049 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_3969049 : Nat := 118140960795 + 3969049 * 2 ^ 59
def prefixEnd_3969049 : Nat := 4983230072969 + 3 ^ 40 * 3969049 * 2
def baseEnd_3969049 : Nat := 1358686585498097874156121

theorem tailTrace_3969049 : CollatzResearch.WordTrace tailWord_3969049 prefixEnd_3969049 1358686585498097874156121 := by
  unfold tailWord_3969049
  simp only [CollatzResearch.WordTrace]
  refine ⟨144763109797820807447150201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96508739865213871631433467 144763109797820807447150201)
  ·
    refine ⟨108572332348365605585362651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144763109797820807447150201 108572332348365605585362651)
    ·
      refine ⟨162858498522548408378043977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108572332348365605585362651 162858498522548408378043977)
      ·
        refine ⟨122143873891911306283532983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162858498522548408378043977 122143873891911306283532983)
        ·
          refine ⟨183215810837866959425299475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122143873891911306283532983 183215810837866959425299475)
          ·
            refine ⟨274823716256800439137949213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183215810837866959425299475 274823716256800439137949213)
            ·
              refine ⟨103058893596300164676730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274823716256800439137949213 103058893596300164676730955)
              ·
                refine ⟨154588340394450247015096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103058893596300164676730955 154588340394450247015096433)
                ·
                  refine ⟨115941255295837685261322325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154588340394450247015096433 115941255295837685261322325)
                  ·
                    refine ⟨1358686585498097874156121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 115941255295837685261322325 1358686585498097874156121)
                    ·
                      rfl

theorem cell22_3969049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_3969049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969049 prefixEnd_3969049 := by exact prefixLift 3969049
  have htrace : WordTrace (prefixWord ++ tailWord_3969049) baseStart_3969049 baseEnd_3969049 := by
    simpa [prefixWord, tailWord_3969049, baseEnd_3969049] using wordTrace_append hprefix tailTrace_3969049
  have hstable : (prefixWord ++ tailWord_3969049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969049).length < 2 ^ (prefixWord ++ tailWord_3969049).sum := by decide
  have hdescent : baseEnd_3969049 < baseStart_3969049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969053 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 5]
def baseStart_3969053 : Nat := 118140960795 + 3969053 * 2 ^ 59
def prefixEnd_3969053 : Nat := 4983230072969 + 3 ^ 40 * 3969053 * 2
def baseEnd_3969053 : Nat := 452895984926614399018703

theorem tailTrace_3969053 : CollatzResearch.WordTrace tailWord_3969053 prefixEnd_3969053 452895984926614399018703 := by
  unfold tailWord_3969053
  simp only [CollatzResearch.WordTrace]
  refine ⟨144763255689806316130295813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96508837126537544086863875 144763255689806316130295813)
  ·
    refine ⟨27143110441838684274430465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144763255689806316130295813 27143110441838684274430465)
    ·
      refine ⟨20357332831379013205822849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27143110441838684274430465 20357332831379013205822849)
      ·
        refine ⟨15267999623534259904367137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20357332831379013205822849 15267999623534259904367137)
        ·
          refine ⟨11450999717650694928275353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15267999623534259904367137 11450999717650694928275353)
          ·
            refine ⟨8588249788238021196206515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11450999717650694928275353 8588249788238021196206515)
            ·
              refine ⟨12882374682357031794309773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8588249788238021196206515 12882374682357031794309773)
              ·
                refine ⟨4830890505883886922866165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12882374682357031794309773 4830890505883886922866165)
                ·
                  refine ⟨452895984926614399018703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4830890505883886922866165 452895984926614399018703)
                  ·
                    rfl

theorem cell22_3969053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_3969053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969053 prefixEnd_3969053 := by exact prefixLift 3969053
  have htrace : WordTrace (prefixWord ++ tailWord_3969053) baseStart_3969053 baseEnd_3969053 := by
    simpa [prefixWord, tailWord_3969053, baseEnd_3969053] using wordTrace_append hprefix tailTrace_3969053
  have hstable : (prefixWord ++ tailWord_3969053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969053).length < 2 ^ (prefixWord ++ tailWord_3969053).sum := by decide
  have hdescent : baseEnd_3969053 < baseStart_3969053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969111 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_3969111 : Nat := 118140960795 + 3969111 * 2 ^ 59
def prefixEnd_3969111 : Nat := 4983230072969 + 3 ^ 40 * 3969111 * 2
def baseEnd_3969111 : Nat := 1358707809365150379105931

theorem tailTrace_3969111 : CollatzResearch.WordTrace tailWord_3969111 prefixEnd_3969111 1358707809365150379105931 := by
  unfold tailWord_3969111
  simp only [CollatzResearch.WordTrace]
  refine ⟨144765371123596192035907187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96510247415730794690604791 144765371123596192035907187)
  ·
    refine ⟨217148056685394288053860781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144765371123596192035907187 217148056685394288053860781)
    ·
      refine ⟨81430521257022858020197793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217148056685394288053860781 81430521257022858020197793)
      ·
        refine ⟨61072890942767143515148345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81430521257022858020197793 61072890942767143515148345)
        ·
          refine ⟨45804668207075357636361259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61072890942767143515148345 45804668207075357636361259)
          ·
            refine ⟨68707002310613036454541889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45804668207075357636361259 68707002310613036454541889)
            ·
              refine ⟨51530251732959777340906417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68707002310613036454541889 51530251732959777340906417)
              ·
                refine ⟨38647688799719833005679813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51530251732959777340906417 38647688799719833005679813)
                ·
                  refine ⟨7246441649947468688564965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38647688799719833005679813 7246441649947468688564965)
                  ·
                    refine ⟨1358707809365150379105931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7246441649947468688564965 1358707809365150379105931)
                    ·
                      rfl

theorem cell22_3969111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_3969111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969111 prefixEnd_3969111 := by exact prefixLift 3969111
  have htrace : WordTrace (prefixWord ++ tailWord_3969111) baseStart_3969111 baseEnd_3969111 := by
    simpa [prefixWord, tailWord_3969111, baseEnd_3969111] using wordTrace_append hprefix tailTrace_3969111
  have hstable : (prefixWord ++ tailWord_3969111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969111).length < 2 ^ (prefixWord ++ tailWord_3969111).sum := by decide
  have hdescent : baseEnd_3969111 < baseStart_3969111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969113 : List Nat := [1, 2, 1, 2, 2, 1, 3, 5, 2, 3]
def baseStart_3969113 : Nat := 118140960795 + 3969113 * 2 ^ 59
def prefixEnd_3969113 : Nat := 4983230072969 + 3 ^ 40 * 3969113 * 2
def baseEnd_3969113 : Nat := 1358708494006023040555925

theorem tailTrace_3969113 : CollatzResearch.WordTrace tailWord_3969113 prefixEnd_3969113 1358708494006023040555925 := by
  unfold tailWord_3969113
  simp only [CollatzResearch.WordTrace]
  refine ⟨144765444069588946377479993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96510296046392630918319995 144765444069588946377479993)
  ·
    refine ⟨108574083052191709783109995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144765444069588946377479993 108574083052191709783109995)
    ·
      refine ⟨162861124578287564674664993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108574083052191709783109995 162861124578287564674664993)
      ·
        refine ⟨122145843433715673505998745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162861124578287564674664993 122145843433715673505998745)
        ·
          refine ⟨91609382575286755129499059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122145843433715673505998745 91609382575286755129499059)
          ·
            refine ⟨137414073862930132694248589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91609382575286755129499059 137414073862930132694248589)
            ·
              refine ⟨51530277698598799760343221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137414073862930132694248589 51530277698598799760343221)
              ·
                refine ⟨4830963534243637477532177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51530277698598799760343221 4830963534243637477532177)
                ·
                  refine ⟨3623222650682728108149133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4830963534243637477532177 3623222650682728108149133)
                  ·
                    refine ⟨1358708494006023040555925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623222650682728108149133 1358708494006023040555925)
                    ·
                      rfl

theorem cell22_3969113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_3969113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969113 prefixEnd_3969113 := by exact prefixLift 3969113
  have htrace : WordTrace (prefixWord ++ tailWord_3969113) baseStart_3969113 baseEnd_3969113 := by
    simpa [prefixWord, tailWord_3969113, baseEnd_3969113] using wordTrace_append hprefix tailTrace_3969113
  have hstable : (prefixWord ++ tailWord_3969113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969113).length < 2 ^ (prefixWord ++ tailWord_3969113).sum := by decide
  have hdescent : baseEnd_3969113 < baseStart_3969113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969248 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_3969248 : Nat := 118140960795 + 3969248 * 2 ^ 59
def prefixEnd_3969248 : Nat := 4983230072969 + 3 ^ 40 * 3969248 * 2
def baseEnd_3969248 : Nat := 1358754707264927688430511

theorem tailTrace_3969248 : CollatzResearch.WordTrace tailWord_3969248 prefixEnd_3969248 1358754707264927688430511 := by
  unfold tailWord_3969248
  simp only [CollatzResearch.WordTrace]
  refine ⟨72385183962049932216822199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96513578616066576289096265 72385183962049932216822199)
  ·
    refine ⟨108577775943074898325233299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72385183962049932216822199 108577775943074898325233299)
    ·
      refine ⟨162866663914612347487849949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108577775943074898325233299 162866663914612347487849949)
      ·
        refine ⟨61074998967979630307943731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162866663914612347487849949 61074998967979630307943731)
        ·
          refine ⟨91612498451969445461915597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61074998967979630307943731 91612498451969445461915597)
          ·
            refine ⟨34354686919488542048218349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91612498451969445461915597 34354686919488542048218349)
            ·
              refine ⟨12883007594808203268081881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34354686919488542048218349 12883007594808203268081881)
              ·
                refine ⟨9662255696106152451061411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12883007594808203268081881 9662255696106152451061411)
                ·
                  refine ⟨14493383544159228676592117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662255696106152451061411 14493383544159228676592117)
                  ·
                    refine ⟨1358754707264927688430511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14493383544159228676592117 1358754707264927688430511)
                    ·
                      rfl

theorem cell22_3969248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_3969248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969248 prefixEnd_3969248 := by exact prefixLift 3969248
  have htrace : WordTrace (prefixWord ++ tailWord_3969248) baseStart_3969248 baseEnd_3969248 := by
    simpa [prefixWord, tailWord_3969248, baseEnd_3969248] using wordTrace_append hprefix tailTrace_3969248
  have hstable : (prefixWord ++ tailWord_3969248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969248).length < 2 ^ (prefixWord ++ tailWord_3969248).sum := by decide
  have hdescent : baseEnd_3969248 < baseStart_3969248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969265 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_3969265 : Nat := 118140960795 + 3969265 * 2 ^ 59
def prefixEnd_3969265 : Nat := 4983230072969 + 3 ^ 40 * 3969265 * 2
def baseEnd_3969265 : Nat := 1358760526712345310755459

theorem tailTrace_3969265 : CollatzResearch.WordTrace tailWord_3969265 prefixEnd_3969265 1358760526712345310755459 := by
  unfold tailWord_3969265
  simp only [CollatzResearch.WordTrace]
  refine ⟨144770987965038276337013249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96513991976692184224675499 144770987965038276337013249)
  ·
    refine ⟨108578240973778707252759937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144770987965038276337013249 108578240973778707252759937)
    ·
      refine ⟨81433680730334030439569953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108578240973778707252759937 81433680730334030439569953)
      ·
        refine ⟨61075260547750522829677465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81433680730334030439569953 61075260547750522829677465)
        ·
          refine ⟨45806445410812892122258099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61075260547750522829677465 45806445410812892122258099)
          ·
            refine ⟨68709668116219338183387149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45806445410812892122258099 68709668116219338183387149)
            ·
              refine ⟨25766125543582251818770181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68709668116219338183387149 25766125543582251818770181)
              ·
                refine ⟨4831148539421672216019409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25766125543582251818770181 4831148539421672216019409)
                ·
                  refine ⟨3623361404566254162014557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831148539421672216019409 3623361404566254162014557)
                  ·
                    refine ⟨1358760526712345310755459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623361404566254162014557 1358760526712345310755459)
                    ·
                      rfl

theorem cell22_3969265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_3969265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969265 prefixEnd_3969265 := by exact prefixLift 3969265
  have htrace : WordTrace (prefixWord ++ tailWord_3969265) baseStart_3969265 baseEnd_3969265 := by
    simpa [prefixWord, tailWord_3969265, baseEnd_3969265] using wordTrace_append hprefix tailTrace_3969265
  have hstable : (prefixWord ++ tailWord_3969265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969265).length < 2 ^ (prefixWord ++ tailWord_3969265).sum := by decide
  have hdescent : baseEnd_3969265 < baseStart_3969265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969282 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3969282 : Nat := 118140960795 + 3969282 * 2 ^ 59
def prefixEnd_3969282 : Nat := 4983230072969 + 3 ^ 40 * 3969282 * 2
def baseEnd_3969282 : Nat := 1358766346159762933080407

theorem tailTrace_3969282 : CollatzResearch.WordTrace tailWord_3969282 prefixEnd_3969282 1358766346159762933080407 := by
  unfold tailWord_3969282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36192902001494172060095525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96514405337317792160254733 36192902001494172060095525)
  ·
    refine ⟨6786169125280157261267911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36192902001494172060095525 6786169125280157261267911)
    ·
      refine ⟨10179253687920235891901867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786169125280157261267911 10179253687920235891901867)
      ·
        refine ⟨15268880531880353837852801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179253687920235891901867 15268880531880353837852801)
        ·
          refine ⟨11451660398910265378389601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15268880531880353837852801 11451660398910265378389601)
          ·
            refine ⟨8588745299182699033792201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11451660398910265378389601 8588745299182699033792201)
            ·
              refine ⟨6441558974387024275344151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8588745299182699033792201 6441558974387024275344151)
              ·
                refine ⟨9662338461580536413016227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441558974387024275344151 9662338461580536413016227)
                ·
                  refine ⟨14493507692370804619524341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662338461580536413016227 14493507692370804619524341)
                  ·
                    refine ⟨1358766346159762933080407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14493507692370804619524341 1358766346159762933080407)
                    ·
                      rfl

theorem cell22_3969282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3969282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969282 prefixEnd_3969282 := by exact prefixLift 3969282
  have htrace : WordTrace (prefixWord ++ tailWord_3969282) baseStart_3969282 baseEnd_3969282 := by
    simpa [prefixWord, tailWord_3969282, baseEnd_3969282] using wordTrace_append hprefix tailTrace_3969282
  have hstable : (prefixWord ++ tailWord_3969282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969282).length < 2 ^ (prefixWord ++ tailWord_3969282).sum := by decide
  have hdescent : baseEnd_3969282 < baseStart_3969282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969327 : List Nat := [1, 1, 2, 1, 2, 1, 6, 4, 1, 3]
def baseStart_3969327 : Nat := 118140960795 + 3969327 * 2 ^ 59
def prefixEnd_3969327 : Nat := 4983230072969 + 3 ^ 40 * 3969327 * 2
def baseEnd_3969327 : Nat := 1358781750579397815705269

theorem tailTrace_3969327 : CollatzResearch.WordTrace tailWord_3969327 prefixEnd_3969327 1358781750579397815705269 := by
  unfold tailWord_3969327
  simp only [CollatzResearch.WordTrace]
  refine ⟨144773249290813660925770235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96515499527209107283846823 144773249290813660925770235)
  ·
    refine ⟨217159873936220491388655353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144773249290813660925770235 217159873936220491388655353)
    ·
      refine ⟨162869905452165368541491515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217159873936220491388655353 162869905452165368541491515)
      ·
        refine ⟨244304858178248052812237273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162869905452165368541491515 244304858178248052812237273)
        ·
          refine ⟨183228643633686039609177955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244304858178248052812237273 183228643633686039609177955)
          ·
            refine ⟨274842965450529059413766933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183228643633686039609177955 274842965450529059413766933)
            ·
              refine ⟨12883264005493549660020325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274842965450529059413766933 12883264005493549660020325)
              ·
                refine ⟨2415612001030040561253811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12883264005493549660020325 2415612001030040561253811)
                ·
                  refine ⟨3623418001545060841880717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415612001030040561253811 3623418001545060841880717)
                  ·
                    refine ⟨1358781750579397815705269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623418001545060841880717 1358781750579397815705269)
                    ·
                      rfl

theorem cell22_3969327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_3969327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969327 prefixEnd_3969327 := by exact prefixLift 3969327
  have htrace : WordTrace (prefixWord ++ tailWord_3969327) baseStart_3969327 baseEnd_3969327 := by
    simpa [prefixWord, tailWord_3969327, baseEnd_3969327] using wordTrace_append hprefix tailTrace_3969327
  have hstable : (prefixWord ++ tailWord_3969327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969327).length < 2 ^ (prefixWord ++ tailWord_3969327).sum := by decide
  have hdescent : baseEnd_3969327 < baseStart_3969327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969432 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_3969432 : Nat := 118140960795 + 3969432 * 2 ^ 59
def prefixEnd_3969432 : Nat := 4983230072969 + 3 ^ 40 * 3969432 * 2
def baseEnd_3969432 : Nat := 1358817694225212541829947

theorem tailTrace_3969432 : CollatzResearch.WordTrace tailWord_3969432 prefixEnd_3969432 1358817694225212541829947 := by
  unfold tailWord_3969432
  simp only [CollatzResearch.WordTrace]
  refine ⟨72388539477716631929171275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96518052636955509238895033 72388539477716631929171275)
  ·
    refine ⟨108582809216574947893756913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72388539477716631929171275 108582809216574947893756913)
    ·
      refine ⟨81437106912431210920317685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108582809216574947893756913 81437106912431210920317685)
      ·
        refine ⟨7634728773040426023779783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81437106912431210920317685 7634728773040426023779783)
        ·
          refine ⟨11452093159560639035669675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7634728773040426023779783 11452093159560639035669675)
          ·
            refine ⟨17178139739340958553504513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452093159560639035669675 17178139739340958553504513)
            ·
              refine ⟨12883604804505718915128385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17178139739340958553504513 12883604804505718915128385)
              ·
                refine ⟨9662703603379289186346289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12883604804505718915128385 9662703603379289186346289)
                ·
                  refine ⟨7247027702534466889759717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9662703603379289186346289 7247027702534466889759717)
                  ·
                    refine ⟨1358817694225212541829947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7247027702534466889759717 1358817694225212541829947)
                    ·
                      rfl

theorem cell22_3969432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_3969432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969432 prefixEnd_3969432 := by exact prefixLift 3969432
  have htrace : WordTrace (prefixWord ++ tailWord_3969432) baseStart_3969432 baseEnd_3969432 := by
    simpa [prefixWord, tailWord_3969432, baseEnd_3969432] using wordTrace_append hprefix tailTrace_3969432
  have hstable : (prefixWord ++ tailWord_3969432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969432).length < 2 ^ (prefixWord ++ tailWord_3969432).sum := by decide
  have hdescent : baseEnd_3969432 < baseStart_3969432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969434 : List Nat := [3, 1, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_3969434 : Nat := 118140960795 + 3969434 * 2 ^ 59
def prefixEnd_3969434 : Nat := 4983230072969 + 3 ^ 40 * 3969434 * 2
def baseEnd_3969434 : Nat := 1358818378866085203279941

theorem tailTrace_3969434 : CollatzResearch.WordTrace tailWord_3969434 prefixEnd_3969434 1358818378866085203279941 := by
  unfold tailWord_3969434
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194287975356504549978839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96518101267617345466610237 36194287975356504549978839)
  ·
    refine ⟨54291431963034756824968259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36194287975356504549978839 54291431963034756824968259)
    ·
      refine ⟨81437147944552135237452389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54291431963034756824968259 81437147944552135237452389)
      ·
        refine ⟨15269465239603525357022323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81437147944552135237452389 15269465239603525357022323)
        ·
          refine ⟨22904197859405288035533485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269465239603525357022323 22904197859405288035533485)
          ·
            refine ⟨8589074197276983013325057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22904197859405288035533485 8589074197276983013325057)
            ·
              refine ⟨6441805647957737259993793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589074197276983013325057 6441805647957737259993793)
              ·
                refine ⟨4831354235968302944995345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441805647957737259993793 4831354235968302944995345)
                ·
                  refine ⟨3623515676976227208746509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831354235968302944995345 3623515676976227208746509)
                  ·
                    refine ⟨1358818378866085203279941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623515676976227208746509 1358818378866085203279941)
                    ·
                      rfl

theorem cell22_3969434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_3969434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969434 prefixEnd_3969434 := by exact prefixLift 3969434
  have htrace : WordTrace (prefixWord ++ tailWord_3969434) baseStart_3969434 baseEnd_3969434 := by
    simpa [prefixWord, tailWord_3969434, baseEnd_3969434] using wordTrace_append hprefix tailTrace_3969434
  have hstable : (prefixWord ++ tailWord_3969434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969434).length < 2 ^ (prefixWord ++ tailWord_3969434).sum := by decide
  have hdescent : baseEnd_3969434 < baseStart_3969434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969447 : List Nat := [1, 1, 6, 1, 1, 4, 1, 7]
def baseStart_3969447 : Nat := 118140960795 + 3969447 * 2 ^ 59
def prefixEnd_3969447 : Nat := 4983230072969 + 3 ^ 40 * 3969447 * 2
def baseEnd_3969447 : Nat := 150980314336861944744989

theorem tailTrace_3969447 : CollatzResearch.WordTrace tailWord_3969447 prefixEnd_3969447 150980314336861944744989 := by
  unfold tailWord_3969447
  simp only [CollatzResearch.WordTrace]
  refine ⟨144777626050378921420138595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96518417366919280946759063 144777626050378921420138595)
  ·
    refine ⟨217166439075568382130207893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144777626050378921420138595 217166439075568382130207893)
    ·
      refine ⟨10179676831667267912353495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217166439075568382130207893 10179676831667267912353495)
      ·
        refine ⟨15269515247500901868530243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179676831667267912353495 15269515247500901868530243)
        ·
          refine ⟨22904272871251352802795365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15269515247500901868530243 22904272871251352802795365)
          ·
            refine ⟨4294551163359628650524131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22904272871251352802795365 4294551163359628650524131)
            ·
              refine ⟨6441826745039442975786197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294551163359628650524131 6441826745039442975786197)
              ·
                refine ⟨150980314336861944744989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6441826745039442975786197 150980314336861944744989)
                ·
                  rfl

theorem cell22_3969447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 7].length) (baseStart_3969447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969447 prefixEnd_3969447 := by exact prefixLift 3969447
  have htrace : WordTrace (prefixWord ++ tailWord_3969447) baseStart_3969447 baseEnd_3969447 := by
    simpa [prefixWord, tailWord_3969447, baseEnd_3969447] using wordTrace_append hprefix tailTrace_3969447
  have hstable : (prefixWord ++ tailWord_3969447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969447).length < 2 ^ (prefixWord ++ tailWord_3969447).sum := by decide
  have hdescent : baseEnd_3969447 < baseStart_3969447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969479 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 1, 3]
def baseStart_3969479 : Nat := 118140960795 + 3969479 * 2 ^ 59
def prefixEnd_3969479 : Nat := 4983230072969 + 3 ^ 40 * 3969479 * 2
def baseEnd_3969479 : Nat := 1358833783285720085904803

theorem tailTrace_3969479 : CollatzResearch.WordTrace tailWord_3969479 prefixEnd_3969479 1358833783285720085904803 := by
  unfold tailWord_3969479
  simp only [CollatzResearch.WordTrace]
  refine ⟨144778793186262990885303491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96519195457508660590202327 144778793186262990885303491)
  ·
    refine ⟨217168189779394486327955237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144778793186262990885303491 217168189779394486327955237)
    ·
      refine ⟨40719035583636466186491607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217168189779394486327955237 40719035583636466186491607)
      ·
        refine ⟨61078553375454699279737411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40719035583636466186491607 61078553375454699279737411)
        ·
          refine ⟨91617830063182048919606117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61078553375454699279737411 91617830063182048919606117)
          ·
            refine ⟨17178343136846634172426147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91617830063182048919606117 17178343136846634172426147)
            ·
              refine ⟨25767514705269951258639221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17178343136846634172426147 25767514705269951258639221)
              ·
                refine ⟨2415704503619057930497427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25767514705269951258639221 2415704503619057930497427)
                ·
                  refine ⟨3623556755428586895746141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415704503619057930497427 3623556755428586895746141)
                  ·
                    refine ⟨1358833783285720085904803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623556755428586895746141 1358833783285720085904803)
                    ·
                      rfl

theorem cell22_3969479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_3969479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969479 prefixEnd_3969479 := by exact prefixLift 3969479
  have htrace : WordTrace (prefixWord ++ tailWord_3969479) baseStart_3969479 baseEnd_3969479 := by
    simpa [prefixWord, tailWord_3969479, baseEnd_3969479] using wordTrace_append hprefix tailTrace_3969479
  have hstable : (prefixWord ++ tailWord_3969479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969479).length < 2 ^ (prefixWord ++ tailWord_3969479).sum := by decide
  have hdescent : baseEnd_3969479 < baseStart_3969479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969492 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3969492 : Nat := 118140960795 + 3969492 * 2 ^ 59
def prefixEnd_3969492 : Nat := 4983230072969 + 3 ^ 40 * 3969492 * 2
def baseEnd_3969492 : Nat := 452946077817130795109921

theorem tailTrace_3969492 : CollatzResearch.WordTrace tailWord_3969492 prefixEnd_3969492 452946077817130795109921 := by
  unfold tailWord_3969492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72389633667607947052763365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96519511556810596070351153 72389633667607947052763365)
  ·
    refine ⟨13573056312676490072393131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72389633667607947052763365 13573056312676490072393131)
    ·
      refine ⟨20359584469014735108589697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13573056312676490072393131 20359584469014735108589697)
      ·
        refine ⟨15269688351761051331442273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20359584469014735108589697 15269688351761051331442273)
        ·
          refine ⟨11452266263820788498581705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15269688351761051331442273 11452266263820788498581705)
          ·
            refine ⟨8589199697865591373936279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11452266263820788498581705 8589199697865591373936279)
            ·
              refine ⟨12883799546798387060904419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8589199697865591373936279 12883799546798387060904419)
              ·
                refine ⟨19325699320197580591356629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12883799546798387060904419 19325699320197580591356629)
                ·
                  refine ⟨452946077817130795109921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19325699320197580591356629 452946077817130795109921)
                  ·
                    rfl

theorem cell22_3969492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3969492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969492 prefixEnd_3969492 := by exact prefixLift 3969492
  have htrace : WordTrace (prefixWord ++ tailWord_3969492) baseStart_3969492 baseEnd_3969492 := by
    simpa [prefixWord, tailWord_3969492, baseEnd_3969492] using wordTrace_append hprefix tailTrace_3969492
  have hstable : (prefixWord ++ tailWord_3969492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969492).length < 2 ^ (prefixWord ++ tailWord_3969492).sum := by decide
  have hdescent : baseEnd_3969492 < baseStart_3969492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969520 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_3969520 : Nat := 118140960795 + 3969520 * 2 ^ 59
def prefixEnd_3969520 : Nat := 4983230072969 + 3 ^ 40 * 3969520 * 2
def baseEnd_3969520 : Nat := 452949272807869881876559

theorem tailTrace_3969520 : CollatzResearch.WordTrace tailWord_3969520 prefixEnd_3969520 452949272807869881876559 := by
  unfold tailWord_3969520
  simp only [CollatzResearch.WordTrace]
  refine ⟨72390144289557227443773007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96520192386076303258364009 72390144289557227443773007)
  ·
    refine ⟨108585216434335841165659511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72390144289557227443773007 108585216434335841165659511)
    ·
      refine ⟨162877824651503761748489267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108585216434335841165659511 162877824651503761748489267)
      ·
        refine ⟨244316736977255642622733901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162877824651503761748489267 244316736977255642622733901)
        ·
          refine ⟨91618776366470865983525213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244316736977255642622733901 91618776366470865983525213)
          ·
            refine ⟨34357041137426574743821955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91618776366470865983525213 34357041137426574743821955)
            ·
              refine ⟨51535561706139862115732933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34357041137426574743821955 51535561706139862115732933)
              ·
                refine ⟨9662917819901224146699925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51535561706139862115732933 9662917819901224146699925)
                ·
                  refine ⟨452949272807869881876559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9662917819901224146699925 452949272807869881876559)
                  ·
                    rfl

theorem cell22_3969520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_3969520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969520 prefixEnd_3969520 := by exact prefixLift 3969520
  have htrace : WordTrace (prefixWord ++ tailWord_3969520) baseStart_3969520 baseEnd_3969520 := by
    simpa [prefixWord, tailWord_3969520, baseEnd_3969520] using wordTrace_append hprefix tailTrace_3969520
  have hstable : (prefixWord ++ tailWord_3969520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969520).length < 2 ^ (prefixWord ++ tailWord_3969520).sum := by decide
  have hdescent : baseEnd_3969520 < baseStart_3969520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969535 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_3969535 : Nat := 118140960795 + 3969535 * 2 ^ 59
def prefixEnd_3969535 : Nat := 4983230072969 + 3 ^ 40 * 3969535 * 2
def baseEnd_3969535 : Nat := 1358852953230154606504631

theorem tailTrace_3969535 : CollatzResearch.WordTrace tailWord_3969535 prefixEnd_3969535 1358852953230154606504631 := by
  unfold tailWord_3969535
  simp only [CollatzResearch.WordTrace]
  refine ⟨144780835674060112449342059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96520557116040074966228039 144780835674060112449342059)
  ·
    refine ⟨217171253511090168674013089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144780835674060112449342059 217171253511090168674013089)
    ·
      refine ⟨162878440133317626505509817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217171253511090168674013089 162878440133317626505509817)
      ·
        refine ⟨122158830099988219879132363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162878440133317626505509817 122158830099988219879132363)
        ·
          refine ⟨183238245149982329818698545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122158830099988219879132363 183238245149982329818698545)
          ·
            refine ⟨137428683862486747364023909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183238245149982329818698545 137428683862486747364023909)
            ·
              refine ⟨25767878224216265130754483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137428683862486747364023909 25767878224216265130754483)
              ·
                refine ⟨38651817336324397696131725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25767878224216265130754483 38651817336324397696131725)
                ·
                  refine ⟨14494431501121649136049397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38651817336324397696131725 14494431501121649136049397)
                  ·
                    refine ⟨1358852953230154606504631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14494431501121649136049397 1358852953230154606504631)
                    ·
                      rfl

theorem cell22_3969535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_3969535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969535 prefixEnd_3969535 := by exact prefixLift 3969535
  have htrace : WordTrace (prefixWord ++ tailWord_3969535) baseStart_3969535 baseEnd_3969535 := by
    simpa [prefixWord, tailWord_3969535, baseEnd_3969535] using wordTrace_append hprefix tailTrace_3969535
  have hstable : (prefixWord ++ tailWord_3969535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969535).length < 2 ^ (prefixWord ++ tailWord_3969535).sum := by decide
  have hdescent : baseEnd_3969535 < baseStart_3969535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969569 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 2, 3]
def baseStart_3969569 : Nat := 118140960795 + 3969569 * 2 ^ 59
def prefixEnd_3969569 : Nat := 4983230072969 + 3 ^ 40 * 3969569 * 2
def baseEnd_3969569 : Nat := 1358864592124989851154527

theorem tailTrace_3969569 : CollatzResearch.WordTrace tailWord_3969569 prefixEnd_3969569 1358864592124989851154527 := by
  unfold tailWord_3969569
  simp only [CollatzResearch.WordTrace]
  refine ⟨144782075755936936256079761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96521383837291290837386507 144782075755936936256079761)
  ·
    refine ⟨108586556816952702192059821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144782075755936936256079761 108586556816952702192059821)
    ·
      refine ⟨40719958806357263322022433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108586556816952702192059821 40719958806357263322022433)
      ·
        refine ⟨30539969104767947491516825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40719958806357263322022433 30539969104767947491516825)
        ·
          refine ⟨22904976828575960618637619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30539969104767947491516825 22904976828575960618637619)
          ·
            refine ⟨34357465242863940927956429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22904976828575960618637619 34357465242863940927956429)
            ·
              refine ⟨12884049466073977847983661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34357465242863940927956429 12884049466073977847983661)
              ·
                refine ⟨4831518549777741692993873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12884049466073977847983661 4831518549777741692993873)
                ·
                  refine ⟨3623638912333306269745405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831518549777741692993873 3623638912333306269745405)
                  ·
                    refine ⟨1358864592124989851154527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623638912333306269745405 1358864592124989851154527)
                    ·
                      rfl

theorem cell22_3969569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_3969569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969569 prefixEnd_3969569 := by exact prefixLift 3969569
  have htrace : WordTrace (prefixWord ++ tailWord_3969569) baseStart_3969569 baseEnd_3969569 := by
    simpa [prefixWord, tailWord_3969569, baseEnd_3969569] using wordTrace_append hprefix tailTrace_3969569
  have hstable : (prefixWord ++ tailWord_3969569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969569).length < 2 ^ (prefixWord ++ tailWord_3969569).sum := by decide
  have hdescent : baseEnd_3969569 < baseStart_3969569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969580 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_3969580 : Nat := 118140960795 + 3969580 * 2 ^ 59
def prefixEnd_3969580 : Nat := 4983230072969 + 3 ^ 40 * 3969580 * 2
def baseEnd_3969580 : Nat := 1358868357649789489129493

theorem tailTrace_3969580 : CollatzResearch.WordTrace tailWord_3969580 prefixEnd_3969580 1358868357649789489129493 := by
  unfold tailWord_3969580
  simp only [CollatzResearch.WordTrace]
  refine ⟨72391238479448542567365097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96521651305931390089820129 72391238479448542567365097)
  ·
    refine ⟨54293428859586406925523823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72391238479448542567365097 54293428859586406925523823)
    ·
      refine ⟨81440143289379610388285735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54293428859586406925523823 81440143289379610388285735)
      ·
        refine ⟨122160214934069415582428603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81440143289379610388285735 122160214934069415582428603)
        ·
          refine ⟨183240322401104123373642905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122160214934069415582428603 183240322401104123373642905)
          ·
            refine ⟨137430241800828092530232179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183240322401104123373642905 137430241800828092530232179)
            ·
              refine ⟨206145362701242138795348269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137430241800828092530232179 206145362701242138795348269)
              ·
                refine ⟨77304511012965802048255601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206145362701242138795348269 77304511012965802048255601)
                ·
                  refine ⟨57978383259724351536191701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77304511012965802048255601 57978383259724351536191701)
                  ·
                    refine ⟨1358868357649789489129493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57978383259724351536191701 1358868357649789489129493)
                    ·
                      rfl

theorem cell22_3969580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_3969580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969580 prefixEnd_3969580 := by exact prefixLift 3969580
  have htrace : WordTrace (prefixWord ++ tailWord_3969580) baseStart_3969580 baseEnd_3969580 := by
    simpa [prefixWord, tailWord_3969580, baseEnd_3969580] using wordTrace_append hprefix tailTrace_3969580
  have hstable : (prefixWord ++ tailWord_3969580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969580).length < 2 ^ (prefixWord ++ tailWord_3969580).sum := by decide
  have hdescent : baseEnd_3969580 < baseStart_3969580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969642 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3969642 : Nat := 118140960795 + 3969642 * 2 ^ 59
def prefixEnd_3969642 : Nat := 4983230072969 + 3 ^ 40 * 3969642 * 2
def baseEnd_3969642 : Nat := 1358889581516841994079303

theorem tailTrace_3969642 : CollatzResearch.WordTrace tailWord_3969642 prefixEnd_3969642 1358889581516841994079303 := by
  unfold tailWord_3969642
  simp only [CollatzResearch.WordTrace]
  refine ⟨36196184571168117430871795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96523158856448313148991453 36196184571168117430871795)
  ·
    refine ⟨54294276856752176146307693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36196184571168117430871795 54294276856752176146307693)
    ·
      refine ⟨20360353821282066054865385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54294276856752176146307693 20360353821282066054865385)
      ·
        refine ⟨15270265365961549541149039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20360353821282066054865385 15270265365961549541149039)
        ·
          refine ⟨22905398048942324311723559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15270265365961549541149039 22905398048942324311723559)
          ·
            refine ⟨34358097073413486467585339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905398048942324311723559 34358097073413486467585339)
            ·
              refine ⟨51537145610120229701378009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34358097073413486467585339 51537145610120229701378009)
              ·
                refine ⟨38652859207590172276033507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51537145610120229701378009 38652859207590172276033507)
                ·
                  refine ⟨57979288811385258414050261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38652859207590172276033507 57979288811385258414050261)
                  ·
                    refine ⟨1358889581516841994079303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57979288811385258414050261 1358889581516841994079303)
                    ·
                      rfl

theorem cell22_3969642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3969642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969642 prefixEnd_3969642 := by exact prefixLift 3969642
  have htrace : WordTrace (prefixWord ++ tailWord_3969642) baseStart_3969642 baseEnd_3969642 := by
    simpa [prefixWord, tailWord_3969642, baseEnd_3969642] using wordTrace_append hprefix tailTrace_3969642
  have hstable : (prefixWord ++ tailWord_3969642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969642).length < 2 ^ (prefixWord ++ tailWord_3969642).sum := by decide
  have hdescent : baseEnd_3969642 < baseStart_3969642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969648 : List Nat := [2, 1, 1, 1, 7, 1, 2, 3, 1, 3]
def baseStart_3969648 : Nat := 118140960795 + 3969648 * 2 ^ 59
def prefixEnd_3969648 : Nat := 4983230072969 + 3 ^ 40 * 3969648 * 2
def baseEnd_3969648 : Nat := 1358891635439459978429285

theorem tailTrace_3969648 : CollatzResearch.WordTrace tailWord_3969648 prefixEnd_3969648 1358891635439459978429285 := by
  unfold tailWord_3969648
  simp only [CollatzResearch.WordTrace]
  refine ⟨72392478561325366374102799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96523304748433821832137065 72392478561325366374102799)
  ·
    refine ⟨108588717841988049561154199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72392478561325366374102799 108588717841988049561154199)
    ·
      refine ⟨162883076762982074341731299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108588717841988049561154199 162883076762982074341731299)
      ·
        refine ⟨244324615144473111512596949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162883076762982074341731299 244324615144473111512596949)
        ·
          refine ⟨5726358167448588551076491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244324615144473111512596949 5726358167448588551076491)
          ·
            refine ⟨8589537251172882826614737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726358167448588551076491 8589537251172882826614737)
            ·
              refine ⟨6442152938379662119961053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8589537251172882826614737 6442152938379662119961053)
              ·
                refine ⟨2415807351892373294985395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6442152938379662119961053 2415807351892373294985395)
                ·
                  refine ⟨3623711027838559942478093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415807351892373294985395 3623711027838559942478093)
                  ·
                    refine ⟨1358891635439459978429285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623711027838559942478093 1358891635439459978429285)
                    ·
                      rfl

theorem cell22_3969648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_3969648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969648 prefixEnd_3969648 := by exact prefixLift 3969648
  have htrace : WordTrace (prefixWord ++ tailWord_3969648) baseStart_3969648 baseEnd_3969648 := by
    simpa [prefixWord, tailWord_3969648, baseEnd_3969648] using wordTrace_append hprefix tailTrace_3969648
  have hstable : (prefixWord ++ tailWord_3969648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969648).length < 2 ^ (prefixWord ++ tailWord_3969648).sum := by decide
  have hdescent : baseEnd_3969648 < baseStart_3969648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969661 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 5]
def baseStart_3969661 : Nat := 118140960795 + 3969661 * 2 ^ 59
def prefixEnd_3969661 : Nat := 4983230072969 + 3 ^ 40 * 3969661 * 2
def baseEnd_3969661 : Nat := 452965361868377425951415

theorem tailTrace_3969661 : CollatzResearch.WordTrace tailWord_3969661 prefixEnd_3969661 452965361868377425951415 := by
  unfold tailWord_3969661
  simp only [CollatzResearch.WordTrace]
  refine ⟨144785431271603635968428837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96523620847735757312285891 144785431271603635968428837)
  ·
    refine ⟨27147268363425681744080407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144785431271603635968428837 27147268363425681744080407)
    ·
      refine ⟨40720902545138522616120611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27147268363425681744080407 40720902545138522616120611)
      ·
        refine ⟨61081353817707783924180917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40720902545138522616120611 61081353817707783924180917)
        ·
          refine ⟨5726376920410104742891961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61081353817707783924180917 5726376920410104742891961)
          ·
            refine ⟨4294782690307578557168971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5726376920410104742891961 4294782690307578557168971)
            ·
              refine ⟨6442174035461367835753457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294782690307578557168971 6442174035461367835753457)
              ·
                refine ⟨4831630526596025876815093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442174035461367835753457 4831630526596025876815093)
                ·
                  refine ⟨452965361868377425951415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4831630526596025876815093 452965361868377425951415)
                  ·
                    rfl

theorem cell22_3969661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_3969661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969661 prefixEnd_3969661 := by exact prefixLift 3969661
  have htrace : WordTrace (prefixWord ++ tailWord_3969661) baseStart_3969661 baseEnd_3969661 := by
    simpa [prefixWord, tailWord_3969661, baseEnd_3969661] using wordTrace_append hprefix tailTrace_3969661
  have hstable : (prefixWord ++ tailWord_3969661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969661).length < 2 ^ (prefixWord ++ tailWord_3969661).sum := by decide
  have hdescent : baseEnd_3969661 < baseStart_3969661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969738 : List Nat := [3, 1, 2, 1, 4, 1, 4, 1, 2, 3]
def baseStart_3969738 : Nat := 118140960795 + 3969738 * 2 ^ 59
def prefixEnd_3969738 : Nat := 4983230072969 + 3 ^ 40 * 3969738 * 2
def baseEnd_3969738 : Nat := 1358922444278729743679009

theorem tailTrace_3969738 : CollatzResearch.WordTrace tailWord_3969738 prefixEnd_3969738 1358922444278729743679009 := by
  unfold tailWord_3969738
  simp only [CollatzResearch.WordTrace]
  refine ⟨36197059923081169529745467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96525493128216452079321245 36197059923081169529745467)
  ·
    refine ⟨54295589884621754294618201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36197059923081169529745467 54295589884621754294618201)
    ·
      refine ⟨40721692413466315720963651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54295589884621754294618201 40721692413466315720963651)
      ·
        refine ⟨61082538620199473581445477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40721692413466315720963651 61082538620199473581445477)
        ·
          refine ⟨11452975991287401296521027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61082538620199473581445477 11452975991287401296521027)
          ·
            refine ⟨17179463986931101944781541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452975991287401296521027 17179463986931101944781541)
            ·
              refine ⟨3221149497549581614646539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17179463986931101944781541 3221149497549581614646539)
              ·
                refine ⟨4831724246324372421969809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221149497549581614646539 4831724246324372421969809)
                ·
                  refine ⟨3623793184743279316477357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831724246324372421969809 3623793184743279316477357)
                  ·
                    refine ⟨1358922444278729743679009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623793184743279316477357 1358922444278729743679009)
                    ·
                      rfl

theorem cell22_3969738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_3969738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969738 prefixEnd_3969738 := by exact prefixLift 3969738
  have htrace : WordTrace (prefixWord ++ tailWord_3969738) baseStart_3969738 baseEnd_3969738 := by
    simpa [prefixWord, tailWord_3969738, baseEnd_3969738] using wordTrace_append hprefix tailTrace_3969738
  have hstable : (prefixWord ++ tailWord_3969738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969738).length < 2 ^ (prefixWord ++ tailWord_3969738).sum := by decide
  have hdescent : baseEnd_3969738 < baseStart_3969738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969792 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_3969792 : Nat := 118140960795 + 3969792 * 2 ^ 59
def prefixEnd_3969792 : Nat := 4983230072969 + 3 ^ 40 * 3969792 * 2
def baseEnd_3969792 : Nat := 1358940929582291602828843

theorem tailTrace_3969792 : CollatzResearch.WordTrace tailWord_3969792 prefixEnd_3969792 1358940929582291602828843 := by
  unfold tailWord_3969792
  simp only [CollatzResearch.WordTrace]
  refine ⟨72395104617064522670723815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96526806156086030227631753 72395104617064522670723815)
  ·
    refine ⟨108592656925596784006085723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72395104617064522670723815 108592656925596784006085723)
    ·
      refine ⟨162888985388395176009128585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108592656925596784006085723 162888985388395176009128585)
      ·
        refine ⟨122166739041296382006846439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162888985388395176009128585 122166739041296382006846439)
        ·
          refine ⟨183250108561944573010269659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122166739041296382006846439 183250108561944573010269659)
          ·
            refine ⟨274875162842916859515404489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183250108561944573010269659 274875162842916859515404489)
            ·
              refine ⟨206156372132187644636553367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274875162842916859515404489 206156372132187644636553367)
              ·
                refine ⟨309234558198281466954830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206156372132187644636553367 309234558198281466954830051)
                ·
                  refine ⟨463851837297422200432245077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309234558198281466954830051 463851837297422200432245077)
                  ·
                    refine ⟨1358940929582291602828843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 463851837297422200432245077 1358940929582291602828843)
                    ·
                      rfl

theorem cell22_3969792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_3969792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969792 prefixEnd_3969792 := by exact prefixLift 3969792
  have htrace : WordTrace (prefixWord ++ tailWord_3969792) baseStart_3969792 baseEnd_3969792 := by
    simpa [prefixWord, tailWord_3969792, baseEnd_3969792] using wordTrace_append hprefix tailTrace_3969792
  have hstable : (prefixWord ++ tailWord_3969792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969792).length < 2 ^ (prefixWord ++ tailWord_3969792).sum := by decide
  have hdescent : baseEnd_3969792 < baseStart_3969792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969809 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 3, 4]
def baseStart_3969809 : Nat := 118140960795 + 3969809 * 2 ^ 59
def prefixEnd_3969809 : Nat := 4983230072969 + 3 ^ 40 * 3969809 * 2
def baseEnd_3969809 : Nat := 1358946749029709225153791

theorem tailTrace_3969809 : CollatzResearch.WordTrace tailWord_3969809 prefixEnd_3969809 1358946749029709225153791 := by
  unfold tailWord_3969809
  simp only [CollatzResearch.WordTrace]
  refine ⟨144790829275067457244816481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96527219516711638163210987 144790829275067457244816481)
  ·
    refine ⟨108593121956300592933612361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144790829275067457244816481 108593121956300592933612361)
    ·
      refine ⟨81444841467225444700209271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108593121956300592933612361 81444841467225444700209271)
      ·
        refine ⟨122167262200838167050313907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81444841467225444700209271 122167262200838167050313907)
        ·
          refine ⟨183250893301257250575470861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122167262200838167050313907 183250893301257250575470861)
          ·
            refine ⟨68719084987971468965801573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183250893301257250575470861 68719084987971468965801573)
            ·
              refine ⟨12884828435244650431087795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68719084987971468965801573 12884828435244650431087795)
              ·
                refine ⟨19327242652866975646631693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12884828435244650431087795 19327242652866975646631693)
                ·
                  refine ⟨7247715994825115867486885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19327242652866975646631693 7247715994825115867486885)
                  ·
                    refine ⟨1358946749029709225153791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7247715994825115867486885 1358946749029709225153791)
                    ·
                      rfl

theorem cell22_3969809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_3969809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969809 prefixEnd_3969809 := by exact prefixLift 3969809
  have htrace : WordTrace (prefixWord ++ tailWord_3969809) baseStart_3969809 baseEnd_3969809 := by
    simpa [prefixWord, tailWord_3969809, baseEnd_3969809] using wordTrace_append hprefix tailTrace_3969809
  have hstable : (prefixWord ++ tailWord_3969809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969809).length < 2 ^ (prefixWord ++ tailWord_3969809).sum := by decide
  have hdescent : baseEnd_3969809 < baseStart_3969809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969841 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 4]
def baseStart_3969841 : Nat := 118140960795 + 3969841 * 2 ^ 59
def prefixEnd_3969841 : Nat := 4983230072969 + 3 ^ 40 * 3969841 * 2
def baseEnd_3969841 : Nat := 452985901094557269451231

theorem tailTrace_3969841 : CollatzResearch.WordTrace tailWord_3969841 prefixEnd_3969841 452985901094557269451231 := by
  unfold tailWord_3969841
  simp only [CollatzResearch.WordTrace]
  refine ⟨144791996410951526709981377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96527997607301017806654251 144791996410951526709981377)
  ·
    refine ⟨108593997308213645032486033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144791996410951526709981377 108593997308213645032486033)
    ·
      refine ⟨81445497981160233774364525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108593997308213645032486033 81445497981160233774364525)
      ·
        refine ⟨30542061742935087665386697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81445497981160233774364525 30542061742935087665386697)
        ·
          refine ⟨22906546307201315749040023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30542061742935087665386697 22906546307201315749040023)
          ·
            refine ⟨34359819460801973623560035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22906546307201315749040023 34359819460801973623560035)
            ·
              refine ⟨51539729191202960435340053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34359819460801973623560035 51539729191202960435340053)
              ·
                refine ⟨2415924805837638770406565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51539729191202960435340053 2415924805837638770406565)
                ·
                  refine ⟨452985901094557269451231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415924805837638770406565 452985901094557269451231)
                  ·
                    rfl

theorem cell22_3969841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_3969841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969841 prefixEnd_3969841 := by exact prefixLift 3969841
  have htrace : WordTrace (prefixWord ++ tailWord_3969841) baseStart_3969841 baseEnd_3969841 := by
    simpa [prefixWord, tailWord_3969841, baseEnd_3969841] using wordTrace_append hprefix tailTrace_3969841
  have hstable : (prefixWord ++ tailWord_3969841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969841).length < 2 ^ (prefixWord ++ tailWord_3969841).sum := by decide
  have hdescent : baseEnd_3969841 < baseStart_3969841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969856 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 2, 3]
def baseStart_3969856 : Nat := 118140960795 + 3969856 * 2 ^ 59
def prefixEnd_3969856 : Nat := 4983230072969 + 3 ^ 40 * 3969856 * 2
def baseEnd_3969856 : Nat := 1358962838090216769228647

theorem tailTrace_3969856 : CollatzResearch.WordTrace tailWord_3969856 prefixEnd_3969856 1358962838090216769228647 := by
  unfold tailWord_3969856
  simp only [CollatzResearch.WordTrace]
  refine ⟨72396271752948592135888711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96528362337264789514518281 72396271752948592135888711)
  ·
    refine ⟨108594407629422888203833067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72396271752948592135888711 108594407629422888203833067)
    ·
      refine ⟨162891611444134332305749601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108594407629422888203833067 162891611444134332305749601)
      ·
        refine ⟨122168708583100749229312201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162891611444134332305749601 122168708583100749229312201)
        ·
          refine ⟨91626531437325561921984151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122168708583100749229312201 91626531437325561921984151)
          ·
            refine ⟨137439797155988342882976227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91626531437325561921984151 137439797155988342882976227)
            ·
              refine ⟨206159695733982514324464341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137439797155988342882976227 206159695733982514324464341)
              ·
                refine ⟨4831867868765215179479633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206159695733982514324464341 4831867868765215179479633)
                ·
                  refine ⟨3623900901573911384609725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4831867868765215179479633 3623900901573911384609725)
                  ·
                    refine ⟨1358962838090216769228647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3623900901573911384609725 1358962838090216769228647)
                    ·
                      rfl

theorem cell22_3969856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_3969856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969856 prefixEnd_3969856 := by exact prefixLift 3969856
  have htrace : WordTrace (prefixWord ++ tailWord_3969856) baseStart_3969856 baseEnd_3969856 := by
    simpa [prefixWord, tailWord_3969856, baseEnd_3969856] using wordTrace_append hprefix tailTrace_3969856
  have hstable : (prefixWord ++ tailWord_3969856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969856).length < 2 ^ (prefixWord ++ tailWord_3969856).sum := by decide
  have hdescent : baseEnd_3969856 < baseStart_3969856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969922 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3969922 : Nat := 118140960795 + 3969922 * 2 ^ 59
def prefixEnd_3969922 : Nat := 4983230072969 + 3 ^ 40 * 3969922 * 2
def baseEnd_3969922 : Nat := 1358985431239014597078445

theorem tailTrace_3969922 : CollatzResearch.WordTrace tailWord_3969922 prefixEnd_3969922 1358985431239014597078445 := by
  unfold tailWord_3969922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198737680914519385920005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96529967149105385029120013 36198737680914519385920005)
  ·
    refine ⟨6787263315171472384860001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36198737680914519385920005 6787263315171472384860001)
    ·
      refine ⟨5090447486378604288645001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6787263315171472384860001 5090447486378604288645001)
      ·
        refine ⟨3817835614783953216483751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5090447486378604288645001 3817835614783953216483751)
        ·
          refine ⟨5726753422175929824725627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3817835614783953216483751 5726753422175929824725627)
          ·
            refine ⟨8590130133263894737088441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726753422175929824725627 8590130133263894737088441)
            ·
              refine ⟨6442597599947921052816331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590130133263894737088441 6442597599947921052816331)
              ·
                refine ⟨9663896399921881579224497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442597599947921052816331 9663896399921881579224497)
                ·
                  refine ⟨7247922299941411184418373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9663896399921881579224497 7247922299941411184418373)
                  ·
                    refine ⟨1358985431239014597078445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7247922299941411184418373 1358985431239014597078445)
                    ·
                      rfl

theorem cell22_3969922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3969922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969922 prefixEnd_3969922 := by exact prefixLift 3969922
  have htrace : WordTrace (prefixWord ++ tailWord_3969922) baseStart_3969922 baseEnd_3969922 := by
    simpa [prefixWord, tailWord_3969922, baseEnd_3969922] using wordTrace_append hprefix tailTrace_3969922
  have hstable : (prefixWord ++ tailWord_3969922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969922).length < 2 ^ (prefixWord ++ tailWord_3969922).sum := by decide
  have hdescent : baseEnd_3969922 < baseStart_3969922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969976 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_3969976 : Nat := 118140960795 + 3969976 * 2 ^ 59
def prefixEnd_3969976 : Nat := 4983230072969 + 3 ^ 40 * 3969976 * 2
def baseEnd_3969976 : Nat := 453001305514192152076093

theorem tailTrace_3969976 : CollatzResearch.WordTrace tailWord_3969976 prefixEnd_3969976 453001305514192152076093 := by
  unfold tailWord_3969976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72398460132731222383072891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96531280176974963177430521 72398460132731222383072891)
  ·
    refine ⟨108597690199096833574609337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72398460132731222383072891 108597690199096833574609337)
    ·
      refine ⟨81448267649322625180957003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108597690199096833574609337 81448267649322625180957003)
      ·
        refine ⟨122172401473983937771435505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81448267649322625180957003 122172401473983937771435505)
        ·
          refine ⟨91629301105487953328576629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122172401473983937771435505 91629301105487953328576629)
          ·
            refine ⟨8590246978639495624554059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91629301105487953328576629 8590246978639495624554059)
            ·
              refine ⟨12885370467959243436831089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590246978639495624554059 12885370467959243436831089)
              ·
                refine ⟨9664027850969432577623317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12885370467959243436831089 9664027850969432577623317)
                ·
                  refine ⟨453001305514192152076093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9664027850969432577623317 453001305514192152076093)
                  ·
                    rfl

theorem cell22_3969976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_3969976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969976 prefixEnd_3969976 := by exact prefixLift 3969976
  have htrace : WordTrace (prefixWord ++ tailWord_3969976) baseStart_3969976 baseEnd_3969976 := by
    simpa [prefixWord, tailWord_3969976, baseEnd_3969976] using wordTrace_append hprefix tailTrace_3969976
  have hstable : (prefixWord ++ tailWord_3969976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969976).length < 2 ^ (prefixWord ++ tailWord_3969976).sum := by decide
  have hdescent : baseEnd_3969976 < baseStart_3969976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969991 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3969991 : Nat := 118140960795 + 3969991 * 2 ^ 59
def prefixEnd_3969991 : Nat := 4983230072969 + 3 ^ 40 * 3969991 * 2
def baseEnd_3969991 : Nat := 1359009051349121417103233

theorem tailTrace_3969991 : CollatzResearch.WordTrace tailWord_3969991 prefixEnd_3969991 1359009051349121417103233 := by
  unfold tailWord_3969991
  simp only [CollatzResearch.WordTrace]
  refine ⟨144797467360408102327941827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96531644906938734885294551 144797467360408102327941827)
  ·
    refine ⟨217196201040612153491912741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144797467360408102327941827 217196201040612153491912741)
    ·
      refine ⟨40724287695114778779733639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217196201040612153491912741 40724287695114778779733639)
      ·
        refine ⟨61086431542672168169600459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40724287695114778779733639 61086431542672168169600459)
        ·
          refine ⟨91629647314008252254400689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61086431542672168169600459 91629647314008252254400689)
          ·
            refine ⟨68722235485506189190800517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91629647314008252254400689 68722235485506189190800517)
            ·
              refine ⟨12885419153532410473275097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68722235485506189190800517 12885419153532410473275097)
              ·
                refine ⟨9664064365149307854956323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12885419153532410473275097 9664064365149307854956323)
                ·
                  refine ⟨14496096547723961782434485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664064365149307854956323 14496096547723961782434485)
                  ·
                    refine ⟨1359009051349121417103233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14496096547723961782434485 1359009051349121417103233)
                    ·
                      rfl

theorem cell22_3969991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3969991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969991 prefixEnd_3969991 := by exact prefixLift 3969991
  have htrace : WordTrace (prefixWord ++ tailWord_3969991) baseStart_3969991 baseEnd_3969991 := by
    simpa [prefixWord, tailWord_3969991, baseEnd_3969991] using wordTrace_append hprefix tailTrace_3969991
  have hstable : (prefixWord ++ tailWord_3969991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969991).length < 2 ^ (prefixWord ++ tailWord_3969991).sum := by decide
  have hdescent : baseEnd_3969991 < baseStart_3969991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3969995 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 1, 4]
def baseStart_3969995 : Nat := 118140960795 + 3969995 * 2 ^ 59
def prefixEnd_3969995 : Nat := 4983230072969 + 3 ^ 40 * 3969995 * 2
def baseEnd_3969995 : Nat := 1359010420630866740003221

theorem tailTrace_3969995 : CollatzResearch.WordTrace tailWord_3969995 prefixEnd_3969995 1359010420630866740003221 := by
  unfold tailWord_3969995
  simp only [CollatzResearch.WordTrace]
  refine ⟨144797613252393611011087439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96531742168262407340724959 144797613252393611011087439)
  ·
    refine ⟨217196419878590416516631159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144797613252393611011087439 217196419878590416516631159)
    ·
      refine ⟨325794629817885624774946739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217196419878590416516631159 325794629817885624774946739)
      ·
        refine ⟨488691944726828437162420109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325794629817885624774946739 488691944726828437162420109)
        ·
          refine ⟨183259479272560663935907541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 488691944726828437162420109 183259479272560663935907541)
          ·
            refine ⟨4295144045450640560997833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 183259479272560663935907541 4295144045450640560997833)
            ·
              refine ⟨3221358034087980420748375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295144045450640560997833 3221358034087980420748375)
              ·
                refine ⟨4832037051131970631122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221358034087980420748375 4832037051131970631122563)
                ·
                  refine ⟨7248055576697955946683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832037051131970631122563 7248055576697955946683845)
                  ·
                    refine ⟨1359010420630866740003221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7248055576697955946683845 1359010420630866740003221)
                    ·
                      rfl

theorem cell22_3969995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 4].length) (baseStart_3969995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3969995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3969995 prefixEnd_3969995 := by exact prefixLift 3969995
  have htrace : WordTrace (prefixWord ++ tailWord_3969995) baseStart_3969995 baseEnd_3969995 := by
    simpa [prefixWord, tailWord_3969995, baseEnd_3969995] using wordTrace_append hprefix tailTrace_3969995
  have hstable : (prefixWord ++ tailWord_3969995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3969995).length < 2 ^ (prefixWord ++ tailWord_3969995).sum := by decide
  have hdescent : baseEnd_3969995 < baseStart_3969995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3969995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970008 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 4, 3]
def baseStart_3970008 : Nat := 118140960795 + 3970008 * 2 ^ 59
def prefixEnd_3970008 : Nat := 4983230072969 + 3 ^ 40 * 3970008 * 2
def baseEnd_3970008 : Nat := 1359014870796539039428181

theorem tailTrace_3970008 : CollatzResearch.WordTrace tailWord_3970008 prefixEnd_3970008 1359014870796539039428181 := by
  unfold tailWord_3970008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72399043700673257115655339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96532058267564342820873785 72399043700673257115655339)
  ·
    refine ⟨108598565551009885673483009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72399043700673257115655339 108598565551009885673483009)
    ·
      refine ⟨81448924163257414255112257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108598565551009885673483009 81448924163257414255112257)
      ·
        refine ⟨61086693122443060691334193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81448924163257414255112257 61086693122443060691334193)
        ·
          refine ⟨45815019841832295518500645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61086693122443060691334193 45815019841832295518500645)
          ·
            refine ⟨8590316220343555409718871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45815019841832295518500645 8590316220343555409718871)
            ·
              refine ⟨12885474330515333114578307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590316220343555409718871 12885474330515333114578307)
              ·
                refine ⟨19328211495772999671867461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12885474330515333114578307 19328211495772999671867461)
                ·
                  refine ⟨3624039655457437438475149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19328211495772999671867461 3624039655457437438475149)
                  ·
                    refine ⟨1359014870796539039428181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624039655457437438475149 1359014870796539039428181)
                    ·
                      rfl

theorem cell22_3970008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_3970008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970008 prefixEnd_3970008 := by exact prefixLift 3970008
  have htrace : WordTrace (prefixWord ++ tailWord_3970008) baseStart_3970008 baseEnd_3970008 := by
    simpa [prefixWord, tailWord_3970008, baseEnd_3970008] using wordTrace_append hprefix tailTrace_3970008
  have hstable : (prefixWord ++ tailWord_3970008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970008).length < 2 ^ (prefixWord ++ tailWord_3970008).sum := by decide
  have hdescent : baseEnd_3970008 < baseStart_3970008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970038 : List Nat := [5, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3970038 : Nat := 118140960795 + 3970038 * 2 ^ 59
def prefixEnd_3970038 : Nat := 4983230072969 + 3 ^ 40 * 3970038 * 2
def baseEnd_3970038 : Nat := 151002793378847662353121

theorem tailTrace_3970038 : CollatzResearch.WordTrace tailWord_3970038 prefixEnd_3970038 151002793378847662353121 := by
  unfold tailWord_3970038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049948849452364334681423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96532787727491886236601845 9049948849452364334681423)
  ·
    refine ⟨13574923274178546502022135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049948849452364334681423 13574923274178546502022135)
    ·
      refine ⟨20362384911267819753033203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13574923274178546502022135 20362384911267819753033203)
      ·
        refine ⟨30543577366901729629549805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20362384911267819753033203 30543577366901729629549805)
        ·
          refine ⟨11453841512588148611081177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30543577366901729629549805 11453841512588148611081177)
          ·
            refine ⟨8590381134441111458310883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11453841512588148611081177 8590381134441111458310883)
            ·
              refine ⟨12885571701661667187466325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590381134441111458310883 12885571701661667187466325)
              ·
                refine ⟨151002793378847662353121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12885571701661667187466325 151002793378847662353121)
                ·
                  rfl

theorem cell22_3970038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3970038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970038 prefixEnd_3970038 := by exact prefixLift 3970038
  have htrace : WordTrace (prefixWord ++ tailWord_3970038) baseStart_3970038 baseEnd_3970038 := by
    simpa [prefixWord, tailWord_3970038, baseEnd_3970038] using wordTrace_append hprefix tailTrace_3970038
  have hstable : (prefixWord ++ tailWord_3970038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970038).length < 2 ^ (prefixWord ++ tailWord_3970038).sum := by decide
  have hdescent : baseEnd_3970038 < baseStart_3970038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970083 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 5]
def baseStart_3970083 : Nat := 118140960795 + 3970083 * 2 ^ 59
def prefixEnd_3970083 : Nat := 4983230072969 + 3 ^ 40 * 3970083 * 2
def baseEnd_3970083 : Nat := 453013514943087947934317

theorem tailTrace_3970083 : CollatzResearch.WordTrace tailWord_3970083 prefixEnd_3970083 453013514943087947934317 := by
  unfold tailWord_3970083
  simp only [CollatzResearch.WordTrace]
  refine ⟨144800822876074802040290903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96533881917383201360193935 144800822876074802040290903)
  ·
    refine ⟨217201234314112203060436355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144800822876074802040290903 217201234314112203060436355)
    ·
      refine ⟨325801851471168304590654533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217201234314112203060436355 325801851471168304590654533)
      ·
        refine ⟨61087847150844057110747725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325801851471168304590654533 61087847150844057110747725)
        ·
          refine ⟨22907942681566521416530397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61087847150844057110747725 22907942681566521416530397)
          ·
            refine ⟨8590478505587445531198899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22907942681566521416530397 8590478505587445531198899)
            ·
              refine ⟨12885717758381168296798349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590478505587445531198899 12885717758381168296798349)
              ·
                refine ⟨4832144159392938111299381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12885717758381168296798349 4832144159392938111299381)
                ·
                  refine ⟨453013514943087947934317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832144159392938111299381 453013514943087947934317)
                  ·
                    rfl

theorem cell22_3970083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 5].length) (baseStart_3970083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970083 prefixEnd_3970083 := by exact prefixLift 3970083
  have htrace : WordTrace (prefixWord ++ tailWord_3970083) baseStart_3970083 baseEnd_3970083 := by
    simpa [prefixWord, tailWord_3970083, baseEnd_3970083] using wordTrace_append hprefix tailTrace_3970083
  have hstable : (prefixWord ++ tailWord_3970083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970083).length < 2 ^ (prefixWord ++ tailWord_3970083).sum := by decide
  have hdescent : baseEnd_3970083 < baseStart_3970083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970143 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 1, 5]
def baseStart_3970143 : Nat := 118140960795 + 3970143 * 2 ^ 59
def prefixEnd_3970143 : Nat := 4983230072969 + 3 ^ 40 * 3970143 * 2
def baseEnd_3970143 : Nat := 1359061084055443687302767

theorem tailTrace_3970143 : CollatzResearch.WordTrace tailWord_3970143 prefixEnd_3970143 1359061084055443687302767 := by
  unfold tailWord_3970143
  simp only [CollatzResearch.WordTrace]
  refine ⟨144803011255857432287475083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96535340837238288191650055 144803011255857432287475083)
  ·
    refine ⟨217204516883786148431212625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144803011255857432287475083 217204516883786148431212625)
    ·
      refine ⟨162903387662839611323409469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217204516883786148431212625 162903387662839611323409469)
      ·
        refine ⟨61088770373564854246278551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162903387662839611323409469 61088770373564854246278551)
        ·
          refine ⟨91633155560347281369417827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61088770373564854246278551 91633155560347281369417827)
          ·
            refine ⟨137449733340520922054126741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91633155560347281369417827 137449733340520922054126741)
            ·
              refine ⟨6442956250336918221287191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137449733340520922054126741 6442956250336918221287191)
              ·
                refine ⟨9664434375505377331930787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6442956250336918221287191 9664434375505377331930787)
                ·
                  refine ⟨14496651563258065997896181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664434375505377331930787 14496651563258065997896181)
                  ·
                    refine ⟨1359061084055443687302767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14496651563258065997896181 1359061084055443687302767)
                    ·
                      rfl

theorem cell22_3970143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_3970143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970143 prefixEnd_3970143 := by exact prefixLift 3970143
  have htrace : WordTrace (prefixWord ++ tailWord_3970143) baseStart_3970143 baseEnd_3970143 := by
    simpa [prefixWord, tailWord_3970143, baseEnd_3970143] using wordTrace_append hprefix tailTrace_3970143
  have hstable : (prefixWord ++ tailWord_3970143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970143).length < 2 ^ (prefixWord ++ tailWord_3970143).sum := by decide
  have hdescent : baseEnd_3970143 < baseStart_3970143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970171 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_3970171 : Nat := 118140960795 + 3970171 * 2 ^ 59
def prefixEnd_3970171 : Nat := 4983230072969 + 3 ^ 40 * 3970171 * 2
def baseEnd_3970171 : Nat := 1359070669027660947602681

theorem tailTrace_3970171 : CollatzResearch.WordTrace tailWord_3970171 prefixEnd_3970171 1359070669027660947602681 := by
  unfold tailWord_3970171
  simp only [CollatzResearch.WordTrace]
  refine ⟨144804032499755993069494367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96536021666503995379662911 144804032499755993069494367)
  ·
    refine ⟨217206048749633989604241551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144804032499755993069494367 217206048749633989604241551)
    ·
      refine ⟨325809073124450984406362327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217206048749633989604241551 325809073124450984406362327)
      ·
        refine ⟨488713609686676476609543491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325809073124450984406362327 488713609686676476609543491)
        ·
          refine ⟨733070414530014714914315237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488713609686676476609543491 733070414530014714914315237)
          ·
            refine ⟨137450702724377759046434107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 733070414530014714914315237 137450702724377759046434107)
            ·
              refine ⟨206176054086566638569651161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137450702724377759046434107 206176054086566638569651161)
              ·
                refine ⟨154632040564924978927238371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206176054086566638569651161 154632040564924978927238371)
                ·
                  refine ⟨231948060847387468390857557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154632040564924978927238371 231948060847387468390857557)
                  ·
                    refine ⟨1359070669027660947602681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 231948060847387468390857557 1359070669027660947602681)
                    ·
                      rfl

theorem cell22_3970171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_3970171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970171 prefixEnd_3970171 := by exact prefixLift 3970171
  have htrace : WordTrace (prefixWord ++ tailWord_3970171) baseStart_3970171 baseEnd_3970171 := by
    simpa [prefixWord, tailWord_3970171, baseEnd_3970171] using wordTrace_append hprefix tailTrace_3970171
  have hstable : (prefixWord ++ tailWord_3970171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970171).length < 2 ^ (prefixWord ++ tailWord_3970171).sum := by decide
  have hdescent : baseEnd_3970171 < baseStart_3970171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970177 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3970177 : Nat := 118140960795 + 3970177 * 2 ^ 59
def prefixEnd_3970177 : Nat := 4983230072969 + 3 ^ 40 * 3970177 * 2
def baseEnd_3970177 : Nat := 1359072722950278931952663

theorem tailTrace_3970177 : CollatzResearch.WordTrace tailWord_3970177 prefixEnd_3970177 1359072722950278931952663 := by
  unfold tailWord_3970177
  simp only [CollatzResearch.WordTrace]
  refine ⟨144804251337734256094212785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96536167558489504062808523 144804251337734256094212785)
  ·
    refine ⟨108603188503300692070659589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144804251337734256094212785 108603188503300692070659589)
    ·
      refine ⟨20363097844368879763248673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108603188503300692070659589 20363097844368879763248673)
      ·
        refine ⟨15272323383276659822436505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20363097844368879763248673 15272323383276659822436505)
        ·
          refine ⟨11454242537457494866827379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15272323383276659822436505 11454242537457494866827379)
          ·
            refine ⟨17181363806186242300241069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11454242537457494866827379 17181363806186242300241069)
            ·
              refine ⟨6443011427319840862590401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17181363806186242300241069 6443011427319840862590401)
              ·
                refine ⟨4832258570489880646942801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443011427319840862590401 4832258570489880646942801)
                ·
                  refine ⟨3624193927867410485207101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832258570489880646942801 3624193927867410485207101)
                  ·
                    refine ⟨1359072722950278931952663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624193927867410485207101 1359072722950278931952663)
                    ·
                      rfl

theorem cell22_3970177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3970177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970177 prefixEnd_3970177 := by exact prefixLift 3970177
  have htrace : WordTrace (prefixWord ++ tailWord_3970177) baseStart_3970177 baseEnd_3970177 := by
    simpa [prefixWord, tailWord_3970177, baseEnd_3970177] using wordTrace_append hprefix tailTrace_3970177
  have hstable : (prefixWord ++ tailWord_3970177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970177).length < 2 ^ (prefixWord ++ tailWord_3970177).sum := by decide
  have hdescent : baseEnd_3970177 < baseStart_3970177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970194 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3970194 : Nat := 118140960795 + 3970194 * 2 ^ 59
def prefixEnd_3970194 : Nat := 4983230072969 + 3 ^ 40 * 3970194 * 2
def baseEnd_3970194 : Nat := 1359078542397696554277611

theorem tailTrace_3970194 : CollatzResearch.WordTrace tailWord_3970194 prefixEnd_3970194 1359078542397696554277611 := by
  unfold tailWord_3970194
  simp only [CollatzResearch.WordTrace]
  refine ⟨36201217844668166999395409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96536580919115111998387757 36201217844668166999395409)
  ·
    refine ⟨27150913383501125249546557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36201217844668166999395409 27150913383501125249546557)
    ·
      refine ⟨10181592518812921968579959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27150913383501125249546557 10181592518812921968579959)
      ·
        refine ⟨15272388778219382952869939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181592518812921968579959 15272388778219382952869939)
        ·
          refine ⟨22908583167329074429304909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15272388778219382952869939 22908583167329074429304909)
          ·
            refine ⟨8590718687748402910989341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22908583167329074429304909 8590718687748402910989341)
            ·
              refine ⟨3221519507905651091621003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8590718687748402910989341 3221519507905651091621003)
              ·
                refine ⟨4832279261858476637431505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221519507905651091621003 4832279261858476637431505)
                ·
                  refine ⟨3624209446393857478073629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832279261858476637431505 3624209446393857478073629)
                  ·
                    refine ⟨1359078542397696554277611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624209446393857478073629 1359078542397696554277611)
                    ·
                      rfl

theorem cell22_3970194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3970194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970194 prefixEnd_3970194 := by exact prefixLift 3970194
  have htrace : WordTrace (prefixWord ++ tailWord_3970194) baseStart_3970194 baseEnd_3970194 := by
    simpa [prefixWord, tailWord_3970194, baseEnd_3970194] using wordTrace_append hprefix tailTrace_3970194
  have hstable : (prefixWord ++ tailWord_3970194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970194).length < 2 ^ (prefixWord ++ tailWord_3970194).sum := by decide
  have hdescent : baseEnd_3970194 < baseStart_3970194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970205 : List Nat := [1, 4, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3970205 : Nat := 118140960795 + 3970205 * 2 ^ 59
def prefixEnd_3970205 : Nat := 4983230072969 + 3 ^ 40 * 3970205 * 2
def baseEnd_3970205 : Nat := 1359082307922496192252577

theorem tailTrace_3970205 : CollatzResearch.WordTrace tailWord_3970205 prefixEnd_3970205 1359082307922496192252577 := by
  unfold tailWord_3970205
  simp only [CollatzResearch.WordTrace]
  refine ⟨144805272581632816876232069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96536848387755211250821379 144805272581632816876232069)
  ·
    refine ⟨27150988609056153164293513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144805272581632816876232069 27150988609056153164293513)
    ·
      refine ⟨20363241456792114873220135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27150988609056153164293513 20363241456792114873220135)
      ·
        refine ⟨30544862185188172309830203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20363241456792114873220135 30544862185188172309830203)
        ·
          refine ⟨45817293277782258464745305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30544862185188172309830203 45817293277782258464745305)
          ·
            refine ⟨34362969958336693848558979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45817293277782258464745305 34362969958336693848558979)
            ·
              refine ⟨51544454937505040772838469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34362969958336693848558979 51544454937505040772838469)
              ·
                refine ⟨9664585300782195144907213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51544454937505040772838469 9664585300782195144907213)
                ·
                  refine ⟨3624219487793323179340205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9664585300782195144907213 3624219487793323179340205)
                  ·
                    refine ⟨1359082307922496192252577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624219487793323179340205 1359082307922496192252577)
                    ·
                      rfl

theorem cell22_3970205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3970205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970205 prefixEnd_3970205 := by exact prefixLift 3970205
  have htrace : WordTrace (prefixWord ++ tailWord_3970205) baseStart_3970205 baseEnd_3970205 := by
    simpa [prefixWord, tailWord_3970205, baseEnd_3970205] using wordTrace_append hprefix tailTrace_3970205
  have hstable : (prefixWord ++ tailWord_3970205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970205).length < 2 ^ (prefixWord ++ tailWord_3970205).sum := by decide
  have hdescent : baseEnd_3970205 < baseStart_3970205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970207 : List Nat := [1, 1, 2, 6, 2, 2, 2, 6]
def baseStart_3970207 : Nat := 118140960795 + 3970207 * 2 ^ 59
def prefixEnd_3970207 : Nat := 4983230072969 + 3 ^ 40 * 3970207 * 2
def baseEnd_3970207 : Nat := 151009221395929872633619

theorem tailTrace_3970207 : CollatzResearch.WordTrace tailWord_3970207 prefixEnd_3970207 151009221395929872633619 := by
  unfold tailWord_3970207
  simp only [CollatzResearch.WordTrace]
  refine ⟨144805345527625571217804875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96536897018417047478536583 144805345527625571217804875)
  ·
    refine ⟨217208018291438356826707313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144805345527625571217804875 217208018291438356826707313)
    ·
      refine ⟨162906013718578767620030485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217208018291438356826707313 162906013718578767620030485)
      ·
        refine ⟨7636219393058379732188929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 162906013718578767620030485 7636219393058379732188929)
        ·
          refine ⟨5727164544793784799141697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7636219393058379732188929 5727164544793784799141697)
          ·
            refine ⟨4295373408595338599356273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727164544793784799141697 4295373408595338599356273)
            ·
              refine ⟨3221530056446503949517205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295373408595338599356273 3221530056446503949517205)
              ·
                refine ⟨151009221395929872633619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3221530056446503949517205 151009221395929872633619)
                ·
                  rfl

theorem cell22_3970207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 6].length) (baseStart_3970207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970207 prefixEnd_3970207 := by exact prefixLift 3970207
  have htrace : WordTrace (prefixWord ++ tailWord_3970207) baseStart_3970207 baseEnd_3970207 := by
    simpa [prefixWord, tailWord_3970207, baseEnd_3970207] using wordTrace_append hprefix tailTrace_3970207
  have hstable : (prefixWord ++ tailWord_3970207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970207).length < 2 ^ (prefixWord ++ tailWord_3970207).sum := by decide
  have hdescent : baseEnd_3970207 < baseStart_3970207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970263 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 6]
def baseStart_3970263 : Nat := 118140960795 + 3970263 * 2 ^ 59
def prefixEnd_3970263 : Nat := 4983230072969 + 3 ^ 40 * 3970263 * 2
def baseEnd_3970263 : Nat := 453034054169267791434133

theorem tailTrace_3970263 : CollatzResearch.WordTrace tailWord_3970263 prefixEnd_3970263 453034054169267791434133 := by
  unfold tailWord_3970263
  simp only [CollatzResearch.WordTrace]
  refine ⟨144807388015422692781843443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96538258676948461854562295 144807388015422692781843443)
  ·
    refine ⟨217211082023134039172765165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144807388015422692781843443 217211082023134039172765165)
    ·
      refine ⟨81454155758675264689786937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217211082023134039172765165 81454155758675264689786937)
      ·
        refine ⟨61090616819006448517340203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81454155758675264689786937 61090616819006448517340203)
        ·
          refine ⟨91635925228509672776010305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61090616819006448517340203 91635925228509672776010305)
          ·
            refine ⟨68726943921382254582007729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91635925228509672776010305 68726943921382254582007729)
            ·
              refine ⟨51545207941036690936505797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68726943921382254582007729 51545207941036690936505797)
              ·
                refine ⟨9664726488944379550594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51545207941036690936505797 9664726488944379550594837)
                ·
                  refine ⟨453034054169267791434133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9664726488944379550594837 453034054169267791434133)
                  ·
                    rfl

theorem cell22_3970263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_3970263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970263 prefixEnd_3970263 := by exact prefixLift 3970263
  have htrace : WordTrace (prefixWord ++ tailWord_3970263) baseStart_3970263 baseEnd_3970263 := by
    simpa [prefixWord, tailWord_3970263, baseEnd_3970263] using wordTrace_append hprefix tailTrace_3970263
  have hstable : (prefixWord ++ tailWord_3970263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970263).length < 2 ^ (prefixWord ++ tailWord_3970263).sum := by decide
  have hdescent : baseEnd_3970263 < baseStart_3970263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970312 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 1, 5]
def baseStart_3970312 : Nat := 118140960795 + 3970312 * 2 ^ 59
def prefixEnd_3970312 : Nat := 4983230072969 + 3 ^ 40 * 3970312 * 2
def baseEnd_3970312 : Nat := 1359118936209183579827249

theorem tailTrace_3970312 : CollatzResearch.WordTrace tailWord_3970312 prefixEnd_3970312 1359118936209183579827249 := by
  unfold tailWord_3970312
  simp only [CollatzResearch.WordTrace]
  refine ⟨72404587596122587075188595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96539450128163449433584793 72404587596122587075188595)
  ·
    refine ⟨108606881394183880612782893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72404587596122587075188595 108606881394183880612782893)
    ·
      refine ⟨40727580522818955229793585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108606881394183880612782893 40727580522818955229793585)
      ·
        refine ⟨30545685392114216422345189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40727580522818955229793585 30545685392114216422345189)
        ·
          refine ⟨5727316011021415579189723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30545685392114216422345189 5727316011021415579189723)
          ·
            refine ⟨8590974016532123368784585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727316011021415579189723 8590974016532123368784585)
            ·
              refine ⟨6443230512399092526588439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590974016532123368784585 6443230512399092526588439)
              ·
                refine ⟨9664845768598638789882659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6443230512399092526588439 9664845768598638789882659)
                ·
                  refine ⟨14497268652897958184823989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9664845768598638789882659 14497268652897958184823989)
                  ·
                    refine ⟨1359118936209183579827249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14497268652897958184823989 1359118936209183579827249)
                    ·
                      rfl

theorem cell22_3970312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_3970312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970312 prefixEnd_3970312 := by exact prefixLift 3970312
  have htrace : WordTrace (prefixWord ++ tailWord_3970312) baseStart_3970312 baseEnd_3970312 := by
    simpa [prefixWord, tailWord_3970312, baseEnd_3970312] using wordTrace_append hprefix tailTrace_3970312
  have hstable : (prefixWord ++ tailWord_3970312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970312).length < 2 ^ (prefixWord ++ tailWord_3970312).sum := by decide
  have hdescent : baseEnd_3970312 < baseStart_3970312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970346 : List Nat := [3, 1, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3970346 : Nat := 118140960795 + 3970346 * 2 ^ 59
def prefixEnd_3970346 : Nat := 4983230072969 + 3 ^ 40 * 3970346 * 2
def baseEnd_3970346 : Nat := 1359130575104018824477145

theorem tailTrace_3970346 : CollatzResearch.WordTrace tailWord_3970346 prefixEnd_3970346 1359130575104018824477145 := by
  unfold tailWord_3970346
  simp only [CollatzResearch.WordTrace]
  refine ⟨36202603818530499489278723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96540276849414665304743261 36202603818530499489278723)
  ·
    refine ⟨54303905727795749233918085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36202603818530499489278723 54303905727795749233918085)
    ·
      refine ⟨10181982323961702981359641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54303905727795749233918085 10181982323961702981359641)
      ·
        refine ⟨7636486742971277236019731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10181982323961702981359641 7636486742971277236019731)
        ·
          refine ⟨11454730114456915854029597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7636486742971277236019731 11454730114456915854029597)
          ·
            refine ⟨4295523792921343445261099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11454730114456915854029597 4295523792921343445261099)
            ·
              refine ⟨6443285689382015167891649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295523792921343445261099 6443285689382015167891649)
              ·
                refine ⟨4832464267036511375918737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443285689382015167891649 4832464267036511375918737)
                ·
                  refine ⟨3624348200277383531939053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832464267036511375918737 3624348200277383531939053)
                  ·
                    refine ⟨1359130575104018824477145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624348200277383531939053 1359130575104018824477145)
                    ·
                      rfl

theorem cell22_3970346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3970346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970346 prefixEnd_3970346 := by exact prefixLift 3970346
  have htrace : WordTrace (prefixWord ++ tailWord_3970346) baseStart_3970346 baseEnd_3970346 := by
    simpa [prefixWord, tailWord_3970346, baseEnd_3970346] using wordTrace_append hprefix tailTrace_3970346
  have hstable : (prefixWord ++ tailWord_3970346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970346).length < 2 ^ (prefixWord ++ tailWord_3970346).sum := by decide
  have hdescent : baseEnd_3970346 < baseStart_3970346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970357 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3970357 : Nat := 118140960795 + 3970357 * 2 ^ 59
def prefixEnd_3970357 : Nat := 4983230072969 + 3 ^ 40 * 3970357 * 2
def baseEnd_3970357 : Nat := 1359134340628818462452111

theorem tailTrace_3970357 : CollatzResearch.WordTrace tailWord_3970357 prefixEnd_3970357 1359134340628818462452111 := by
  unfold tailWord_3970357
  simp only [CollatzResearch.WordTrace]
  refine ⟨144810816477082146835765325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96540544318054764557176883 144810816477082146835765325)
  ·
    refine ⟨54304056178905805063411997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144810816477082146835765325 54304056178905805063411997)
    ·
      refine ⟨20364021067089676898779499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54304056178905805063411997 20364021067089676898779499)
      ·
        refine ⟨30546031600634515348169249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20364021067089676898779499 30546031600634515348169249)
        ·
          refine ⟨22909523700475886511126937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30546031600634515348169249 22909523700475886511126937)
          ·
            refine ⟨17182142775356914883345203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22909523700475886511126937 17182142775356914883345203)
            ·
              refine ⟨25773214163035372325017805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17182142775356914883345203 25773214163035372325017805)
              ·
                refine ⟨9664955311138264621881677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25773214163035372325017805 9664955311138264621881677)
                ·
                  refine ⟨3624358241676849233205629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9664955311138264621881677 3624358241676849233205629)
                  ·
                    refine ⟨1359134340628818462452111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624358241676849233205629 1359134340628818462452111)
                    ·
                      rfl

theorem cell22_3970357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3970357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970357 prefixEnd_3970357 := by exact prefixLift 3970357
  have htrace : WordTrace (prefixWord ++ tailWord_3970357) baseStart_3970357 baseEnd_3970357 := by
    simpa [prefixWord, tailWord_3970357, baseEnd_3970357] using wordTrace_append hprefix tailTrace_3970357
  have hstable : (prefixWord ++ tailWord_3970357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970357).length < 2 ^ (prefixWord ++ tailWord_3970357).sum := by decide
  have hdescent : baseEnd_3970357 < baseStart_3970357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970391 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 1, 3]
def baseStart_3970391 : Nat := 118140960795 + 3970391 * 2 ^ 59
def prefixEnd_3970391 : Nat := 4983230072969 + 3 ^ 40 * 3970391 * 2
def baseEnd_3970391 : Nat := 1359145979523653707102007

theorem tailTrace_3970391 : CollatzResearch.WordTrace tailWord_3970391 prefixEnd_3970391 1359145979523653707102007 := by
  unfold tailWord_3970391
  simp only [CollatzResearch.WordTrace]
  refine ⟨144812056558958970642503027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96541371039305980428335351 144812056558958970642503027)
  ·
    refine ⟨217218084838438455963754541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144812056558958970642503027 217218084838438455963754541)
    ·
      refine ⟨81456781814414420986407953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217218084838438455963754541 81456781814414420986407953)
      ·
        refine ⟨61092586360810815739805965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81456781814414420986407953 61092586360810815739805965)
        ·
          refine ⟨22909719885304055902427237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61092586360810815739805965 22909719885304055902427237)
          ·
            refine ⟨4295572478494510481705107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22909719885304055902427237 4295572478494510481705107)
            ·
              refine ⟨6443358717741765722557661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295572478494510481705107 6443358717741765722557661)
              ·
                refine ⟨2416259519153162145959123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6443358717741765722557661 2416259519153162145959123)
                ·
                  refine ⟨3624389278729743218938685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416259519153162145959123 3624389278729743218938685)
                  ·
                    refine ⟨1359145979523653707102007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624389278729743218938685 1359145979523653707102007)
                    ·
                      rfl

theorem cell22_3970391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_3970391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970391 prefixEnd_3970391 := by exact prefixLift 3970391
  have htrace : WordTrace (prefixWord ++ tailWord_3970391) baseStart_3970391 baseEnd_3970391 := by
    simpa [prefixWord, tailWord_3970391, baseEnd_3970391] using wordTrace_append hprefix tailTrace_3970391
  have hstable : (prefixWord ++ tailWord_3970391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970391).length < 2 ^ (prefixWord ++ tailWord_3970391).sum := by decide
  have hdescent : baseEnd_3970391 < baseStart_3970391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970408 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3970408 : Nat := 118140960795 + 3970408 * 2 ^ 59
def prefixEnd_3970408 : Nat := 4983230072969 + 3 ^ 40 * 3970408 * 2
def baseEnd_3970408 : Nat := 1359151798971071329426955

theorem tailTrace_3970408 : CollatzResearch.WordTrace tailWord_3970408 prefixEnd_3970408 1359151798971071329426955 := by
  unfold tailWord_3970408
  simp only [CollatzResearch.WordTrace]
  refine ⟨72406338299948691272935939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96541784399931588363914585 72406338299948691272935939)
  ·
    refine ⟨108609507449923036909403909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72406338299948691272935939 108609507449923036909403909)
    ·
      refine ⟨20364282646860569420513233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108609507449923036909403909 20364282646860569420513233)
      ·
        refine ⟨15273211985145427065384925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20364282646860569420513233 15273211985145427065384925)
        ·
          refine ⟨5727454494429535149519347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15273211985145427065384925 5727454494429535149519347)
          ·
            refine ⟨8591181741644302724279021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727454494429535149519347 8591181741644302724279021)
            ·
              refine ⟨3221693153116613521604633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8591181741644302724279021 3221693153116613521604633)
              ·
                refine ⟨2416269864837460141203475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221693153116613521604633 2416269864837460141203475)
                ·
                  refine ⟨3624404797256190211805213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416269864837460141203475 3624404797256190211805213)
                  ·
                    refine ⟨1359151798971071329426955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624404797256190211805213 1359151798971071329426955)
                    ·
                      rfl

theorem cell22_3970408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3970408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970408 prefixEnd_3970408 := by exact prefixLift 3970408
  have htrace : WordTrace (prefixWord ++ tailWord_3970408) baseStart_3970408 baseEnd_3970408 := by
    simpa [prefixWord, tailWord_3970408, baseEnd_3970408] using wordTrace_append hprefix tailTrace_3970408
  have hstable : (prefixWord ++ tailWord_3970408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970408).length < 2 ^ (prefixWord ++ tailWord_3970408).sum := by decide
  have hdescent : baseEnd_3970408 < baseStart_3970408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970421 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 5]
def baseStart_3970421 : Nat := 118140960795 + 3970421 * 2 ^ 59
def prefixEnd_3970421 : Nat := 4983230072969 + 3 ^ 40 * 3970421 * 2
def baseEnd_3970421 : Nat := 453052083045581209617305

theorem tailTrace_3970421 : CollatzResearch.WordTrace tailWord_3970421 prefixEnd_3970421 453052083045581209617305 := by
  unfold tailWord_3970421
  simp only [CollatzResearch.WordTrace]
  refine ⟨144813150748850285766095117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96542100499233523844063411 144813150748850285766095117)
  ·
    refine ⟨54304931530818857162285669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144813150748850285766095117 54304931530818857162285669)
    ·
      refine ⟨10182174662028535717928563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54304931530818857162285669 10182174662028535717928563)
      ·
        refine ⟨15273261993042803576892845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10182174662028535717928563 15273261993042803576892845)
        ·
          refine ⟨5727473247391051341334817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15273261993042803576892845 5727473247391051341334817)
          ·
            refine ⟨4295604935543288506001113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727473247391051341334817 4295604935543288506001113)
            ·
              refine ⟨3221703701657466379500835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295604935543288506001113 3221703701657466379500835)
              ·
                refine ⟨4832555552486199569251253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3221703701657466379500835 4832555552486199569251253)
                ·
                  refine ⟨453052083045581209617305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832555552486199569251253 453052083045581209617305)
                  ·
                    rfl

theorem cell22_3970421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_3970421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970421 prefixEnd_3970421 := by exact prefixLift 3970421
  have htrace : WordTrace (prefixWord ++ tailWord_3970421) baseStart_3970421 baseEnd_3970421 := by
    simpa [prefixWord, tailWord_3970421, baseEnd_3970421] using wordTrace_append hprefix tailTrace_3970421
  have hstable : (prefixWord ++ tailWord_3970421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970421).length < 2 ^ (prefixWord ++ tailWord_3970421).sum := by decide
  have hdescent : baseEnd_3970421 < baseStart_3970421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970464 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 2, 3]
def baseStart_3970464 : Nat := 118140960795 + 3970464 * 2 ^ 59
def prefixEnd_3970464 : Nat := 4983230072969 + 3 ^ 40 * 3970464 * 2
def baseEnd_3970464 : Nat := 1359170968915505850026783

theorem tailTrace_3970464 : CollatzResearch.WordTrace tailWord_3970464 prefixEnd_3970464 1359170968915505850026783 := by
  unfold tailWord_3970464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72407359543847252054955223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96543146058463002739940297 72407359543847252054955223)
  ·
    refine ⟨108611039315770878082432835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72407359543847252054955223 108611039315770878082432835)
    ·
      refine ⟨162916558973656317123649253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108611039315770878082432835 162916558973656317123649253)
      ·
        refine ⟨30546854807560559460684235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162916558973656317123649253 30546854807560559460684235)
        ·
          refine ⟨45820282211340839191026353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30546854807560559460684235 45820282211340839191026353)
          ·
            refine ⟨34365211658505629393269765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45820282211340839191026353 34365211658505629393269765)
            ·
              refine ⟨6443477185969805511238081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34365211658505629393269765 6443477185969805511238081)
              ·
                refine ⟨4832607889477354133428561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443477185969805511238081 4832607889477354133428561)
                ·
                  refine ⟨3624455917108015600071421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832607889477354133428561 3624455917108015600071421)
                  ·
                    refine ⟨1359170968915505850026783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624455917108015600071421 1359170968915505850026783)
                    ·
                      rfl

theorem cell22_3970464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_3970464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970464 prefixEnd_3970464 := by exact prefixLift 3970464
  have htrace : WordTrace (prefixWord ++ tailWord_3970464) baseStart_3970464 baseEnd_3970464 := by
    simpa [prefixWord, tailWord_3970464, baseEnd_3970464] using wordTrace_append hprefix tailTrace_3970464
  have hstable : (prefixWord ++ tailWord_3970464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970464).length < 2 ^ (prefixWord ++ tailWord_3970464).sum := by decide
  have hdescent : baseEnd_3970464 < baseStart_3970464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970466 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3970466 : Nat := 118140960795 + 3970466 * 2 ^ 59
def prefixEnd_3970466 : Nat := 4983230072969 + 3 ^ 40 * 3970466 * 2
def baseEnd_3970466 : Nat := 453057217852126170492259

theorem tailTrace_3970466 : CollatzResearch.WordTrace tailWord_3970466 prefixEnd_3970466 453057217852126170492259 := by
  unfold tailWord_3970466
  simp only [CollatzResearch.WordTrace]
  refine ⟨36203698008421814612870813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96543194689124838967655501 36203698008421814612870813)
  ·
    refine ⟨13576386753158180479826555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36203698008421814612870813 13576386753158180479826555)
    ·
      refine ⟨20364580129737270719739833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13576386753158180479826555 20364580129737270719739833)
      ·
        refine ⟨15273435097302953039804875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20364580129737270719739833 15273435097302953039804875)
        ·
          refine ⟨22910152645954429559707313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15273435097302953039804875 22910152645954429559707313)
          ·
            refine ⟨17182614484465822169780485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22910152645954429559707313 17182614484465822169780485)
            ·
              refine ⟨3221740215837341656833841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17182614484465822169780485 3221740215837341656833841)
              ·
                refine ⟨2416305161878006242625381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221740215837341656833841 2416305161878006242625381)
                ·
                  refine ⟨453057217852126170492259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416305161878006242625381 453057217852126170492259)
                  ·
                    rfl

theorem cell22_3970466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3970466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970466 prefixEnd_3970466 := by exact prefixLift 3970466
  have htrace : WordTrace (prefixWord ++ tailWord_3970466) baseStart_3970466 baseEnd_3970466 := by
    simpa [prefixWord, tailWord_3970466, baseEnd_3970466] using wordTrace_append hprefix tailTrace_3970466
  have hstable : (prefixWord ++ tailWord_3970466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970466).length < 2 ^ (prefixWord ++ tailWord_3970466).sum := by decide
  have hdescent : baseEnd_3970466 < baseStart_3970466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970505 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 7]
def baseStart_3970505 : Nat := 118140960795 + 3970505 * 2 ^ 59
def prefixEnd_3970505 : Nat := 4983230072969 + 3 ^ 40 * 3970505 * 2
def baseEnd_3970505 : Nat := 453061668017798469917219

theorem tailTrace_3970505 : CollatzResearch.WordTrace tailWord_3970505 prefixEnd_3970505 453061668017798469917219 := by
  unfold tailWord_3970505
  simp only [CollatzResearch.WordTrace]
  refine ⟨144816214480545968112152969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96544142987030645408101979 144816214480545968112152969)
  ·
    refine ⟨108612160860409476084114727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144816214480545968112152969 108612160860409476084114727)
    ·
      refine ⟨162918241290614214126172091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108612160860409476084114727 162918241290614214126172091)
      ·
        refine ⟨244377361935921321189258137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162918241290614214126172091 244377361935921321189258137)
        ·
          refine ⟨183283021451940990891943603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244377361935921321189258137 183283021451940990891943603)
          ·
            refine ⟨274924532177911486337915405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183283021451940990891943603 274924532177911486337915405)
            ·
              refine ⟨103096699566716807376718277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 274924532177911486337915405 103096699566716807376718277)
              ·
                refine ⟨19330631168759401383134677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103096699566716807376718277 19330631168759401383134677)
                ·
                  refine ⟨453061668017798469917219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19330631168759401383134677 453061668017798469917219)
                  ·
                    rfl

theorem cell22_3970505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_3970505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970505 prefixEnd_3970505 := by exact prefixLift 3970505
  have htrace : WordTrace (prefixWord ++ tailWord_3970505) baseStart_3970505 baseEnd_3970505 := by
    simpa [prefixWord, tailWord_3970505, baseEnd_3970505] using wordTrace_append hprefix tailTrace_3970505
  have hstable : (prefixWord ++ tailWord_3970505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970505).length < 2 ^ (prefixWord ++ tailWord_3970505).sum := by decide
  have hdescent : baseEnd_3970505 < baseStart_3970505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970522 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_3970522 : Nat := 118140960795 + 3970522 * 2 ^ 59
def prefixEnd_3970522 : Nat := 4983230072969 + 3 ^ 40 * 3970522 * 2
def baseEnd_3970522 : Nat := 453063607833604344025535

theorem tailTrace_3970522 : CollatzResearch.WordTrace tailWord_3970522 prefixEnd_3970522 453063607833604344025535 := by
  unfold tailWord_3970522
  simp only [CollatzResearch.WordTrace]
  refine ⟨36204208630371095003880455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96544556347656253343681213 36204208630371095003880455)
  ·
    refine ⟨54306312945556642505820683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36204208630371095003880455 54306312945556642505820683)
    ·
      refine ⟨81459469418334963758731025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54306312945556642505820683 81459469418334963758731025)
      ·
        refine ⟨61094602063751222819048269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81459469418334963758731025 61094602063751222819048269)
        ·
          refine ⟨22910475773906708557143101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61094602063751222819048269 22910475773906708557143101)
          ·
            refine ⟨8591428415215015708928663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22910475773906708557143101 8591428415215015708928663)
            ·
              refine ⟨12887142622822523563392995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591428415215015708928663 12887142622822523563392995)
              ·
                refine ⟨19330713934233785345089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887142622822523563392995 19330713934233785345089493)
                ·
                  refine ⟨453063607833604344025535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19330713934233785345089493 453063607833604344025535)
                  ·
                    rfl

theorem cell22_3970522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_3970522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970522 prefixEnd_3970522 := by exact prefixLift 3970522
  have htrace : WordTrace (prefixWord ++ tailWord_3970522) baseStart_3970522 baseEnd_3970522 := by
    simpa [prefixWord, tailWord_3970522, baseEnd_3970522] using wordTrace_append hprefix tailTrace_3970522
  have hstable : (prefixWord ++ tailWord_3970522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970522).length < 2 ^ (prefixWord ++ tailWord_3970522).sum := by decide
  have hdescent : baseEnd_3970522 < baseStart_3970522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970590 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3970590 : Nat := 118140960795 + 3970590 * 2 ^ 59
def prefixEnd_3970590 : Nat := 4983230072969 + 3 ^ 40 * 3970590 * 2
def baseEnd_3970590 : Nat := 453071367096827840458799

theorem tailTrace_3970590 : CollatzResearch.WordTrace tailWord_3970590 prefixEnd_3970590 453071367096827840458799 := by
  unfold tailWord_3970590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102414335654753453624653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96546209790158685085998149 18102414335654753453624653)
  ·
    refine ⟨6788405375870532545109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18102414335654753453624653 6788405375870532545109245)
    ·
      refine ⟨2545652015951449704415967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6788405375870532545109245 2545652015951449704415967)
      ·
        refine ⟨3818478023927174556623951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545652015951449704415967 3818478023927174556623951)
        ·
          refine ⟨5727717035890761834935927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818478023927174556623951 5727717035890761834935927)
          ·
            refine ⟨8591575553836142752403891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727717035890761834935927 8591575553836142752403891)
            ·
              refine ⟨12887363330754214128605837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591575553836142752403891 12887363330754214128605837)
              ·
                refine ⟨4832761249032830298227189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12887363330754214128605837 4832761249032830298227189)
                ·
                  refine ⟨453071367096827840458799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4832761249032830298227189 453071367096827840458799)
                  ·
                    rfl

theorem cell22_3970590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3970590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970590 prefixEnd_3970590 := by exact prefixLift 3970590
  have htrace : WordTrace (prefixWord ++ tailWord_3970590) baseStart_3970590 baseEnd_3970590 := by
    simpa [prefixWord, tailWord_3970590, baseEnd_3970590] using wordTrace_append hprefix tailTrace_3970590
  have hstable : (prefixWord ++ tailWord_3970590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970590).length < 2 ^ (prefixWord ++ tailWord_3970590).sum := by decide
  have hdescent : baseEnd_3970590 < baseStart_3970590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970597 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3970597 : Nat := 118140960795 + 3970597 * 2 ^ 59
def prefixEnd_3970597 : Nat := 4983230072969 + 3 ^ 40 * 3970597 * 2
def baseEnd_3970597 : Nat := 1359216497533537836451375

theorem tailTrace_3970597 : CollatzResearch.WordTrace tailWord_3970597 prefixEnd_3970597 1359216497533537836451375 := by
  unfold tailWord_3970597
  simp only [CollatzResearch.WordTrace]
  refine ⟨144819569996212667824502045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96546379997475111883001363 144819569996212667824502045)
  ·
    refine ⟨54307338748579750434188267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144819569996212667824502045 54307338748579750434188267)
    ·
      refine ⟨81461008122869625651282401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54307338748579750434188267 81461008122869625651282401)
      ·
        refine ⟨61095756092152219238461801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81461008122869625651282401 61095756092152219238461801)
        ·
          refine ⟨45821817069114164428846351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61095756092152219238461801 45821817069114164428846351)
          ·
            refine ⟨68732725603671246643269527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45821817069114164428846351 68732725603671246643269527)
            ·
              refine ⟨103099088405506869964904291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68732725603671246643269527 103099088405506869964904291)
              ·
                refine ⟨154648632608260304947356437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103099088405506869964904291 154648632608260304947356437)
                ·
                  refine ⟨7249154653512201794407333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154648632608260304947356437 7249154653512201794407333)
                  ·
                    refine ⟨1359216497533537836451375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249154653512201794407333 1359216497533537836451375)
                    ·
                      rfl

theorem cell22_3970597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3970597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970597 prefixEnd_3970597 := by exact prefixLift 3970597
  have htrace : WordTrace (prefixWord ++ tailWord_3970597) baseStart_3970597 baseEnd_3970597 := by
    simpa [prefixWord, tailWord_3970597, baseEnd_3970597] using wordTrace_append hprefix tailTrace_3970597
  have hstable : (prefixWord ++ tailWord_3970597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970597).length < 2 ^ (prefixWord ++ tailWord_3970597).sum := by decide
  have hdescent : baseEnd_3970597 < baseStart_3970597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970661 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_3970661 : Nat := 118140960795 + 3970661 * 2 ^ 59
def prefixEnd_3970661 : Nat := 4983230072969 + 3 ^ 40 * 3970661 * 2
def baseEnd_3970661 : Nat := 1359238406041463002851179

theorem tailTrace_3970661 : CollatzResearch.WordTrace tailWord_3970661 prefixEnd_3970661 1359238406041463002851179 := by
  unfold tailWord_3970661
  simp only [CollatzResearch.WordTrace]
  refine ⟨144821904267980806754831837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96547936178653871169887891 144821904267980806754831837)
  ·
    refine ⟨54308214100492802533061939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144821904267980806754831837 54308214100492802533061939)
    ·
      refine ⟨81462321150739203799592909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54308214100492802533061939 81462321150739203799592909)
      ·
        refine ⟨30548370431527201424847341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81462321150739203799592909 30548370431527201424847341)
        ·
          refine ⟨11455638911822700534317753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30548370431527201424847341 11455638911822700534317753)
          ·
            refine ⟨8591729183867025400738315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11455638911822700534317753 8591729183867025400738315)
            ·
              refine ⟨12887593775800538101107473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591729183867025400738315 12887593775800538101107473)
              ·
                refine ⟨9665695331850403575830605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12887593775800538101107473 9665695331850403575830605)
                ·
                  refine ⟨3624635749443901340936477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9665695331850403575830605 3624635749443901340936477)
                  ·
                    refine ⟨1359238406041463002851179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624635749443901340936477 1359238406041463002851179)
                    ·
                      rfl

theorem cell22_3970661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_3970661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970661 prefixEnd_3970661 := by exact prefixLift 3970661
  have htrace : WordTrace (prefixWord ++ tailWord_3970661) baseStart_3970661 baseEnd_3970661 := by
    simpa [prefixWord, tailWord_3970661, baseEnd_3970661] using wordTrace_append hprefix tailTrace_3970661
  have hstable : (prefixWord ++ tailWord_3970661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970661).length < 2 ^ (prefixWord ++ tailWord_3970661).sum := by decide
  have hdescent : baseEnd_3970661 < baseStart_3970661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970689 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3970689 : Nat := 118140960795 + 3970689 * 2 ^ 59
def prefixEnd_3970689 : Nat := 4983230072969 + 3 ^ 40 * 3970689 * 2
def baseEnd_3970689 : Nat := 1359247991013680263151093

theorem tailTrace_3970689 : CollatzResearch.WordTrace tailWord_3970689 prefixEnd_3970689 1359247991013680263151093 := by
  unfold tailWord_3970689
  simp only [CollatzResearch.WordTrace]
  refine ⟨144822925511879367536851121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96548617007919578357900747 144822925511879367536851121)
  ·
    refine ⟨108617194133909525652638341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144822925511879367536851121 108617194133909525652638341)
    ·
      refine ⟨20365723900108036059869689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108617194133909525652638341 20365723900108036059869689)
      ·
        refine ⟨15274292925081027044902267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20365723900108036059869689 15274292925081027044902267)
        ·
          refine ⟨22911439387621540567353401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15274292925081027044902267 22911439387621540567353401)
          ·
            refine ⟨17183579540716155425515051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22911439387621540567353401 17183579540716155425515051)
            ·
              refine ⟨25775369311074233138272577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183579540716155425515051 25775369311074233138272577)
              ·
                refine ⟨19331526983305674853704433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25775369311074233138272577 19331526983305674853704433)
                ·
                  refine ⟨14498645237479256140278325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19331526983305674853704433 14498645237479256140278325)
                  ·
                    refine ⟨1359247991013680263151093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14498645237479256140278325 1359247991013680263151093)
                    ·
                      rfl

theorem cell22_3970689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3970689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970689 prefixEnd_3970689 := by exact prefixLift 3970689
  have htrace : WordTrace (prefixWord ++ tailWord_3970689) baseStart_3970689 baseEnd_3970689 := by
    simpa [prefixWord, tailWord_3970689, baseEnd_3970689] using wordTrace_append hprefix tailTrace_3970689
  have hstable : (prefixWord ++ tailWord_3970689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970689).length < 2 ^ (prefixWord ++ tailWord_3970689).sum := by decide
  have hdescent : baseEnd_3970689 < baseStart_3970689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970721 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_3970721 : Nat := 118140960795 + 3970721 * 2 ^ 59
def prefixEnd_3970721 : Nat := 4983230072969 + 3 ^ 40 * 3970721 * 2
def baseEnd_3970721 : Nat := 1359258945267642846350995

theorem tailTrace_3970721 : CollatzResearch.WordTrace tailWord_3970721 prefixEnd_3970721 1359258945267642846350995 := by
  unfold tailWord_3970721
  simp only [CollatzResearch.WordTrace]
  refine ⟨144824092647763437002016017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96549395098508958001344011 144824092647763437002016017)
  ·
    refine ⟨108618069485822577751512013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144824092647763437002016017 108618069485822577751512013)
    ·
      refine ⟨40731776057183466656817005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108618069485822577751512013 40731776057183466656817005)
      ·
        refine ⟨15274416021443799996306377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40731776057183466656817005 15274416021443799996306377)
        ·
          refine ⟨11455812016082849997229783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15274416021443799996306377 11455812016082849997229783)
          ·
            refine ⟨17183718024124274995844675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455812016082849997229783 17183718024124274995844675)
            ·
              refine ⟨25775577036186412493767013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183718024124274995844675 25775577036186412493767013)
              ·
                refine ⟨4832920694284952342581315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25775577036186412493767013 4832920694284952342581315)
                ·
                  refine ⟨7249381041427428513871973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4832920694284952342581315 7249381041427428513871973)
                  ·
                    refine ⟨1359258945267642846350995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249381041427428513871973 1359258945267642846350995)
                    ·
                      rfl

theorem cell22_3970721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_3970721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970721 prefixEnd_3970721 := by exact prefixLift 3970721
  have htrace : WordTrace (prefixWord ++ tailWord_3970721) baseStart_3970721 baseEnd_3970721 := by
    simpa [prefixWord, tailWord_3970721, baseEnd_3970721] using wordTrace_append hprefix tailTrace_3970721
  have hstable : (prefixWord ++ tailWord_3970721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970721).length < 2 ^ (prefixWord ++ tailWord_3970721).sum := by decide
  have hdescent : baseEnd_3970721 < baseStart_3970721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970736 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_3970736 : Nat := 118140960795 + 3970736 * 2 ^ 59
def prefixEnd_3970736 : Nat := 4983230072969 + 3 ^ 40 * 3970736 * 2
def baseEnd_3970736 : Nat := 453088026691395935741983

theorem tailTrace_3970736 : CollatzResearch.WordTrace tailWord_3970736 prefixEnd_3970736 453088026691395935741983 := by
  unfold tailWord_3970736
  simp only [CollatzResearch.WordTrace]
  refine ⟨72412319871354547281906031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96549759828472729709208041 72412319871354547281906031)
  ·
    refine ⟨108618479807031820922859047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72412319871354547281906031 108618479807031820922859047)
    ·
      refine ⟨162927719710547731384288571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108618479807031820922859047 162927719710547731384288571)
      ·
        refine ⟨244391579565821597076432857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162927719710547731384288571 244391579565821597076432857)
        ·
          refine ⟨183293684674366197807324643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244391579565821597076432857 183293684674366197807324643)
          ·
            refine ⟨274940527011549296710986965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183293684674366197807324643 274940527011549296710986965)
            ·
              refine ⟨6443918601833186641663757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 274940527011549296710986965 6443918601833186641663757)
              ·
                refine ⟨2416469475687444990623909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6443918601833186641663757 2416469475687444990623909)
                ·
                  refine ⟨453088026691395935741983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416469475687444990623909 453088026691395935741983)
                  ·
                    rfl

theorem cell22_3970736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_3970736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970736 prefixEnd_3970736 := by exact prefixLift 3970736
  have htrace : WordTrace (prefixWord ++ tailWord_3970736) baseStart_3970736 baseEnd_3970736 := by
    simpa [prefixWord, tailWord_3970736, baseEnd_3970736] using wordTrace_append hprefix tailTrace_3970736
  have hstable : (prefixWord ++ tailWord_3970736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970736).length < 2 ^ (prefixWord ++ tailWord_3970736).sum := by decide
  have hdescent : baseEnd_3970736 < baseStart_3970736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970751 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 2, 3]
def baseStart_3970751 : Nat := 118140960795 + 3970751 * 2 ^ 59
def prefixEnd_3970751 : Nat := 4983230072969 + 3 ^ 40 * 3970751 * 2
def baseEnd_3970751 : Nat := 1359269214880732768100903

theorem tailTrace_3970751 : CollatzResearch.WordTrace tailWord_3970751 prefixEnd_3970751 1359269214880732768100903 := by
  unfold tailWord_3970751
  simp only [CollatzResearch.WordTrace]
  refine ⟨144825186837654752125608107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96550124558436501417072071 144825186837654752125608107)
  ·
    refine ⟨217237780256482128188412161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144825186837654752125608107 217237780256482128188412161)
    ·
      refine ⟨162928335192361596141309121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217237780256482128188412161 162928335192361596141309121)
      ·
        refine ⟨122196251394271197105981841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162928335192361596141309121 122196251394271197105981841)
        ·
          refine ⟨91647188545703397829486381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122196251394271197105981841 91647188545703397829486381)
          ·
            refine ⟨34367695704638774186057393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91647188545703397829486381 34367695704638774186057393)
            ·
              refine ⟨25775771778479080639543045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34367695704638774186057393 25775771778479080639543045)
              ·
                refine ⟨4832957208464827619914321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25775771778479080639543045 4832957208464827619914321)
                ·
                  refine ⟨3624717906348620714935741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4832957208464827619914321 3624717906348620714935741)
                  ·
                    refine ⟨1359269214880732768100903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624717906348620714935741 1359269214880732768100903)
                    ·
                      rfl

theorem cell22_3970751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_3970751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970751 prefixEnd_3970751 := by exact prefixLift 3970751
  have htrace : WordTrace (prefixWord ++ tailWord_3970751) baseStart_3970751 baseEnd_3970751 := by
    simpa [prefixWord, tailWord_3970751, baseEnd_3970751] using wordTrace_append hprefix tailTrace_3970751
  have hstable : (prefixWord ++ tailWord_3970751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970751).length < 2 ^ (prefixWord ++ tailWord_3970751).sum := by decide
  have hdescent : baseEnd_3970751 < baseStart_3970751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970804 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3970804 : Nat := 118140960795 + 3970804 * 2 ^ 59
def prefixEnd_3970804 : Nat := 4983230072969 + 3 ^ 40 * 3970804 * 2
def baseEnd_3970804 : Nat := 453095785954619432175247

theorem tailTrace_3970804 : CollatzResearch.WordTrace tailWord_3970804 prefixEnd_3970804 453095785954619432175247 := by
  unfold tailWord_3970804
  simp only [CollatzResearch.WordTrace]
  refine ⟨72413559953231371088643733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96551413270975161451524977 72413559953231371088643733)
  ·
    refine ⟨3394385622807720519780175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72413559953231371088643733 3394385622807720519780175)
    ·
      refine ⟨5091578434211580779670263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394385622807720519780175 5091578434211580779670263)
      ·
        refine ⟨7637367651317371169505395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091578434211580779670263 7637367651317371169505395)
        ·
          refine ⟨11456051476976056754258093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637367651317371169505395 11456051476976056754258093)
          ·
            refine ⟨4296019303866021282846785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11456051476976056754258093 4296019303866021282846785)
            ·
              refine ⟨3222014477899515962135089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296019303866021282846785 3222014477899515962135089)
              ·
                refine ⟨2416510858424636971601317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222014477899515962135089 2416510858424636971601317)
                ·
                  refine ⟨453095785954619432175247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416510858424636971601317 453095785954619432175247)
                  ·
                    rfl

theorem cell22_3970804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3970804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970804 prefixEnd_3970804 := by exact prefixLift 3970804
  have htrace : WordTrace (prefixWord ++ tailWord_3970804) baseStart_3970804 baseEnd_3970804 := by
    simpa [prefixWord, tailWord_3970804, baseEnd_3970804] using wordTrace_append hprefix tailTrace_3970804
  have hstable : (prefixWord ++ tailWord_3970804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970804).length < 2 ^ (prefixWord ++ tailWord_3970804).sum := by decide
  have hdescent : baseEnd_3970804 < baseStart_3970804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970826 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_3970826 : Nat := 118140960795 + 3970826 * 2 ^ 59
def prefixEnd_3970826 : Nat := 4983230072969 + 3 ^ 40 * 3970826 * 2
def baseEnd_3970826 : Nat := 453098296304485857491891

theorem tailTrace_3970826 : CollatzResearch.WordTrace tailWord_3970826 prefixEnd_3970826 453098296304485857491891 := by
  unfold tailWord_3970826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36206980578095759983647083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96551948208255359956392221 36206980578095759983647083)
  ·
    refine ⟨54310470867143639975470625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36206980578095759983647083 54310470867143639975470625)
    ·
      refine ⟨40732853150357729981602969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54310470867143639975470625 40732853150357729981602969)
      ·
        refine ⟨30549639862768297486202227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40732853150357729981602969 30549639862768297486202227)
        ·
          refine ⟨45824459794152446229303341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30549639862768297486202227 45824459794152446229303341)
          ·
            refine ⟨17184172422807167335988753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45824459794152446229303341 17184172422807167335988753)
            ·
              refine ⟨12888129317105375501991565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184172422807167335988753 12888129317105375501991565)
              ·
                refine ⟨4833048493914515813246837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12888129317105375501991565 4833048493914515813246837)
                ·
                  refine ⟨453098296304485857491891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4833048493914515813246837 453098296304485857491891)
                  ·
                    rfl

theorem cell22_3970826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_3970826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970826 prefixEnd_3970826 := by exact prefixLift 3970826
  have htrace : WordTrace (prefixWord ++ tailWord_3970826) baseStart_3970826 baseEnd_3970826 := by
    simpa [prefixWord, tailWord_3970826, baseEnd_3970826] using wordTrace_append hprefix tailTrace_3970826
  have hstable : (prefixWord ++ tailWord_3970826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970826).length < 2 ^ (prefixWord ++ tailWord_3970826).sum := by decide
  have hdescent : baseEnd_3970826 < baseStart_3970826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970901 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3970901 : Nat := 118140960795 + 3970901 * 2 ^ 59
def prefixEnd_3970901 : Nat := 4983230072969 + 3 ^ 40 * 3970901 * 2
def baseEnd_3970901 : Nat := 1359320562946182376850443

theorem tailTrace_3970901 : CollatzResearch.WordTrace tailWord_3970901 prefixEnd_3970901 1359320562946182376850443 := by
  unfold tailWord_3970901
  simp only [CollatzResearch.WordTrace]
  refine ⟨144830657787111327743568557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96553771858074218495712371 144830657787111327743568557)
  ·
    refine ⟨54311496670166747903838209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144830657787111327743568557 54311496670166747903838209)
    ·
      refine ⟨40733622502625060927878657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54311496670166747903838209 40733622502625060927878657)
      ·
        refine ⟨30550216876968795695908993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40733622502625060927878657 30550216876968795695908993)
        ·
          refine ⟨22912662657726596771931745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30550216876968795695908993 22912662657726596771931745)
          ·
            refine ⟨17184496993294947578948809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22912662657726596771931745 17184496993294947578948809)
            ·
              refine ⟨12888372744971210684211607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17184496993294947578948809 12888372744971210684211607)
              ·
                refine ⟨19332559117456816026317411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12888372744971210684211607 19332559117456816026317411)
                ·
                  refine ⟨28998838676185224039476117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19332559117456816026317411 28998838676185224039476117)
                  ·
                    refine ⟨1359320562946182376850443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28998838676185224039476117 1359320562946182376850443)
                    ·
                      rfl

theorem cell22_3970901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3970901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970901 prefixEnd_3970901 := by exact prefixLift 3970901
  have htrace : WordTrace (prefixWord ++ tailWord_3970901) baseStart_3970901 baseEnd_3970901 := by
    simpa [prefixWord, tailWord_3970901, baseEnd_3970901] using wordTrace_append hprefix tailTrace_3970901
  have hstable : (prefixWord ++ tailWord_3970901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970901).length < 2 ^ (prefixWord ++ tailWord_3970901).sum := by decide
  have hdescent : baseEnd_3970901 < baseStart_3970901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970922 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_3970922 : Nat := 118140960795 + 3970922 * 2 ^ 59
def prefixEnd_3970922 : Nat := 4983230072969 + 3 ^ 40 * 3970922 * 2
def baseEnd_3970922 : Nat := 453109250558448440691793

theorem tailTrace_3970922 : CollatzResearch.WordTrace tailWord_3970922 prefixEnd_3970922 453109250558448440691793 := by
  unfold tailWord_3970922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36207855930008812082520755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96554282480023498886722013 36207855930008812082520755)
  ·
    refine ⟨54311783895013218123781133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36207855930008812082520755 54311783895013218123781133)
    ·
      refine ⟨20366918960629956796417925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54311783895013218123781133 20366918960629956796417925)
      ·
        refine ⟨3818797305118116899328361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20366918960629956796417925 3818797305118116899328361)
        ·
          refine ⟨2864097978838587674496271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3818797305118116899328361 2864097978838587674496271)
          ·
            refine ⟨4296146968257881511744407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864097978838587674496271 4296146968257881511744407)
            ·
              refine ⟨6444220452386822267616611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296146968257881511744407 6444220452386822267616611)
              ·
                refine ⟨9666330678580233401424917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444220452386822267616611 9666330678580233401424917)
                ·
                  refine ⟨453109250558448440691793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9666330678580233401424917 453109250558448440691793)
                  ·
                    rfl

theorem cell22_3970922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_3970922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970922 prefixEnd_3970922 := by exact prefixLift 3970922
  have htrace : WordTrace (prefixWord ++ tailWord_3970922) baseStart_3970922 baseEnd_3970922 := by
    simpa [prefixWord, tailWord_3970922, baseEnd_3970922] using wordTrace_append hprefix tailTrace_3970922
  have hstable : (prefixWord ++ tailWord_3970922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970922).length < 2 ^ (prefixWord ++ tailWord_3970922).sum := by decide
  have hdescent : baseEnd_3970922 < baseStart_3970922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970948 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_3970948 : Nat := 118140960795 + 3970948 * 2 ^ 59
def prefixEnd_3970948 : Nat := 4983230072969 + 3 ^ 40 * 3970948 * 2
def baseEnd_3970948 : Nat := 1359336652006689920925299

theorem tailTrace_3970948 : CollatzResearch.WordTrace tailWord_3970948 prefixEnd_3970948 1359336652006689920925299 := by
  unfold tailWord_3970948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72416186008970527385264749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96554914678627369847019665 72416186008970527385264749)
  ·
    refine ⟨27156069753363947769474281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72416186008970527385264749 27156069753363947769474281)
    ·
      refine ⟨20367052315022960827105711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27156069753363947769474281 20367052315022960827105711)
      ·
        refine ⟨30550578472534441240658567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20367052315022960827105711 30550578472534441240658567)
        ·
          refine ⟨45825867708801661860987851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30550578472534441240658567 45825867708801661860987851)
          ·
            refine ⟨68738801563202492791481777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45825867708801661860987851 68738801563202492791481777)
            ·
              refine ⟨51554101172401869593611333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68738801563202492791481777 51554101172401869593611333)
              ·
                refine ⟨9666393969825350548802125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51554101172401869593611333 9666393969825350548802125)
                ·
                  refine ⟨3624897738684506455800797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9666393969825350548802125 3624897738684506455800797)
                  ·
                    refine ⟨1359336652006689920925299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624897738684506455800797 1359336652006689920925299)
                    ·
                      rfl

theorem cell22_3970948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_3970948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970948 prefixEnd_3970948 := by exact prefixLift 3970948
  have htrace : WordTrace (prefixWord ++ tailWord_3970948) baseStart_3970948 baseEnd_3970948 := by
    simpa [prefixWord, tailWord_3970948, baseEnd_3970948] using wordTrace_append hprefix tailTrace_3970948
  have hstable : (prefixWord ++ tailWord_3970948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970948).length < 2 ^ (prefixWord ++ tailWord_3970948).sum := by decide
  have hdescent : baseEnd_3970948 < baseStart_3970948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970965 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_3970965 : Nat := 118140960795 + 3970965 * 2 ^ 59
def prefixEnd_3970965 : Nat := 4983230072969 + 3 ^ 40 * 3970965 * 2
def baseEnd_3970965 : Nat := 1359342471454107543250247

theorem tailTrace_3970965 : CollatzResearch.WordTrace tailWord_3970965 prefixEnd_3970965 1359342471454107543250247 := by
  unfold tailWord_3970965
  simp only [CollatzResearch.WordTrace]
  refine ⟨144832992058879466673898349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96555328039252977782598899 144832992058879466673898349)
  ·
    refine ⟨54312372022079800002711881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144832992058879466673898349 54312372022079800002711881)
    ·
      refine ⟨40734279016559850002033911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54312372022079800002711881 40734279016559850002033911)
      ·
        refine ⟨61101418524839775003050867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40734279016559850002033911 61101418524839775003050867)
        ·
          refine ⟨91652127787259662504576301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61101418524839775003050867 91652127787259662504576301)
          ·
            refine ⟨34369547920222373439216113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91652127787259662504576301 34369547920222373439216113)
            ·
              refine ⟨25777160940166780079412085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34369547920222373439216113 25777160940166780079412085)
              ·
                refine ⟨2416608838140635632444883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25777160940166780079412085 2416608838140635632444883)
                ·
                  refine ⟨3624913257210953448667325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416608838140635632444883 3624913257210953448667325)
                  ·
                    refine ⟨1359342471454107543250247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3624913257210953448667325 1359342471454107543250247)
                    ·
                      rfl

theorem cell22_3970965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_3970965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970965 prefixEnd_3970965 := by exact prefixLift 3970965
  have htrace : WordTrace (prefixWord ++ tailWord_3970965) baseStart_3970965 baseEnd_3970965 := by
    simpa [prefixWord, tailWord_3970965, baseEnd_3970965] using wordTrace_append hprefix tailTrace_3970965
  have hstable : (prefixWord ++ tailWord_3970965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970965).length < 2 ^ (prefixWord ++ tailWord_3970965).sum := by decide
  have hdescent : baseEnd_3970965 < baseStart_3970965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970976 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_3970976 : Nat := 118140960795 + 3970976 * 2 ^ 59
def prefixEnd_3970976 : Nat := 4983230072969 + 3 ^ 40 * 3970976 * 2
def baseEnd_3970976 : Nat := 1359346236978907181225213

theorem tailTrace_3970976 : CollatzResearch.WordTrace tailWord_3970976 prefixEnd_3970976 1359346236978907181225213 := by
  unfold tailWord_3970976
  simp only [CollatzResearch.WordTrace]
  refine ⟨72416696630919807776274391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96555595507893077035032521 72416696630919807776274391)
  ·
    refine ⟨108625044946379711664411587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72416696630919807776274391 108625044946379711664411587)
    ·
      refine ⟨162937567419569567496617381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108625044946379711664411587 162937567419569567496617381)
      ·
        refine ⟨30550793891169293905615759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162937567419569567496617381 30550793891169293905615759)
        ·
          refine ⟨45826190836753940858423639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30550793891169293905615759 45826190836753940858423639)
          ·
            refine ⟨68739286255130911287635459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45826190836753940858423639 68739286255130911287635459)
            ·
              refine ⟨103108929382696366931453189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68739286255130911287635459 103108929382696366931453189)
              ·
                refine ⟨19332924259255568799647473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103108929382696366931453189 19332924259255568799647473)
                ·
                  refine ⟨14499693194441676599735605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19332924259255568799647473 14499693194441676599735605)
                  ·
                    refine ⟨1359346236978907181225213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14499693194441676599735605 1359346236978907181225213)
                    ·
                      rfl

theorem cell22_3970976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_3970976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970976 prefixEnd_3970976 := by exact prefixLift 3970976
  have htrace : WordTrace (prefixWord ++ tailWord_3970976) baseStart_3970976 baseEnd_3970976 := by
    simpa [prefixWord, tailWord_3970976, baseEnd_3970976] using wordTrace_append hprefix tailTrace_3970976
  have hstable : (prefixWord ++ tailWord_3970976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970976).length < 2 ^ (prefixWord ++ tailWord_3970976).sum := by decide
  have hdescent : baseEnd_3970976 < baseStart_3970976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970991 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_3970991 : Nat := 118140960795 + 3970991 * 2 ^ 59
def prefixEnd_3970991 : Nat := 4983230072969 + 3 ^ 40 * 3970991 * 2
def baseEnd_3970991 : Nat := 1359351371785452142100167

theorem tailTrace_3970991 : CollatzResearch.WordTrace tailWord_3970991 prefixEnd_3970991 1359351371785452142100167 := by
  unfold tailWord_3970991
  simp only [CollatzResearch.WordTrace]
  refine ⟨144833940356785273114344827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96555960237856848742896551 144833940356785273114344827)
  ·
    refine ⟨217250910535177909671517241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144833940356785273114344827 217250910535177909671517241)
    ·
      refine ⟨162938182901383432253637931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217250910535177909671517241 162938182901383432253637931)
      ·
        refine ⟨244407274352075148380456897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162938182901383432253637931 244407274352075148380456897)
        ·
          refine ⟨183305455764056361285342673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244407274352075148380456897 183305455764056361285342673)
          ·
            refine ⟨137479091823042270964007005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183305455764056361285342673 137479091823042270964007005)
            ·
              refine ⟨51554659433640851611502627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137479091823042270964007005 51554659433640851611502627)
              ·
                refine ⟨77331989150461277417253941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51554659433640851611502627 77331989150461277417253941)
                ·
                  refine ⟨7249873982855744757867557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77331989150461277417253941 7249873982855744757867557)
                  ·
                    refine ⟨1359351371785452142100167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249873982855744757867557 1359351371785452142100167)
                    ·
                      rfl

theorem cell22_3970991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_3970991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970991 prefixEnd_3970991 := by exact prefixLift 3970991
  have htrace : WordTrace (prefixWord ++ tailWord_3970991) baseStart_3970991 baseEnd_3970991 := by
    simpa [prefixWord, tailWord_3970991, baseEnd_3970991] using wordTrace_append hprefix tailTrace_3970991
  have hstable : (prefixWord ++ tailWord_3970991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970991).length < 2 ^ (prefixWord ++ tailWord_3970991).sum := by decide
  have hdescent : baseEnd_3970991 < baseStart_3970991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3970993 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_3970993 : Nat := 118140960795 + 3970993 * 2 ^ 59
def prefixEnd_3970993 : Nat := 4983230072969 + 3 ^ 40 * 3970993 * 2
def baseEnd_3970993 : Nat := 1359352056426324803550161

theorem tailTrace_3970993 : CollatzResearch.WordTrace tailWord_3970993 prefixEnd_3970993 1359352056426324803550161 := by
  unfold tailWord_3970993
  simp only [CollatzResearch.WordTrace]
  refine ⟨144834013302778027455917633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96556008868518684970611755 144834013302778027455917633)
  ·
    refine ⟨108625509977083520591938225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144834013302778027455917633 108625509977083520591938225)
    ·
      refine ⟨81469132482812640443953669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108625509977083520591938225 81469132482812640443953669)
      ·
        refine ⟨15275462340527370083241313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81469132482812640443953669 15275462340527370083241313)
        ·
          refine ⟨11456596755395527562430985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15275462340527370083241313 11456596755395527562430985)
          ·
            refine ⟨8592447566546645671823239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11456596755395527562430985 8592447566546645671823239)
            ·
              refine ⟨12888671349819968507734859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8592447566546645671823239 12888671349819968507734859)
              ·
                refine ⟨19333007024729952761602289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12888671349819968507734859 19333007024729952761602289)
                ·
                  refine ⟨14499755268547464571201717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19333007024729952761602289 14499755268547464571201717)
                  ·
                    refine ⟨1359352056426324803550161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14499755268547464571201717 1359352056426324803550161)
                    ·
                      rfl

theorem cell22_3970993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_3970993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3970993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3970993 prefixEnd_3970993 := by exact prefixLift 3970993
  have htrace : WordTrace (prefixWord ++ tailWord_3970993) baseStart_3970993 baseEnd_3970993 := by
    simpa [prefixWord, tailWord_3970993, baseEnd_3970993] using wordTrace_append hprefix tailTrace_3970993
  have hstable : (prefixWord ++ tailWord_3970993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3970993).length < 2 ^ (prefixWord ++ tailWord_3970993).sum := by decide
  have hdescent : baseEnd_3970993 < baseStart_3970993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3970993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971008 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 1, 4]
def baseStart_3971008 : Nat := 118140960795 + 3971008 * 2 ^ 59
def prefixEnd_3971008 : Nat := 4983230072969 + 3 ^ 40 * 3971008 * 2
def baseEnd_3971008 : Nat := 1359357191232869764425115

theorem tailTrace_3971008 : CollatzResearch.WordTrace tailWord_3971008 prefixEnd_3971008 1359357191232869764425115 := by
  unfold tailWord_3971008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72417280198861842508856839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96556373598482456678475785 72417280198861842508856839)
  ·
    refine ⟨108625920298292763763285259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72417280198861842508856839 108625920298292763763285259)
    ·
      refine ⟨162938880447439145644927889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108625920298292763763285259 162938880447439145644927889)
      ·
        refine ⟨122204160335579359233695917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162938880447439145644927889 122204160335579359233695917)
        ·
          refine ⟨45826560125842259712635969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122204160335579359233695917 45826560125842259712635969)
          ·
            refine ⟨34369920094381694784476977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45826560125842259712635969 34369920094381694784476977)
            ·
              refine ⟨25777440070786271088357733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34369920094381694784476977 25777440070786271088357733)
              ·
                refine ⟨4833270013272425829067075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25777440070786271088357733 4833270013272425829067075)
                ·
                  refine ⟨7249905019908638743600613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833270013272425829067075 7249905019908638743600613)
                  ·
                    refine ⟨1359357191232869764425115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7249905019908638743600613 1359357191232869764425115)
                    ·
                      rfl

theorem cell22_3971008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_3971008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971008 prefixEnd_3971008 := by exact prefixLift 3971008
  have htrace : WordTrace (prefixWord ++ tailWord_3971008) baseStart_3971008 baseEnd_3971008 := by
    simpa [prefixWord, tailWord_3971008, baseEnd_3971008] using wordTrace_append hprefix tailTrace_3971008
  have hstable : (prefixWord ++ tailWord_3971008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971008).length < 2 ^ (prefixWord ++ tailWord_3971008).sum := by decide
  have hdescent : baseEnd_3971008 < baseStart_3971008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971070 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3971070 : Nat := 118140960795 + 3971070 * 2 ^ 59
def prefixEnd_3971070 : Nat := 4983230072969 + 3 ^ 40 * 3971070 * 2
def baseEnd_3971070 : Nat := 1359378415099922269374925

theorem tailTrace_3971070 : CollatzResearch.WordTrace tailWord_3971070 prefixEnd_3971070 1359378415099922269374925 := by
  unfold tailWord_3971070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18104602715437383700808833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96557881148999379737647109 18104602715437383700808833)
  ·
    refine ⟨13578452036578037775606625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18104602715437383700808833 13578452036578037775606625)
    ·
      refine ⟨10183839027433528331704969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13578452036578037775606625 10183839027433528331704969)
      ·
        refine ⟨7637879270575146248778727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10183839027433528331704969 7637879270575146248778727)
        ·
          refine ⟨11456818905862719373168091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7637879270575146248778727 11456818905862719373168091)
          ·
            refine ⟨17185228358794079059752137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456818905862719373168091 17185228358794079059752137)
            ·
              refine ⟨12888921269095559294814103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17185228358794079059752137 12888921269095559294814103)
              ·
                refine ⟨19333381903643338942221155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12888921269095559294814103 19333381903643338942221155)
                ·
                  refine ⟨29000072855465008413331733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19333381903643338942221155 29000072855465008413331733)
                  ·
                    refine ⟨1359378415099922269374925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29000072855465008413331733 1359378415099922269374925)
                    ·
                      rfl

theorem cell22_3971070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3971070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971070 prefixEnd_3971070 := by exact prefixLift 3971070
  have htrace : WordTrace (prefixWord ++ tailWord_3971070) baseStart_3971070 baseEnd_3971070 := by
    simpa [prefixWord, tailWord_3971070, baseEnd_3971070] using wordTrace_append hprefix tailTrace_3971070
  have hstable : (prefixWord ++ tailWord_3971070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971070).length < 2 ^ (prefixWord ++ tailWord_3971070).sum := by decide
  have hdescent : baseEnd_3971070 < baseStart_3971070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971081 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_3971081 : Nat := 118140960795 + 3971081 * 2 ^ 59
def prefixEnd_3971081 : Nat := 4983230072969 + 3 ^ 40 * 3971081 * 2
def baseEnd_3971081 : Nat := 1359382180624721907349891

theorem tailTrace_3971081 : CollatzResearch.WordTrace tailWord_3971081 prefixEnd_3971081 1359382180624721907349891 := by
  unfold tailWord_3971081
  simp only [CollatzResearch.WordTrace]
  refine ⟨144837222926459218485121097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96558148617639478990080731 144837222926459218485121097)
  ·
    refine ⟨108627917194844413863840823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144837222926459218485121097 108627917194844413863840823)
    ·
      refine ⟨162941875792266620795761235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108627917194844413863840823 162941875792266620795761235)
      ·
        refine ⟨244412813688399931193641853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162941875792266620795761235 244412813688399931193641853)
        ·
          refine ⟨91654805133149974197615695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244412813688399931193641853 91654805133149974197615695)
          ·
            refine ⟨137482207699724961296423543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91654805133149974197615695 137482207699724961296423543)
            ·
              refine ⟨206223311549587441944635315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137482207699724961296423543 206223311549587441944635315)
              ·
                refine ⟨309334967324381162916952973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206223311549587441944635315 309334967324381162916952973)
                ·
                  refine ⟨116000612746642936093857365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309334967324381162916952973 116000612746642936093857365)
                  ·
                    refine ⟨1359382180624721907349891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116000612746642936093857365 1359382180624721907349891)
                    ·
                      rfl

theorem cell22_3971081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_3971081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971081 prefixEnd_3971081 := by exact prefixLift 3971081
  have htrace : WordTrace (prefixWord ++ tailWord_3971081) baseStart_3971081 baseEnd_3971081 := by
    simpa [prefixWord, tailWord_3971081, baseEnd_3971081] using wordTrace_append hprefix tailTrace_3971081
  have hstable : (prefixWord ++ tailWord_3971081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971081).length < 2 ^ (prefixWord ++ tailWord_3971081).sum := by decide
  have hdescent : baseEnd_3971081 < baseStart_3971081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971203 : List Nat := [1, 1, 1, 3, 3, 4, 9]
def baseStart_3971203 : Nat := 118140960795 + 3971203 * 2 ^ 59
def prefixEnd_3971203 : Nat := 4983230072969 + 3 ^ 40 * 3971203 * 2
def baseEnd_3971203 : Nat := 50349034952516824288871

theorem tailTrace_3971203 : CollatzResearch.WordTrace tailWord_3971203 prefixEnd_3971203 50349034952516824288871 := by
  unfold tailWord_3971203
  simp only [CollatzResearch.WordTrace]
  refine ⟨144841672632017233321062263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96561115088011488880708175 144841672632017233321062263)
  ·
    refine ⟨217262508948025849981593395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144841672632017233321062263 217262508948025849981593395)
    ·
      refine ⟨325893763422038774972390093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217262508948025849981593395 325893763422038774972390093)
      ·
        refine ⟨122210161283264540614646285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325893763422038774972390093 122210161283264540614646285)
        ·
          refine ⟨45828810481224202730492357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122210161283264540614646285 45828810481224202730492357)
          ·
            refine ⟨8592901965229538011967317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45828810481224202730492357 8592901965229538011967317)
            ·
              refine ⟨50349034952516824288871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8592901965229538011967317 50349034952516824288871)
              ·
                rfl

theorem cell22_3971203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 9].length) (baseStart_3971203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971203 prefixEnd_3971203 := by exact prefixLift 3971203
  have htrace : WordTrace (prefixWord ++ tailWord_3971203) baseStart_3971203 baseEnd_3971203 := by
    simpa [prefixWord, tailWord_3971203, baseEnd_3971203] using wordTrace_append hprefix tailTrace_3971203
  have hstable : (prefixWord ++ tailWord_3971203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971203).length < 2 ^ (prefixWord ++ tailWord_3971203).sum := by decide
  have hdescent : baseEnd_3971203 < baseStart_3971203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971207 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 2, 3]
def baseStart_3971207 : Nat := 118140960795 + 3971207 * 2 ^ 59
def prefixEnd_3971207 : Nat := 4983230072969 + 3 ^ 40 * 3971207 * 2
def baseEnd_3971207 : Nat := 1359425312999699578699505

theorem tailTrace_3971207 : CollatzResearch.WordTrace tailWord_3971207 prefixEnd_3971207 1359425312999699578699505 := by
  unfold tailWord_3971207
  simp only [CollatzResearch.WordTrace]
  refine ⟨144841818524002742004207875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96561212349335161336138583 144841818524002742004207875)
  ·
    refine ⟨217262727786004113006311813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144841818524002742004207875 217262727786004113006311813)
    ·
      refine ⟨40736761459875771188683465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217262727786004113006311813 40736761459875771188683465)
      ·
        refine ⟨30552571094906828391512599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40736761459875771188683465 30552571094906828391512599)
        ·
          refine ⟨45828856642360242587268899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30552571094906828391512599 45828856642360242587268899)
          ·
            refine ⟨68743284963540363880903349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45828856642360242587268899 68743284963540363880903349)
            ·
              refine ⟨6444682965331909113834689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68743284963540363880903349 6444682965331909113834689)
              ·
                refine ⟨4833512223998931835376017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444682965331909113834689 4833512223998931835376017)
                ·
                  refine ⟨3625134167999198876532013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833512223998931835376017 3625134167999198876532013)
                  ·
                    refine ⟨1359425312999699578699505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3625134167999198876532013 1359425312999699578699505)
                    ·
                      rfl

theorem cell22_3971207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_3971207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971207 prefixEnd_3971207 := by exact prefixLift 3971207
  have htrace : WordTrace (prefixWord ++ tailWord_3971207) baseStart_3971207 baseEnd_3971207 := by
    simpa [prefixWord, tailWord_3971207, baseEnd_3971207] using wordTrace_append hprefix tailTrace_3971207
  have hstable : (prefixWord ++ tailWord_3971207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971207).length < 2 ^ (prefixWord ++ tailWord_3971207).sum := by decide
  have hdescent : baseEnd_3971207 < baseStart_3971207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971224 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 1, 5]
def baseStart_3971224 : Nat := 118140960795 + 3971224 * 2 ^ 59
def prefixEnd_3971224 : Nat := 4983230072969 + 3 ^ 40 * 3971224 * 2
def baseEnd_3971224 : Nat := 1359431132447117201024453

theorem tailTrace_3971224 : CollatzResearch.WordTrace tailWord_3971224 prefixEnd_3971224 1359431132447117201024453 := by
  unfold tailWord_3971224
  simp only [CollatzResearch.WordTrace]
  refine ⟨72421219282470576953788363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96561625709960769271717817 72421219282470576953788363)
  ·
    refine ⟨108631828923705865430682545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72421219282470576953788363 108631828923705865430682545)
    ·
      refine ⟨81473871692779399073011909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108631828923705865430682545 81473871692779399073011909)
      ·
        refine ⟨15276350942396137326189733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81473871692779399073011909 15276350942396137326189733)
        ·
          refine ⟨2864315801699275748660575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15276350942396137326189733 2864315801699275748660575)
          ·
            refine ⟨4296473702548913622990863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864315801699275748660575 4296473702548913622990863)
            ·
              refine ⟨6444710553823370434486295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296473702548913622990863 6444710553823370434486295)
              ·
                refine ⟨9667065830735055651729443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444710553823370434486295 9667065830735055651729443)
                ·
                  refine ⟨14500598746102583477594165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667065830735055651729443 14500598746102583477594165)
                  ·
                    refine ⟨1359431132447117201024453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14500598746102583477594165 1359431132447117201024453)
                    ·
                      rfl

theorem cell22_3971224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_3971224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971224 prefixEnd_3971224 := by exact prefixLift 3971224
  have htrace : WordTrace (prefixWord ++ tailWord_3971224) baseStart_3971224 baseEnd_3971224 := by
    simpa [prefixWord, tailWord_3971224, baseEnd_3971224] using wordTrace_append hprefix tailTrace_3971224
  have hstable : (prefixWord ++ tailWord_3971224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971224).length < 2 ^ (prefixWord ++ tailWord_3971224).sum := by decide
  have hdescent : baseEnd_3971224 < baseStart_3971224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971282 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_3971282 : Nat := 118140960795 + 3971282 * 2 ^ 59
def prefixEnd_3971282 : Nat := 4983230072969 + 3 ^ 40 * 3971282 * 2
def baseEnd_3971282 : Nat := 453150329010808127691425

theorem tailTrace_3971282 : CollatzResearch.WordTrace tailWord_3971282 prefixEnd_3971282 453150329010808127691425 := by
  unfold tailWord_3971282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36211138499682757453297025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96563035999154019875458733 36211138499682757453297025)
  ·
    refine ⟨27158353874762068089972769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36211138499682757453297025 27158353874762068089972769)
    ·
      refine ⟨20368765406071551067479577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27158353874762068089972769 20368765406071551067479577)
      ·
        refine ⟨15276574054553663300609683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20368765406071551067479577 15276574054553663300609683)
        ·
          refine ⟨22914861081830494950914525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15276574054553663300609683 22914861081830494950914525)
          ·
            refine ⟨8593072905686435606592947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22914861081830494950914525 8593072905686435606592947)
            ·
              refine ⟨12889609358529653409889421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8593072905686435606592947 12889609358529653409889421)
              ·
                refine ⟨4833603509448620028708533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12889609358529653409889421 4833603509448620028708533)
                ·
                  refine ⟨453150329010808127691425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4833603509448620028708533 453150329010808127691425)
                  ·
                    rfl

theorem cell22_3971282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_3971282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971282 prefixEnd_3971282 := by exact prefixLift 3971282
  have htrace : WordTrace (prefixWord ++ tailWord_3971282) baseStart_3971282 baseEnd_3971282 := by
    simpa [prefixWord, tailWord_3971282, baseEnd_3971282] using wordTrace_append hprefix tailTrace_3971282
  have hstable : (prefixWord ++ tailWord_3971282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971282).length < 2 ^ (prefixWord ++ tailWord_3971282).sum := by decide
  have hdescent : baseEnd_3971282 < baseStart_3971282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971327 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 4]
def baseStart_3971327 : Nat := 118140960795 + 3971327 * 2 ^ 59
def prefixEnd_3971327 : Nat := 4983230072969 + 3 ^ 40 * 3971327 * 2
def baseEnd_3971327 : Nat := 453155463817353088566379

theorem tailTrace_3971327 : CollatzResearch.WordTrace tailWord_3971327 prefixEnd_3971327 453155463817353088566379 := by
  unfold tailWord_3971327
  simp only [CollatzResearch.WordTrace]
  refine ⟨144846195283568002498576235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96564130189045334999050823 144846195283568002498576235)
  ·
    refine ⟨217269292925352003747864353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144846195283568002498576235 217269292925352003747864353)
    ·
      refine ⟨162951969694014002810898265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217269292925352003747864353 162951969694014002810898265)
      ·
        refine ⟨122213977270510502108173699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162951969694014002810898265 122213977270510502108173699)
        ·
          refine ⟨183320965905765753162260549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122213977270510502108173699 183320965905765753162260549)
          ·
            refine ⟨34372681107331078717923853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183320965905765753162260549 34372681107331078717923853)
            ·
              refine ⟨12889755415249154519221445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34372681107331078717923853 12889755415249154519221445)
              ·
                refine ⟨2416829140359216472354021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12889755415249154519221445 2416829140359216472354021)
                ·
                  refine ⟨453155463817353088566379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2416829140359216472354021 453155463817353088566379)
                  ·
                    rfl

theorem cell22_3971327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 4].length) (baseStart_3971327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971327 prefixEnd_3971327 := by exact prefixLift 3971327
  have htrace : WordTrace (prefixWord ++ tailWord_3971327) baseStart_3971327 baseEnd_3971327 := by
    simpa [prefixWord, tailWord_3971327, baseEnd_3971327] using wordTrace_append hprefix tailTrace_3971327
  have hstable : (prefixWord ++ tailWord_3971327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971327).length < 2 ^ (prefixWord ++ tailWord_3971327).sum := by decide
  have hdescent : baseEnd_3971327 < baseStart_3971327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971340 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_3971340 : Nat := 118140960795 + 3971340 * 2 ^ 59
def prefixEnd_3971340 : Nat := 4983230072969 + 3 ^ 40 * 3971340 * 2
def baseEnd_3971340 : Nat := 1359470841617731565124097

theorem tailTrace_3971340 : CollatzResearch.WordTrace tailWord_3971340 prefixEnd_3971340 1359470841617731565124097 := by
  unfold tailWord_3971340
  simp only [CollatzResearch.WordTrace]
  refine ⟨72423334716260452859399737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96564446288347270479199649 72423334716260452859399737)
  ·
    refine ⟨54317501037195339644549803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72423334716260452859399737 54317501037195339644549803)
    ·
      refine ⟨81476251555793009466824705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54317501037195339644549803 81476251555793009466824705)
      ·
        refine ⟨61107188666844757100118529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81476251555793009466824705 61107188666844757100118529)
        ·
          refine ⟨45830391500133567825088897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61107188666844757100118529 45830391500133567825088897)
          ·
            refine ⟨34372793625100175868816673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45830391500133567825088897 34372793625100175868816673)
            ·
              refine ⟨25779595218825131901612505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34372793625100175868816673 25779595218825131901612505)
              ·
                refine ⟨19334696414118848926209379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25779595218825131901612505 19334696414118848926209379)
                ·
                  refine ⟨29002044621178273389314069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19334696414118848926209379 29002044621178273389314069)
                  ·
                    refine ⟨1359470841617731565124097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29002044621178273389314069 1359470841617731565124097)
                    ·
                      rfl

theorem cell22_3971340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_3971340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971340 prefixEnd_3971340 := by exact prefixLift 3971340
  have htrace : WordTrace (prefixWord ++ tailWord_3971340) baseStart_3971340 baseEnd_3971340 := by
    simpa [prefixWord, tailWord_3971340, baseEnd_3971340] using wordTrace_append hprefix tailTrace_3971340
  have hstable : (prefixWord ++ tailWord_3971340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971340).length < 2 ^ (prefixWord ++ tailWord_3971340).sum := by decide
  have hdescent : baseEnd_3971340 < baseStart_3971340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971342 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_3971342 : Nat := 118140960795 + 3971342 * 2 ^ 59
def prefixEnd_3971342 : Nat := 4983230072969 + 3 ^ 40 * 3971342 * 2
def baseEnd_3971342 : Nat := 1359471526258604226574091

theorem tailTrace_3971342 : CollatzResearch.WordTrace tailWord_3971342 prefixEnd_3971342 1359471526258604226574091 := by
  unfold tailWord_3971342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105842797314207507546535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96564494919009106706914853 18105842797314207507546535)
  ·
    refine ⟨27158764195971311261319803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18105842797314207507546535 27158764195971311261319803)
    ·
      refine ⟨40738146293956966891979705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27158764195971311261319803 40738146293956966891979705)
      ·
        refine ⟨30553609720467725168984779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40738146293956966891979705 30553609720467725168984779)
        ·
          refine ⟨45830414580701587753477169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30553609720467725168984779 45830414580701587753477169)
          ·
            refine ⟨34372810935526190815107877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45830414580701587753477169 34372810935526190815107877)
            ·
              refine ⟨6444902050411160777832727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34372810935526190815107877 6444902050411160777832727)
              ·
                refine ⟨9667353075616741166749091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444902050411160777832727 9667353075616741166749091)
                ·
                  refine ⟨14501029613425111750123637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9667353075616741166749091 14501029613425111750123637)
                  ·
                    refine ⟨1359471526258604226574091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14501029613425111750123637 1359471526258604226574091)
                    ·
                      rfl

theorem cell22_3971342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_3971342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971342 prefixEnd_3971342 := by exact prefixLift 3971342
  have htrace : WordTrace (prefixWord ++ tailWord_3971342) baseStart_3971342 baseEnd_3971342 := by
    simpa [prefixWord, tailWord_3971342, baseEnd_3971342] using wordTrace_append hprefix tailTrace_3971342
  have hstable : (prefixWord ++ tailWord_3971342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971342).length < 2 ^ (prefixWord ++ tailWord_3971342).sum := by decide
  have hdescent : baseEnd_3971342 < baseStart_3971342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971393 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3971393 : Nat := 118140960795 + 3971393 * 2 ^ 59
def prefixEnd_3971393 : Nat := 4983230072969 + 3 ^ 40 * 3971393 * 2
def baseEnd_3971393 : Nat := 1359488984600857093548935

theorem tailTrace_3971393 : CollatzResearch.WordTrace tailWord_3971393 prefixEnd_3971393 1359488984600857093548935 := by
  unfold tailWord_3971393
  simp only [CollatzResearch.WordTrace]
  refine ⟨144848602501328895770478833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96565735000885930513652555 144848602501328895770478833)
  ·
    refine ⟨108636451875996671827859125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144848602501328895770478833 108636451875996671827859125)
    ·
      refine ⟨10184667363374687983861793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108636451875996671827859125 10184667363374687983861793)
      ·
        refine ⟨7638500522531015987896345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10184667363374687983861793 7638500522531015987896345)
        ·
          refine ⟨5728875391898261990922259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7638500522531015987896345 5728875391898261990922259)
          ·
            refine ⟨8593313087847392986383389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728875391898261990922259 8593313087847392986383389)
            ·
              refine ⟨3222492407942772369893771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8593313087847392986383389 3222492407942772369893771)
              ·
                refine ⟨4833738611914158554840657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222492407942772369893771 4833738611914158554840657)
                ·
                  refine ⟨3625303958935618916130493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833738611914158554840657 3625303958935618916130493)
                  ·
                    refine ⟨1359488984600857093548935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3625303958935618916130493 1359488984600857093548935)
                    ·
                      rfl

theorem cell22_3971393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3971393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971393 prefixEnd_3971393 := by exact prefixLift 3971393
  have htrace : WordTrace (prefixWord ++ tailWord_3971393) baseStart_3971393 baseEnd_3971393 := by
    simpa [prefixWord, tailWord_3971393, baseEnd_3971393] using wordTrace_append hprefix tailTrace_3971393
  have hstable : (prefixWord ++ tailWord_3971393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971393).length < 2 ^ (prefixWord ++ tailWord_3971393).sum := by decide
  have hdescent : baseEnd_3971393 < baseStart_3971393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971552 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_3971552 : Nat := 118140960795 + 3971552 * 2 ^ 59
def prefixEnd_3971552 : Nat := 4983230072969 + 3 ^ 40 * 3971552 * 2
def baseEnd_3971552 : Nat := 453181137850077892941149

theorem tailTrace_3971552 : CollatzResearch.WordTrace tailWord_3971552 prefixEnd_3971552 453181137850077892941149 := by
  unfold tailWord_3971552
  simp only [CollatzResearch.WordTrace]
  refine ⟨72427200853876432962758455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96569601138501910617011273 72427200853876432962758455)
  ·
    refine ⟨108640801280814649444137683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72427200853876432962758455 108640801280814649444137683)
    ·
      refine ⟨162961201921221974166206525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108640801280814649444137683 162961201921221974166206525)
      ·
        refine ⟨61110450720458240312327447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162961201921221974166206525 61110450720458240312327447)
        ·
          refine ⟨91665676080687360468491171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61110450720458240312327447 91665676080687360468491171)
          ·
            refine ⟨137498514121031040702736757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91665676080687360468491171 137498514121031040702736757)
            ·
              refine ⟨12890485698846660065881571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137498514121031040702736757 12890485698846660065881571)
              ·
                refine ⟨19335728548269990098822357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12890485698846660065881571 19335728548269990098822357)
                ·
                  refine ⟨453181137850077892941149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19335728548269990098822357 453181137850077892941149)
                  ·
                    rfl

theorem cell22_3971552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_3971552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971552 prefixEnd_3971552 := by exact prefixLift 3971552
  have htrace : WordTrace (prefixWord ++ tailWord_3971552) baseStart_3971552 baseEnd_3971552 := by
    simpa [prefixWord, tailWord_3971552, baseEnd_3971552] using wordTrace_append hprefix tailTrace_3971552
  have hstable : (prefixWord ++ tailWord_3971552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971552).length < 2 ^ (prefixWord ++ tailWord_3971552).sum := by decide
  have hdescent : baseEnd_3971552 < baseStart_3971552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971607 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 1, 3]
def baseStart_3971607 : Nat := 118140960795 + 3971607 * 2 ^ 59
def prefixEnd_3971607 : Nat := 4983230072969 + 3 ^ 40 * 3971607 * 2
def baseEnd_3971607 : Nat := 1359562241174231868698279

theorem tailTrace_3971607 : CollatzResearch.WordTrace tailWord_3971607 prefixEnd_3971607 1359562241174231868698279 := by
  unfold tailWord_3971607
  simp only [CollatzResearch.WordTrace]
  refine ⟨144856407722553610318769075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96570938481702406879179383 144856407722553610318769075)
  ·
    refine ⟨217284611583830415478153613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144856407722553610318769075 217284611583830415478153613)
    ·
      refine ⟨81481729343936405804307605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217284611583830415478153613 81481729343936405804307605)
      ·
        refine ⟨3819456062997019022076919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81481729343936405804307605 3819456062997019022076919)
        ·
          refine ⟨5729184094495528533115379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819456062997019022076919 5729184094495528533115379)
          ·
            refine ⟨8593776141743292799673069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5729184094495528533115379 8593776141743292799673069)
            ·
              refine ⟨3222666053153734799877401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8593776141743292799673069 3222666053153734799877401)
              ·
                refine ⟨2416999539865301099908051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222666053153734799877401 2416999539865301099908051)
                ·
                  refine ⟨3625499309797951649862077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416999539865301099908051 3625499309797951649862077)
                  ·
                    refine ⟨1359562241174231868698279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3625499309797951649862077 1359562241174231868698279)
                    ·
                      rfl

theorem cell22_3971607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_3971607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971607 prefixEnd_3971607 := by exact prefixLift 3971607
  have htrace : WordTrace (prefixWord ++ tailWord_3971607) baseStart_3971607 baseEnd_3971607 := by
    simpa [prefixWord, tailWord_3971607, baseEnd_3971607] using wordTrace_append hprefix tailTrace_3971607
  have hstable : (prefixWord ++ tailWord_3971607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971607).length < 2 ^ (prefixWord ++ tailWord_3971607).sum := by decide
  have hdescent : baseEnd_3971607 < baseStart_3971607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971620 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_3971620 : Nat := 118140960795 + 3971620 * 2 ^ 59
def prefixEnd_3971620 : Nat := 4983230072969 + 3 ^ 40 * 3971620 * 2
def baseEnd_3971620 : Nat := 453188897113301389374413

theorem tailTrace_3971620 : CollatzResearch.WordTrace tailWord_3971620 prefixEnd_3971620 453188897113301389374413 := by
  unfold tailWord_3971620
  simp only [CollatzResearch.WordTrace]
  refine ⟨72428440935753256769496157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96571254581004342359328209 72428440935753256769496157)
  ·
    refine ⟨27160665350907471288561059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72428440935753256769496157 27160665350907471288561059)
    ·
      refine ⟨40740998026361206932841589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27160665350907471288561059 40740998026361206932841589)
      ·
        refine ⟨3819468564971363149953899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40740998026361206932841589 3819468564971363149953899)
        ·
          refine ⟨5729202847457044724930849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819468564971363149953899 5729202847457044724930849)
          ·
            refine ⟨4296902135592783543698137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5729202847457044724930849 4296902135592783543698137)
            ·
              refine ⟨3222676601694587657773603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296902135592783543698137 3222676601694587657773603)
              ·
                refine ⟨4834014902541881486660405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222676601694587657773603 4834014902541881486660405)
                ·
                  refine ⟨453188897113301389374413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4834014902541881486660405 453188897113301389374413)
                  ·
                    rfl

theorem cell22_3971620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_3971620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971620 prefixEnd_3971620 := by exact prefixLift 3971620
  have htrace : WordTrace (prefixWord ++ tailWord_3971620) baseStart_3971620 baseEnd_3971620 := by
    simpa [prefixWord, tailWord_3971620, baseEnd_3971620] using wordTrace_append hprefix tailTrace_3971620
  have hstable : (prefixWord ++ tailWord_3971620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971620).length < 2 ^ (prefixWord ++ tailWord_3971620).sum := by decide
  have hdescent : baseEnd_3971620 < baseStart_3971620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971627 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_3971627 : Nat := 118140960795 + 3971627 * 2 ^ 59
def prefixEnd_3971627 : Nat := 4983230072969 + 3 ^ 40 * 3971627 * 2
def baseEnd_3971627 : Nat := 1359569087582958483198217

theorem tailTrace_3971627 : CollatzResearch.WordTrace tailWord_3971627 prefixEnd_3971627 1359569087582958483198217 := by
  unfold tailWord_3971627
  simp only [CollatzResearch.WordTrace]
  refine ⟨144857137182481153734497135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96571424788320769156331423 144857137182481153734497135)
  ·
    refine ⟨217285705773721730601745703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144857137182481153734497135 217285705773721730601745703)
    ·
      refine ⟨325928558660582595902618555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217285705773721730601745703 325928558660582595902618555)
      ·
        refine ⟨488892837990873893853927833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325928558660582595902618555 488892837990873893853927833)
        ·
          refine ⟨366669628493155420390445875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488892837990873893853927833 366669628493155420390445875)
          ·
            refine ⟨550004442739733130585668813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366669628493155420390445875 550004442739733130585668813)
            ·
              refine ⟨206251666027399923969625805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550004442739733130585668813 206251666027399923969625805)
              ·
                refine ⟨77344374760274971488609677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206251666027399923969625805 77344374760274971488609677)
                ·
                  refine ⟨29004140535103114308228629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77344374760274971488609677 29004140535103114308228629)
                  ·
                    refine ⟨1359569087582958483198217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29004140535103114308228629 1359569087582958483198217)
                    ·
                      rfl

theorem cell22_3971627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_3971627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971627 prefixEnd_3971627 := by exact prefixLift 3971627
  have htrace : WordTrace (prefixWord ++ tailWord_3971627) baseStart_3971627 baseEnd_3971627 := by
    simpa [prefixWord, tailWord_3971627, baseEnd_3971627] using wordTrace_append hprefix tailTrace_3971627
  have hstable : (prefixWord ++ tailWord_3971627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971627).length < 2 ^ (prefixWord ++ tailWord_3971627).sum := by decide
  have hdescent : baseEnd_3971627 < baseStart_3971627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971708 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 1, 3]
def baseStart_3971708 : Nat := 118140960795 + 3971708 * 2 ^ 59
def prefixEnd_3971708 : Nat := 4983230072969 + 3 ^ 40 * 3971708 * 2
def baseEnd_3971708 : Nat := 1359596815538301271922969

theorem tailTrace_3971708 : CollatzResearch.WordTrace tailWord_3971708 prefixEnd_3971708 1359596815538301271922969 := by
  unfold tailWord_3971708
  simp only [CollatzResearch.WordTrace]
  refine ⟨72430045747593852284097889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96573394330125136378797185 72430045747593852284097889)
  ·
    refine ⟨54322534310695389213073417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72430045747593852284097889 54322534310695389213073417)
    ·
      refine ⟨40741900733021541909805063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54322534310695389213073417 40741900733021541909805063)
      ·
        refine ⟨61112851099532312864707595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40741900733021541909805063 61112851099532312864707595)
        ·
          refine ⟨91669276649298469297061393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61112851099532312864707595 91669276649298469297061393)
          ·
            refine ⟨68751957486973851972796045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91669276649298469297061393 68751957486973851972796045)
            ·
              refine ⟨25781984057615194489798517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68751957486973851972796045 25781984057615194489798517)
              ·
                refine ⟨2417061005401424483418611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25781984057615194489798517 2417061005401424483418611)
                ·
                  refine ⟨3625591508102136725127917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417061005401424483418611 3625591508102136725127917)
                  ·
                    refine ⟨1359596815538301271922969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3625591508102136725127917 1359596815538301271922969)
                    ·
                      rfl

theorem cell22_3971708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_3971708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971708 prefixEnd_3971708 := by exact prefixLift 3971708
  have htrace : WordTrace (prefixWord ++ tailWord_3971708) baseStart_3971708 baseEnd_3971708 := by
    simpa [prefixWord, tailWord_3971708, baseEnd_3971708] using wordTrace_append hprefix tailTrace_3971708
  have hstable : (prefixWord ++ tailWord_3971708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971708).length < 2 ^ (prefixWord ++ tailWord_3971708).sum := by decide
  have hdescent : baseEnd_3971708 < baseStart_3971708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971719 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3971719 : Nat := 118140960795 + 3971719 * 2 ^ 59
def prefixEnd_3971719 : Nat := 4983230072969 + 3 ^ 40 * 3971719 * 2
def baseEnd_3971719 : Nat := 1359600581063100909897935

theorem tailTrace_3971719 : CollatzResearch.WordTrace tailWord_3971719 prefixEnd_3971719 1359600581063100909897935 := by
  unfold tailWord_3971719
  simp only [CollatzResearch.WordTrace]
  refine ⟨144860492698147853446846211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96573661798765235631230807 144860492698147853446846211)
  ·
    refine ⟨217290739047221780170269317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144860492698147853446846211 217290739047221780170269317)
    ·
      refine ⟨40742013571354083781925497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217290739047221780170269317 40742013571354083781925497)
      ·
        refine ⟨30556510178515562836444123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40742013571354083781925497 30556510178515562836444123)
        ·
          refine ⟨45834765267773344254666185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30556510178515562836444123 45834765267773344254666185)
          ·
            refine ⟨34376073950830008190999639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45834765267773344254666185 34376073950830008190999639)
            ·
              refine ⟨51564110926245012286499459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34376073950830008190999639 51564110926245012286499459)
              ·
                refine ⟨77346166389367518429749189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51564110926245012286499459 77346166389367518429749189)
                ·
                  refine ⟨14502406198006409705577973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77346166389367518429749189 14502406198006409705577973)
                  ·
                    refine ⟨1359600581063100909897935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14502406198006409705577973 1359600581063100909897935)
                    ·
                      rfl

theorem cell22_3971719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3971719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971719 prefixEnd_3971719 := by exact prefixLift 3971719
  have htrace : WordTrace (prefixWord ++ tailWord_3971719) baseStart_3971719 baseEnd_3971719 := by
    simpa [prefixWord, tailWord_3971719, baseEnd_3971719] using wordTrace_append hprefix tailTrace_3971719
  have hstable : (prefixWord ++ tailWord_3971719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971719).length < 2 ^ (prefixWord ++ tailWord_3971719).sum := by decide
  have hdescent : baseEnd_3971719 < baseStart_3971719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971789 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3971789 : Nat := 118140960795 + 3971789 * 2 ^ 59
def prefixEnd_3971789 : Nat := 4983230072969 + 3 ^ 40 * 3971789 * 2
def baseEnd_3971789 : Nat := 453208181164548020215907

theorem tailTrace_3971789 : CollatzResearch.WordTrace tailWord_3971789 prefixEnd_3971789 453208181164548020215907 := by
  unfold tailWord_3971789
  simp only [CollatzResearch.WordTrace]
  refine ⟨144863045807894255401894421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96575363871929503601262947 144863045807894255401894421)
  ·
    refine ⟨6790455272245043221963801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144863045807894255401894421 6790455272245043221963801)
    ·
      refine ⟨5092841454183782416472851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6790455272245043221963801 5092841454183782416472851)
      ·
        refine ⟨7639262181275673624709277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092841454183782416472851 7639262181275673624709277)
        ·
          refine ⟨2864723317978377609265979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7639262181275673624709277 2864723317978377609265979)
          ·
            refine ⟨4297084976967566413898969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864723317978377609265979 4297084976967566413898969)
            ·
              refine ⟨3222813732725674810424227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297084976967566413898969 3222813732725674810424227)
              ·
                refine ⟨4834220599088512215636341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222813732725674810424227 4834220599088512215636341)
                ·
                  refine ⟨453208181164548020215907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4834220599088512215636341 453208181164548020215907)
                  ·
                    rfl

theorem cell22_3971789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3971789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971789 prefixEnd_3971789 := by exact prefixLift 3971789
  have htrace : WordTrace (prefixWord ++ tailWord_3971789) baseStart_3971789 baseEnd_3971789 := by
    simpa [prefixWord, tailWord_3971789, baseEnd_3971789] using wordTrace_append hprefix tailTrace_3971789
  have hstable : (prefixWord ++ tailWord_3971789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971789).length < 2 ^ (prefixWord ++ tailWord_3971789).sum := by decide
  have hdescent : baseEnd_3971789 < baseStart_3971789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971811 : List Nat := [1, 1, 1, 7, 1, 1, 2, 8]
def baseStart_3971811 : Nat := 118140960795 + 3971811 * 2 ^ 59
def prefixEnd_3971811 : Nat := 4983230072969 + 3 ^ 40 * 3971811 * 2
def baseEnd_3971811 : Nat := 151070230504804815177517

theorem tailTrace_3971811 : CollatzResearch.WordTrace tailWord_3971811 prefixEnd_3971811 151070230504804815177517 := by
  unfold tailWord_3971811
  simp only [CollatzResearch.WordTrace]
  refine ⟨144863848213814553159195287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96575898809209702106130191 144863848213814553159195287)
  ·
    refine ⟨217295772320721829738792931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144863848213814553159195287 217295772320721829738792931)
    ·
      refine ⟨325943658481082744608189397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217295772320721829738792931 325943658481082744608189397)
      ·
        refine ⟨7639304495650376826754439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 325943658481082744608189397 7639304495650376826754439)
        ·
          refine ⟨11458956743475565240131659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639304495650376826754439 11458956743475565240131659)
          ·
            refine ⟨17188435115213347860197489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458956743475565240131659 17188435115213347860197489)
            ·
              refine ⟨12891326336410010895148117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17188435115213347860197489 12891326336410010895148117)
              ·
                refine ⟨151070230504804815177517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12891326336410010895148117 151070230504804815177517)
                ·
                  rfl

theorem cell22_3971811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 8].length) (baseStart_3971811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971811 prefixEnd_3971811 := by exact prefixLift 3971811
  have htrace : WordTrace (prefixWord ++ tailWord_3971811) baseStart_3971811 baseEnd_3971811 := by
    simpa [prefixWord, tailWord_3971811, baseEnd_3971811] using wordTrace_append hprefix tailTrace_3971811
  have hstable : (prefixWord ++ tailWord_3971811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971811).length < 2 ^ (prefixWord ++ tailWord_3971811).sum := by decide
  have hdescent : baseEnd_3971811 < baseStart_3971811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971813 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_3971813 : Nat := 118140960795 + 3971813 * 2 ^ 59
def prefixEnd_3971813 : Nat := 4983230072969 + 3 ^ 40 * 3971813 * 2
def baseEnd_3971813 : Nat := 1359632759184115998047647

theorem tailTrace_3971813 : CollatzResearch.WordTrace tailWord_3971813 prefixEnd_3971813 1359632759184115998047647 := by
  unfold tailWord_3971813
  simp only [CollatzResearch.WordTrace]
  refine ⟨144863921159807307500768093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96575947439871538333845395 144863921159807307500768093)
  ·
    refine ⟨54323970434927740312788035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144863921159807307500768093 54323970434927740312788035)
    ·
      refine ⟨81485955652391610469182053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54323970434927740312788035 81485955652391610469182053)
      ·
        refine ⟨15278616684823426962971635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81485955652391610469182053 15278616684823426962971635)
        ·
          refine ⟨22917925027235140444457453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15278616684823426962971635 22917925027235140444457453)
          ·
            refine ⟨8594221885213177666671545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22917925027235140444457453 8594221885213177666671545)
            ·
              refine ⟨6445666413909883250003659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594221885213177666671545 6445666413909883250003659)
              ·
                refine ⟨9668499620864824875005489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6445666413909883250003659 9668499620864824875005489)
                ·
                  refine ⟨7251374715648618656254117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668499620864824875005489 7251374715648618656254117)
                  ·
                    refine ⟨1359632759184115998047647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251374715648618656254117 1359632759184115998047647)
                    ·
                      rfl

theorem cell22_3971813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_3971813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971813 prefixEnd_3971813 := by exact prefixLift 3971813
  have htrace : WordTrace (prefixWord ++ tailWord_3971813) baseStart_3971813 baseEnd_3971813 := by
    simpa [prefixWord, tailWord_3971813, baseEnd_3971813] using wordTrace_append hprefix tailTrace_3971813
  have hstable : (prefixWord ++ tailWord_3971813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971813).length < 2 ^ (prefixWord ++ tailWord_3971813).sum := by decide
  have hdescent : baseEnd_3971813 < baseStart_3971813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971828 : List Nat := [2, 6, 1, 1, 12]
def baseStart_3971828 : Nat := 118140960795 + 3971828 * 2 ^ 59
def prefixEnd_3971828 : Nat := 4983230072969 + 3 ^ 40 * 3971828 * 2
def baseEnd_3971828 : Nat := 5595217670743460736307

theorem tailTrace_3971828 : CollatzResearch.WordTrace tailWord_3971828 prefixEnd_3971828 5595217670743460736307 := by
  unfold tailWord_3971828
  simp only [CollatzResearch.WordTrace]
  refine ⟨72432234127376482531282069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96576312169835310041709425 72432234127376482531282069)
  ·
    refine ⟨3395260974720772618653847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 72432234127376482531282069 3395260974720772618653847)
    ·
      refine ⟨5092891462081158927980771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395260974720772618653847 5092891462081158927980771)
      ·
        refine ⟨7639337193121738391971157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092891462081158927980771 7639337193121738391971157)
        ·
          refine ⟨5595217670743460736307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7639337193121738391971157 5595217670743460736307)
          ·
            rfl

theorem cell22_3971828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 12].length) (baseStart_3971828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971828 prefixEnd_3971828 := by exact prefixLift 3971828
  have htrace : WordTrace (prefixWord ++ tailWord_3971828) baseStart_3971828 baseEnd_3971828 := by
    simpa [prefixWord, tailWord_3971828, baseEnd_3971828] using wordTrace_append hprefix tailTrace_3971828
  have hstable : (prefixWord ++ tailWord_3971828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971828).length < 2 ^ (prefixWord ++ tailWord_3971828).sum := by decide
  have hdescent : baseEnd_3971828 < baseStart_3971828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3971948 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 2, 4]
def baseStart_3971948 : Nat := 118140960795 + 3971948 * 2 ^ 59
def prefixEnd_3971948 : Nat := 4983230072969 + 3 ^ 40 * 3971948 * 2
def baseEnd_3971948 : Nat := 1359678972443020645922233

theorem tailTrace_3971948 : CollatzResearch.WordTrace tailWord_3971948 prefixEnd_3971948 1359678972443020645922233 := by
  unfold tailWord_3971948
  simp only [CollatzResearch.WordTrace]
  refine ⟨72434422507159112778466249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96579230009545483704621665 72434422507159112778466249)
  ·
    refine ⟨54325816880369334583849687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72434422507159112778466249 54325816880369334583849687)
    ·
      refine ⟨81488725320554001875774531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54325816880369334583849687 81488725320554001875774531)
      ·
        refine ⟨122233087980831002813661797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81488725320554001875774531 122233087980831002813661797)
        ·
          refine ⟨22918703996405813027561587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122233087980831002813661797 22918703996405813027561587)
          ·
            refine ⟨34378055994608719541342381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22918703996405813027561587 34378055994608719541342381)
            ·
              refine ⟨12891770997978269828003393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34378055994608719541342381 12891770997978269828003393)
              ·
                refine ⟨9668828248483702371002545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12891770997978269828003393 9668828248483702371002545)
                ·
                  refine ⟨7251621186362776778251909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9668828248483702371002545 7251621186362776778251909)
                  ·
                    refine ⟨1359678972443020645922233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7251621186362776778251909 1359678972443020645922233)
                    ·
                      rfl

theorem cell22_3971948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_3971948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3971948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3971948 prefixEnd_3971948 := by exact prefixLift 3971948
  have htrace : WordTrace (prefixWord ++ tailWord_3971948) baseStart_3971948 baseEnd_3971948 := by
    simpa [prefixWord, tailWord_3971948, baseEnd_3971948] using wordTrace_append hprefix tailTrace_3971948
  have hstable : (prefixWord ++ tailWord_3971948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3971948).length < 2 ^ (prefixWord ++ tailWord_3971948).sum := by decide
  have hdescent : baseEnd_3971948 < baseStart_3971948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3971948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972205 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3972205 : Nat := 118140960795 + 3972205 * 2 ^ 59
def prefixEnd_3972205 : Nat := 4983230072969 + 3 ^ 40 * 3972205 * 2
def baseEnd_3972205 : Nat := 453255649598385880748815

theorem tailTrace_3972205 : CollatzResearch.WordTrace tailWord_3972205 prefixEnd_3972205 453255649598385880748815 := by
  unfold tailWord_3972205
  simp only [CollatzResearch.WordTrace]
  refine ⟨144878218574387158449038069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96585479049591438966025379 144878218574387158449038069)
  ·
    refine ⟨13582332991348796104597319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144878218574387158449038069 13582332991348796104597319)
    ·
      refine ⟨20373499487023194156895979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13582332991348796104597319 20373499487023194156895979)
      ·
        refine ⟨30560249230534791235343969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20373499487023194156895979 30560249230534791235343969)
        ·
          refine ⟨22920186922901093426507977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30560249230534791235343969 22920186922901093426507977)
          ·
            refine ⟨17190140192175820069880983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22920186922901093426507977 17190140192175820069880983)
            ·
              refine ⟨25785210288263730104821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17190140192175820069880983 25785210288263730104821475)
              ·
                refine ⟨38677815432395595157232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25785210288263730104821475 38677815432395595157232213)
                ·
                  refine ⟨453255649598385880748815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38677815432395595157232213 453255649598385880748815)
                  ·
                    rfl

theorem cell22_3972205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3972205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972205 prefixEnd_3972205 := by exact prefixLift 3972205
  have htrace : WordTrace (prefixWord ++ tailWord_3972205) baseStart_3972205 baseEnd_3972205 := by
    simpa [prefixWord, tailWord_3972205, baseEnd_3972205] using wordTrace_append hprefix tailTrace_3972205
  have hstable : (prefixWord ++ tailWord_3972205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972205).length < 2 ^ (prefixWord ++ tailWord_3972205).sum := by decide
  have hdescent : baseEnd_3972205 < baseStart_3972205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972220 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3972220 : Nat := 118140960795 + 3972220 * 2 ^ 59
def prefixEnd_3972220 : Nat := 4983230072969 + 3 ^ 40 * 3972220 * 2
def baseEnd_3972220 : Nat := 1359772083601702603121399

theorem tailTrace_3972220 : CollatzResearch.WordTrace tailWord_3972220 prefixEnd_3972220 1359772083601702603121399 := by
  unfold tailWord_3972220
  simp only [CollatzResearch.WordTrace]
  refine ⟨72439382834666408005417057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96585843779555210673889409 72439382834666408005417057)
  ·
    refine ⟨54329537125999806004062793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72439382834666408005417057 54329537125999806004062793)
    ·
      refine ⟨40747152844499854503047095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54329537125999806004062793 40747152844499854503047095)
      ·
        refine ⟨61120729266749781754570643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40747152844499854503047095 61120729266749781754570643)
        ·
          refine ⟨91681093900124672631855965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61120729266749781754570643 91681093900124672631855965)
          ·
            refine ⟨34380410212546752236945987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91681093900124672631855965 34380410212546752236945987)
            ·
              refine ⟨51570615318820128355418981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34380410212546752236945987 51570615318820128355418981)
              ·
                refine ⟨9669490372278774066641059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51570615318820128355418981 9669490372278774066641059)
                ·
                  refine ⟨14504235558418161099961589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9669490372278774066641059 14504235558418161099961589)
                  ·
                    refine ⟨1359772083601702603121399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14504235558418161099961589 1359772083601702603121399)
                    ·
                      rfl

theorem cell22_3972220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3972220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972220 prefixEnd_3972220 := by exact prefixLift 3972220
  have htrace : WordTrace (prefixWord ++ tailWord_3972220) baseStart_3972220 baseEnd_3972220 := by
    simpa [prefixWord, tailWord_3972220, baseEnd_3972220] using wordTrace_append hprefix tailTrace_3972220
  have hstable : (prefixWord ++ tailWord_3972220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972220).length < 2 ^ (prefixWord ++ tailWord_3972220).sum := by decide
  have hdescent : baseEnd_3972220 < baseStart_3972220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972235 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_3972235 : Nat := 118140960795 + 3972235 * 2 ^ 59
def prefixEnd_3972235 : Nat := 4983230072969 + 3 ^ 40 * 3972235 * 2
def baseEnd_3972235 : Nat := 1359777218408247563996353

theorem tailTrace_3972235 : CollatzResearch.WordTrace tailWord_3972235 prefixEnd_3972235 1359777218408247563996353 := by
  unfold tailWord_3972235
  simp only [CollatzResearch.WordTrace]
  refine ⟨144879312764278473572630159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96586208509518982381753439 144879312764278473572630159)
  ·
    refine ⟨217318969146417710358945239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144879312764278473572630159 217318969146417710358945239)
    ·
      refine ⟨325978453719626565538417859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217318969146417710358945239 325978453719626565538417859)
      ·
        refine ⟨488967680579439848307626789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325978453719626565538417859 488967680579439848307626789)
        ·
          refine ⟨91681440108644971557680023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 488967680579439848307626789 91681440108644971557680023)
          ·
            refine ⟨137522160162967457336520035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91681440108644971557680023 137522160162967457336520035)
            ·
              refine ⟨206283240244451186004780053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137522160162967457336520035 206283240244451186004780053)
              ·
                refine ⟨9669526886458649343974065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 206283240244451186004780053 9669526886458649343974065)
                ·
                  refine ⟨7252145164843987007980549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9669526886458649343974065 7252145164843987007980549)
                  ·
                    refine ⟨1359777218408247563996353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7252145164843987007980549 1359777218408247563996353)
                    ·
                      rfl

theorem cell22_3972235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_3972235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972235 prefixEnd_3972235 := by exact prefixLift 3972235
  have htrace : WordTrace (prefixWord ++ tailWord_3972235) baseStart_3972235 baseEnd_3972235 := by
    simpa [prefixWord, tailWord_3972235, baseEnd_3972235] using wordTrace_append hprefix tailTrace_3972235
  have hstable : (prefixWord ++ tailWord_3972235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972235).length < 2 ^ (prefixWord ++ tailWord_3972235).sum := by decide
  have hdescent : baseEnd_3972235 < baseStart_3972235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972254 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3972254 : Nat := 118140960795 + 3972254 * 2 ^ 59
def prefixEnd_3972254 : Nat := 4983230072969 + 3 ^ 40 * 3972254 * 2
def baseEnd_3972254 : Nat := 1359783722496537847771295

theorem tailTrace_3972254 : CollatzResearch.WordTrace tailWord_3972254 prefixEnd_3972254 1359783722496537847771295 := by
  unfold tailWord_3972254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110000718901204977196477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96586670500806426545047877 18110000718901204977196477)
  ·
    refine ⟨6791250269587951866448679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18110000718901204977196477 6791250269587951866448679)
    ·
      refine ⟨10186875404381927799673019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791250269587951866448679 10186875404381927799673019)
      ·
        refine ⟨15280313106572891699509529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186875404381927799673019 15280313106572891699509529)
        ·
          refine ⟨11460234829929668774632147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15280313106572891699509529 11460234829929668774632147)
          ·
            refine ⟨17190352244894503161948221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460234829929668774632147 17190352244894503161948221)
            ·
              refine ⟨6446382091835438685730583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17190352244894503161948221 6446382091835438685730583)
              ·
                refine ⟨9669573137753158028595875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446382091835438685730583 9669573137753158028595875)
                ·
                  refine ⟨14504359706629737042893813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9669573137753158028595875 14504359706629737042893813)
                  ·
                    refine ⟨1359783722496537847771295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14504359706629737042893813 1359783722496537847771295)
                    ·
                      rfl

theorem cell22_3972254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3972254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972254 prefixEnd_3972254 := by exact prefixLift 3972254
  have htrace : WordTrace (prefixWord ++ tailWord_3972254) baseStart_3972254 baseEnd_3972254 := by
    simpa [prefixWord, tailWord_3972254, baseEnd_3972254] using wordTrace_append hprefix tailTrace_3972254
  have hstable : (prefixWord ++ tailWord_3972254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972254).length < 2 ^ (prefixWord ++ tailWord_3972254).sum := by decide
  have hdescent : baseEnd_3972254 < baseStart_3972254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972290 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3972290 : Nat := 118140960795 + 3972290 * 2 ^ 59
def prefixEnd_3972290 : Nat := 4983230072969 + 3 ^ 40 * 3972290 * 2
def baseEnd_3972290 : Nat := 453265348677415251290395

theorem tailTrace_3972290 : CollatzResearch.WordTrace tailWord_3972290 prefixEnd_3972290 453265348677415251290395 := by
  unfold tailWord_3972290
  simp only [CollatzResearch.WordTrace]
  refine ⟨36220329694769804491470581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96587545852719478643921549 36220329694769804491470581)
  ·
    refine ⟨3395655908884669171075367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36220329694769804491470581 3395655908884669171075367)
    ·
      refine ⟨5093483863327003756613051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395655908884669171075367 5093483863327003756613051)
      ·
        refine ⟨7640225794990505634919577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093483863327003756613051 7640225794990505634919577)
        ·
          refine ⟨5730169346242879226189683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7640225794990505634919577 5730169346242879226189683)
          ·
            refine ⟨8595254019364318839284525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730169346242879226189683 8595254019364318839284525)
            ·
              refine ⟨3223220257261619564731697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8595254019364318839284525 3223220257261619564731697)
              ·
                refine ⟨2417415192946214673548773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223220257261619564731697 2417415192946214673548773)
                ·
                  refine ⟨453265348677415251290395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417415192946214673548773 453265348677415251290395)
                  ·
                    rfl

theorem cell22_3972290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3972290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972290 prefixEnd_3972290 := by exact prefixLift 3972290
  have htrace : WordTrace (prefixWord ++ tailWord_3972290) baseStart_3972290 baseEnd_3972290 := by
    simpa [prefixWord, tailWord_3972290, baseEnd_3972290] using wordTrace_append hprefix tailTrace_3972290
  have hstable : (prefixWord ++ tailWord_3972290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972290).length < 2 ^ (prefixWord ++ tailWord_3972290).sum := by decide
  have hdescent : baseEnd_3972290 < baseStart_3972290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972301 : List Nat := [1, 6, 2, 2, 1, 1, 2, 7]
def baseStart_3972301 : Nat := 118140960795 + 3972301 * 2 ^ 59
def prefixEnd_3972301 : Nat := 4983230072969 + 3 ^ 40 * 3972301 * 2
def baseEnd_3972301 : Nat := 151088867950782821316239

theorem tailTrace_3972301 : CollatzResearch.WordTrace tailWord_3972301 prefixEnd_3972301 151088867950782821316239 := by
  unfold tailWord_3972301
  simp only [CollatzResearch.WordTrace]
  refine ⟨144881719982039366844532757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96587813321359577896355171 144881719982039366844532757)
  ·
    refine ⟨6791330624158095320837473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 144881719982039366844532757 6791330624158095320837473)
    ·
      refine ⟨5093497968118571490628105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6791330624158095320837473 5093497968118571490628105)
      ·
        refine ⟨3820123476088928617971079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5093497968118571490628105 3820123476088928617971079)
        ·
          refine ⟨5730185214133392926956619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3820123476088928617971079 5730185214133392926956619)
          ·
            refine ⟨8595277821200089390434929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730185214133392926956619 8595277821200089390434929)
            ·
              refine ⟨6446458365900067042826197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8595277821200089390434929 6446458365900067042826197)
              ·
                refine ⟨151088867950782821316239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6446458365900067042826197 151088867950782821316239)
                ·
                  rfl

theorem cell22_3972301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 7].length) (baseStart_3972301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972301 prefixEnd_3972301 := by exact prefixLift 3972301
  have htrace : WordTrace (prefixWord ++ tailWord_3972301) baseStart_3972301 baseEnd_3972301 := by
    simpa [prefixWord, tailWord_3972301, baseEnd_3972301] using wordTrace_append hprefix tailTrace_3972301
  have hstable : (prefixWord ++ tailWord_3972301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972301).length < 2 ^ (prefixWord ++ tailWord_3972301).sum := by decide
  have hdescent : baseEnd_3972301 < baseStart_3972301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972350 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3972350 : Nat := 118140960795 + 3972350 * 2 ^ 59
def prefixEnd_3972350 : Nat := 4983230072969 + 3 ^ 40 * 3972350 * 2
def baseEnd_3972350 : Nat := 1359816585258425597371001

theorem tailTrace_3972350 : CollatzResearch.WordTrace tailWord_3972350 prefixEnd_3972350 1359816585258425597371001 := by
  unfold tailWord_3972350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110438394857731026633313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96589004772574565475377669 18110438394857731026633313)
  ·
    refine ⟨13582828796143298269974985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18110438394857731026633313 13582828796143298269974985)
    ·
      refine ⟨10187121597107473702481239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13582828796143298269974985 10187121597107473702481239)
      ·
        refine ⟨15280682395661210553721859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187121597107473702481239 15280682395661210553721859)
        ·
          refine ⟨22921023593491815830582789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280682395661210553721859 22921023593491815830582789)
          ·
            refine ⟨4297691923779715468234273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22921023593491815830582789 4297691923779715468234273)
            ·
              refine ⟨3223268942834786601175705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297691923779715468234273 3223268942834786601175705)
              ·
                refine ⟨2417451707126089950881779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223268942834786601175705 2417451707126089950881779)
                ·
                  refine ⟨3626177560689134926322669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417451707126089950881779 3626177560689134926322669)
                  ·
                    refine ⟨1359816585258425597371001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626177560689134926322669 1359816585258425597371001)
                    ·
                      rfl

theorem cell22_3972350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3972350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972350 prefixEnd_3972350 := by exact prefixLift 3972350
  have htrace : WordTrace (prefixWord ++ tailWord_3972350) baseStart_3972350 baseEnd_3972350 := by
    simpa [prefixWord, tailWord_3972350, baseEnd_3972350] using wordTrace_append hprefix tailTrace_3972350
  have hstable : (prefixWord ++ tailWord_3972350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972350).length < 2 ^ (prefixWord ++ tailWord_3972350).sum := by decide
  have hdescent : baseEnd_3972350 < baseStart_3972350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972387 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_3972387 : Nat := 118140960795 + 3972387 * 2 ^ 59
def prefixEnd_3972387 : Nat := 4983230072969 + 3 ^ 40 * 3972387 * 2
def baseEnd_3972387 : Nat := 1359829251114569834195887

theorem tailTrace_3972387 : CollatzResearch.WordTrace tailWord_3972387 prefixEnd_3972387 1359829251114569834195887 := by
  unfold tailWord_3972387
  simp only [CollatzResearch.WordTrace]
  refine ⟨144884856659727803532163415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96589904439818535688108943 144884856659727803532163415)
  ·
    refine ⟨217327284989591705298245123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144884856659727803532163415 217327284989591705298245123)
    ·
      refine ⟨325990927484387557947367685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217327284989591705298245123 325990927484387557947367685)
      ·
        refine ⟨61123298903322667115131441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 325990927484387557947367685 61123298903322667115131441)
        ·
          refine ⟨45842474177492000336348581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61123298903322667115131441 45842474177492000336348581)
          ·
            refine ⟨8595463908279750063065359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45842474177492000336348581 8595463908279750063065359)
            ·
              refine ⟨12893195862419625094598039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595463908279750063065359 12893195862419625094598039)
              ·
                refine ⟨19339793793629437641897059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12893195862419625094598039 19339793793629437641897059)
                ·
                  refine ⟨29009690690444156462845589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19339793793629437641897059 29009690690444156462845589)
                  ·
                    refine ⟨1359829251114569834195887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29009690690444156462845589 1359829251114569834195887)
                    ·
                      rfl

theorem cell22_3972387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_3972387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972387 prefixEnd_3972387 := by exact prefixLift 3972387
  have htrace : WordTrace (prefixWord ++ tailWord_3972387) baseStart_3972387 baseEnd_3972387 := by
    simpa [prefixWord, tailWord_3972387, baseEnd_3972387] using wordTrace_append hprefix tailTrace_3972387
  have hstable : (prefixWord ++ tailWord_3972387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972387).length < 2 ^ (prefixWord ++ tailWord_3972387).sum := by decide
  have hdescent : baseEnd_3972387 < baseStart_3972387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972402 : List Nat := [3, 2, 1, 1, 4, 2, 9]
def baseStart_3972402 : Nat := 118140960795 + 3972402 * 2 ^ 59
def prefixEnd_3972402 : Nat := 4983230072969 + 3 ^ 40 * 3972402 * 2
def baseEnd_3972402 : Nat := 50364236515596844261883

theorem tailTrace_3972402 : CollatzResearch.WordTrace tailWord_3972402 prefixEnd_3972402 50364236515596844261883 := by
  unfold tailWord_3972402
  simp only [CollatzResearch.WordTrace]
  refine ⟨36221350938668365273489865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96590269169782307395972973 36221350938668365273489865)
  ·
    refine ⟨27166013204001273955117399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36221350938668365273489865 27166013204001273955117399)
    ·
      refine ⟨40749019806001910932676099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27166013204001273955117399 40749019806001910932676099)
      ·
        refine ⟨61123529709002866399014149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40749019806001910932676099 61123529709002866399014149)
        ·
          refine ⟨11460661820438037449815153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61123529709002866399014149 11460661820438037449815153)
          ·
            refine ⟨8595496365328528087361365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11460661820438037449815153 8595496365328528087361365)
            ·
              refine ⟨50364236515596844261883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8595496365328528087361365 50364236515596844261883)
              ·
                rfl

theorem cell22_3972402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 9].length) (baseStart_3972402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972402 prefixEnd_3972402 := by exact prefixLift 3972402
  have htrace : WordTrace (prefixWord ++ tailWord_3972402) baseStart_3972402 baseEnd_3972402 := by
    simpa [prefixWord, tailWord_3972402, baseEnd_3972402] using wordTrace_append hprefix tailTrace_3972402
  have hstable : (prefixWord ++ tailWord_3972402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972402).length < 2 ^ (prefixWord ++ tailWord_3972402).sum := by decide
  have hdescent : baseEnd_3972402 < baseStart_3972402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972404 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3972404 : Nat := 118140960795 + 3972404 * 2 ^ 59
def prefixEnd_3972404 : Nat := 4983230072969 + 3 ^ 40 * 3972404 * 2
def baseEnd_3972404 : Nat := 1359835070561987456520835

theorem tailTrace_3972404 : CollatzResearch.WordTrace tailWord_3972404 prefixEnd_3972404 1359835070561987456520835 := by
  unfold tailWord_3972404
  simp only [CollatzResearch.WordTrace]
  refine ⟨72442738350333107717766133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96590317800444143623688177 72442738350333107717766133)
  ·
    refine ⟨6791506720343728848540575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72442738350333107717766133 6791506720343728848540575)
    ·
      refine ⟨10187260080515593272810863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6791506720343728848540575 10187260080515593272810863)
      ·
        refine ⟨15280890120773389909216295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10187260080515593272810863 15280890120773389909216295)
        ·
          refine ⟨22921335181160084863824443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280890120773389909216295 22921335181160084863824443)
          ·
            refine ⟨34382002771740127295736665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22921335181160084863824443 34382002771740127295736665)
            ·
              refine ⟨25786502078805095471802499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34382002771740127295736665 25786502078805095471802499)
              ·
                refine ⟨38679753118207643207703749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25786502078805095471802499 38679753118207643207703749)
                ·
                  refine ⟨7252453709663933101444453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38679753118207643207703749 7252453709663933101444453)
                  ·
                    refine ⟨1359835070561987456520835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7252453709663933101444453 1359835070561987456520835)
                    ·
                      rfl

theorem cell22_3972404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3972404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972404 prefixEnd_3972404 := by exact prefixLift 3972404
  have htrace : WordTrace (prefixWord ++ tailWord_3972404) baseStart_3972404 baseEnd_3972404 := by
    simpa [prefixWord, tailWord_3972404, baseEnd_3972404] using wordTrace_append hprefix tailTrace_3972404
  have hstable : (prefixWord ++ tailWord_3972404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972404).length < 2 ^ (prefixWord ++ tailWord_3972404).sum := by decide
  have hdescent : baseEnd_3972404 < baseStart_3972404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972481 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 5]
def baseStart_3972481 : Nat := 118140960795 + 3972481 * 2 ^ 59
def prefixEnd_3972481 : Nat := 4983230072969 + 3 ^ 40 * 3972481 * 2
def baseEnd_3972481 : Nat := 453287143078528307448533

theorem tailTrace_3972481 : CollatzResearch.WordTrace tailWord_3972481 prefixEnd_3972481 453287143078528307448533 := by
  unfold tailWord_3972481
  simp only [CollatzResearch.WordTrace]
  refine ⟨144888285121387257586085297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96592190080924838390723531 144888285121387257586085297)
  ·
    refine ⟨108666213841040443189563973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144888285121387257586085297 108666213841040443189563973)
    ·
      refine ⟨20374915095195083098043245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108666213841040443189563973 20374915095195083098043245)
      ·
        refine ⟨7640593160698156161766217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20374915095195083098043245 7640593160698156161766217)
        ·
          refine ⟨5730444870523617121324663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7640593160698156161766217 5730444870523617121324663)
          ·
            refine ⟨8595667305785425681986995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730444870523617121324663 8595667305785425681986995)
            ·
              refine ⟨12893500958678138522980493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8595667305785425681986995 12893500958678138522980493)
              ·
                refine ⟨4835062859504301946117685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12893500958678138522980493 4835062859504301946117685)
                ·
                  refine ⟨453287143078528307448533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4835062859504301946117685 453287143078528307448533)
                  ·
                    rfl

theorem cell22_3972481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_3972481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972481 prefixEnd_3972481 := by exact prefixLift 3972481
  have htrace : WordTrace (prefixWord ++ tailWord_3972481) baseStart_3972481 baseEnd_3972481 := by
    simpa [prefixWord, tailWord_3972481, baseEnd_3972481] using wordTrace_append hprefix tailTrace_3972481
  have hstable : (prefixWord ++ tailWord_3972481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972481).length < 2 ^ (prefixWord ++ tailWord_3972481).sum := by decide
  have hdescent : baseEnd_3972481 < baseStart_3972481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972492 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_3972492 : Nat := 118140960795 + 3972492 * 2 ^ 59
def prefixEnd_3972492 : Nat := 4983230072969 + 3 ^ 40 * 3972492 * 2
def baseEnd_3972492 : Nat := 453288398253461520106855

theorem tailTrace_3972492 : CollatzResearch.WordTrace tailWord_3972492 prefixEnd_3972492 453288398253461520106855 := by
  unfold tailWord_3972492
  simp only [CollatzResearch.WordTrace]
  refine ⟨72444343162173703232367865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96592457549564937643157153 72444343162173703232367865)
  ·
    refine ⟨54333257371630277424275899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72444343162173703232367865 54333257371630277424275899)
    ·
      refine ⟨81499886057445416136413849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54333257371630277424275899 81499886057445416136413849)
      ·
        refine ⟨61124914543084062102310387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81499886057445416136413849 61124914543084062102310387)
        ·
          refine ⟨91687371814626093153465581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61124914543084062102310387 91687371814626093153465581)
          ·
            refine ⟨34382764430484784932549593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91687371814626093153465581 34382764430484784932549593)
            ·
              refine ⟨25787073322863588699412195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34382764430484784932549593 25787073322863588699412195)
              ·
                refine ⟨38680609984295383049118293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25787073322863588699412195 38680609984295383049118293)
                ·
                  refine ⟨453288398253461520106855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38680609984295383049118293 453288398253461520106855)
                  ·
                    rfl

theorem cell22_3972492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_3972492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972492 prefixEnd_3972492 := by exact prefixLift 3972492
  have htrace : WordTrace (prefixWord ++ tailWord_3972492) baseStart_3972492 baseEnd_3972492 := by
    simpa [prefixWord, tailWord_3972492, baseEnd_3972492] using wordTrace_append hprefix tailTrace_3972492
  have hstable : (prefixWord ++ tailWord_3972492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972492).length < 2 ^ (prefixWord ++ tailWord_3972492).sum := by decide
  have hdescent : baseEnd_3972492 < baseStart_3972492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972524 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_3972524 : Nat := 118140960795 + 3972524 * 2 ^ 59
def prefixEnd_3972524 : Nat := 4983230072969 + 3 ^ 40 * 3972524 * 2
def baseEnd_3972524 : Nat := 1359876149014347143520467

theorem tailTrace_3972524 : CollatzResearch.WordTrace tailWord_3972524 prefixEnd_3972524 1359876149014347143520467 := by
  unfold tailWord_3972524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72444926730115737964950313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96593235640154317286600417 72444926730115737964950313)
  ·
    refine ⟨54333695047586803473712735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72444926730115737964950313 54333695047586803473712735)
    ·
      refine ⟨81500542571380205210569103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54333695047586803473712735 81500542571380205210569103)
      ·
        refine ⟨122250813857070307815853655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81500542571380205210569103 122250813857070307815853655)
        ·
          refine ⟨183376220785605461723780483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122250813857070307815853655 183376220785605461723780483)
          ·
            refine ⟨275064331178408192585670725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183376220785605461723780483 275064331178408192585670725)
            ·
              refine ⟨51574562095951536109813261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275064331178408192585670725 51574562095951536109813261)
              ·
                refine ⟨19340460785981826041179973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51574562095951536109813261 19340460785981826041179973)
                ·
                  refine ⟨3626336397371592382721245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19340460785981826041179973 3626336397371592382721245)
                  ·
                    refine ⟨1359876149014347143520467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626336397371592382721245 1359876149014347143520467)
                    ·
                      rfl

theorem cell22_3972524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_3972524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972524 prefixEnd_3972524 := by exact prefixLift 3972524
  have htrace : WordTrace (prefixWord ++ tailWord_3972524) baseStart_3972524 baseEnd_3972524 := by
    simpa [prefixWord, tailWord_3972524, baseEnd_3972524] using wordTrace_append hprefix tailTrace_3972524
  have hstable : (prefixWord ++ tailWord_3972524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972524).length < 2 ^ (prefixWord ++ tailWord_3972524).sum := by decide
  have hdescent : baseEnd_3972524 < baseStart_3972524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972541 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3972541 : Nat := 118140960795 + 3972541 * 2 ^ 59
def prefixEnd_3972541 : Nat := 4983230072969 + 3 ^ 40 * 3972541 * 2
def baseEnd_3972541 : Nat := 1359881968461764765845415

theorem tailTrace_3972541 : CollatzResearch.WordTrace tailWord_3972541 prefixEnd_3972541 1359881968461764765845415 := by
  unfold tailWord_3972541
  simp only [CollatzResearch.WordTrace]
  refine ⟨144890473501169887833269477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96593649000779925222179651 144890473501169887833269477)
  ·
    refine ⟨27166963781469353968738027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144890473501169887833269477 27166963781469353968738027)
    ·
      refine ⟨40750445672204030953107041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27166963781469353968738027 40750445672204030953107041)
      ·
        refine ⟨30562834254153023214830281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40750445672204030953107041 30562834254153023214830281)
        ·
          refine ⟨22922125690614767411122711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30562834254153023214830281 22922125690614767411122711)
          ·
            refine ⟨34383188535922151116684067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22922125690614767411122711 34383188535922151116684067)
            ·
              refine ⟨51574782803883226675026101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34383188535922151116684067 51574782803883226675026101)
              ·
                refine ⟨4835135887864052500783697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51574782803883226675026101 4835135887864052500783697)
                ·
                  refine ⟨3626351915898039375587773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835135887864052500783697 3626351915898039375587773)
                  ·
                    refine ⟨1359881968461764765845415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626351915898039375587773 1359881968461764765845415)
                    ·
                      rfl

theorem cell22_3972541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3972541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972541 prefixEnd_3972541 := by exact prefixLift 3972541
  have htrace : WordTrace (prefixWord ++ tailWord_3972541) baseStart_3972541 baseEnd_3972541 := by
    simpa [prefixWord, tailWord_3972541, baseEnd_3972541] using wordTrace_append hprefix tailTrace_3972541
  have hstable : (prefixWord ++ tailWord_3972541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972541).length < 2 ^ (prefixWord ++ tailWord_3972541).sum := by decide
  have hdescent : baseEnd_3972541 < baseStart_3972541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972556 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_3972556 : Nat := 118140960795 + 3972556 * 2 ^ 59
def prefixEnd_3972556 : Nat := 4983230072969 + 3 ^ 40 * 3972556 * 2
def baseEnd_3972556 : Nat := 1359887103268309726720369

theorem tailTrace_3972556 : CollatzResearch.WordTrace tailWord_3972556 prefixEnd_3972556 1359887103268309726720369 := by
  unfold tailWord_3972556
  simp only [CollatzResearch.WordTrace]
  refine ⟨72445510298057772697532761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96594013730743696930043681 72445510298057772697532761)
  ·
    refine ⟨54334132723543329523149571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72445510298057772697532761 54334132723543329523149571)
    ·
      refine ⟨81501199085314994284724357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54334132723543329523149571 81501199085314994284724357)
      ·
        refine ⟨15281474828496561428385817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81501199085314994284724357 15281474828496561428385817)
        ·
          refine ⟨11461106121372421071289363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15281474828496561428385817 11461106121372421071289363)
          ·
            refine ⟨17191659182058631606934045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11461106121372421071289363 17191659182058631606934045)
            ·
              refine ⟨6446872193271986852600267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17191659182058631606934045 6446872193271986852600267)
              ·
                refine ⟨9670308289907980278900401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6446872193271986852600267 9670308289907980278900401)
                ·
                  refine ⟨7252731217430985209175301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670308289907980278900401 7252731217430985209175301)
                  ·
                    refine ⟨1359887103268309726720369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7252731217430985209175301 1359887103268309726720369)
                    ·
                      rfl

theorem cell22_3972556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_3972556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972556 prefixEnd_3972556 := by exact prefixLift 3972556
  have htrace : WordTrace (prefixWord ++ tailWord_3972556) baseStart_3972556 baseEnd_3972556 := by
    simpa [prefixWord, tailWord_3972556, baseEnd_3972556] using wordTrace_append hprefix tailTrace_3972556
  have hstable : (prefixWord ++ tailWord_3972556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972556).length < 2 ^ (prefixWord ++ tailWord_3972556).sum := by decide
  have hdescent : baseEnd_3972556 < baseStart_3972556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972663 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 1, 4]
def baseStart_3972663 : Nat := 118140960795 + 3972663 * 2 ^ 59
def prefixEnd_3972663 : Nat := 4983230072969 + 3 ^ 40 * 3972663 * 2
def baseEnd_3972663 : Nat := 1359923731554997114295041

theorem tailTrace_3972663 : CollatzResearch.WordTrace tailWord_3972663 prefixEnd_3972663 1359923731554997114295041 := by
  unfold tailWord_3972663
  simp only [CollatzResearch.WordTrace]
  refine ⟨144894923206727902669210643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96596615471151935112807095 144894923206727902669210643)
  ·
    refine ⟨217342384810091854003815965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144894923206727902669210643 217342384810091854003815965)
    ·
      refine ⟨81503394303784445251430987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217342384810091854003815965 81503394303784445251430987)
      ·
        refine ⟨122255091455676667877146481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81503394303784445251430987 122255091455676667877146481)
        ·
          refine ⟨91691318591757500907859861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122255091455676667877146481 91691318591757500907859861)
          ·
            refine ⟨4298030558988632855055931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91691318591757500907859861 4298030558988632855055931)
            ·
              refine ⟨6447045838482949282583897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298030558988632855055931 6447045838482949282583897)
              ·
                refine ⟨4835284378862211961937923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447045838482949282583897 4835284378862211961937923)
                ·
                  refine ⟨7252926568293317942906885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835284378862211961937923 7252926568293317942906885)
                  ·
                    refine ⟨1359923731554997114295041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7252926568293317942906885 1359923731554997114295041)
                    ·
                      rfl

theorem cell22_3972663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_3972663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972663 prefixEnd_3972663 := by exact prefixLift 3972663
  have htrace : WordTrace (prefixWord ++ tailWord_3972663) baseStart_3972663 baseEnd_3972663 := by
    simpa [prefixWord, tailWord_3972663, baseEnd_3972663] using wordTrace_append hprefix tailTrace_3972663
  have hstable : (prefixWord ++ tailWord_3972663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972663).length < 2 ^ (prefixWord ++ tailWord_3972663).sum := by decide
  have hdescent : baseEnd_3972663 < baseStart_3972663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972695 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 4]
def baseStart_3972695 : Nat := 118140960795 + 3972695 * 2 ^ 59
def prefixEnd_3972695 : Nat := 4983230072969 + 3 ^ 40 * 3972695 * 2
def baseEnd_3972695 : Nat := 453311561936319899164981

theorem tailTrace_3972695 : CollatzResearch.WordTrace tailWord_3972695 prefixEnd_3972695 453311561936319899164981 := by
  unfold tailWord_3972695
  simp only [CollatzResearch.WordTrace]
  refine ⟨144896090342611972134375539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96597393561741314756250359 144896090342611972134375539)
  ·
    refine ⟨217344135513917958201563309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144896090342611972134375539 217344135513917958201563309)
    ·
      refine ⟨81504050817719234325586241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217344135513917958201563309 81504050817719234325586241)
      ·
        refine ⟨61128038113289425744189681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81504050817719234325586241 61128038113289425744189681)
        ·
          refine ⟨45846028584967069308142261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61128038113289425744189681 45846028584967069308142261)
          ·
            refine ⟨4298065179840662747638337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45846028584967069308142261 4298065179840662747638337)
            ·
              refine ⟨3223548884880497060728753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298065179840662747638337 3223548884880497060728753)
              ·
                refine ⟨2417661663660372795546565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223548884880497060728753 2417661663660372795546565)
                ·
                  refine ⟨453311561936319899164981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2417661663660372795546565 453311561936319899164981)
                  ·
                    rfl

theorem cell22_3972695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 4].length) (baseStart_3972695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972695 prefixEnd_3972695 := by exact prefixLift 3972695
  have htrace : WordTrace (prefixWord ++ tailWord_3972695) baseStart_3972695 baseEnd_3972695 := by
    simpa [prefixWord, tailWord_3972695, baseEnd_3972695] using wordTrace_append hprefix tailTrace_3972695
  have hstable : (prefixWord ++ tailWord_3972695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972695).length < 2 ^ (prefixWord ++ tailWord_3972695).sum := by decide
  have hdescent : baseEnd_3972695 < baseStart_3972695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972704 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_3972704 : Nat := 118140960795 + 3972704 * 2 ^ 59
def prefixEnd_3972704 : Nat := 4983230072969 + 3 ^ 40 * 3972704 * 2
def baseEnd_3972704 : Nat := 1359937766692886674019915

theorem tailTrace_3972704 : CollatzResearch.WordTrace tailWord_3972704 prefixEnd_3972704 1359937766692886674019915 := by
  unfold tailWord_3972704
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448209299789683335726583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96597612399719577780968777 72448209299789683335726583)
  ·
    refine ⟨108672313949684525003589875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72448209299789683335726583 108672313949684525003589875)
    ·
      refine ⟨163008470924526787505384813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108672313949684525003589875 163008470924526787505384813)
      ·
        refine ⟨61128176596697545314519305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163008470924526787505384813 61128176596697545314519305)
        ·
          refine ⟨45846132447523158985889479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61128176596697545314519305 45846132447523158985889479)
          ·
            refine ⟨68769198671284738478834219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45846132447523158985889479 68769198671284738478834219)
            ·
              refine ⟨103153798006927107718251329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68769198671284738478834219 103153798006927107718251329)
              ·
                refine ⟨77365348505195330788688497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103153798006927107718251329 77365348505195330788688497)
                ·
                  refine ⟨58024011378896498091516373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77365348505195330788688497 58024011378896498091516373)
                  ·
                    refine ⟨1359937766692886674019915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58024011378896498091516373 1359937766692886674019915)
                    ·
                      rfl

theorem cell22_3972704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_3972704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972704 prefixEnd_3972704 := by exact prefixLift 3972704
  have htrace : WordTrace (prefixWord ++ tailWord_3972704) baseStart_3972704 baseEnd_3972704 := by
    simpa [prefixWord, tailWord_3972704, baseEnd_3972704] using wordTrace_append hprefix tailTrace_3972704
  have hstable : (prefixWord ++ tailWord_3972704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972704).length < 2 ^ (prefixWord ++ tailWord_3972704).sum := by decide
  have hdescent : baseEnd_3972704 < baseStart_3972704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972719 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_3972719 : Nat := 118140960795 + 3972719 * 2 ^ 59
def prefixEnd_3972719 : Nat := 4983230072969 + 3 ^ 40 * 3972719 * 2
def baseEnd_3972719 : Nat := 1359942901499431634894869

theorem tailTrace_3972719 : CollatzResearch.WordTrace tailWord_3972719 prefixEnd_3972719 1359942901499431634894869 := by
  unfold tailWord_3972719
  simp only [CollatzResearch.WordTrace]
  refine ⟨144896965694525024233249211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96597977129683349488832807 144896965694525024233249211)
  ·
    refine ⟨217345448541787536349873817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144896965694525024233249211 217345448541787536349873817)
    ·
      refine ⟨163009086406340652262405363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217345448541787536349873817 163009086406340652262405363)
      ·
        refine ⟨244513629609510978393608045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163009086406340652262405363 244513629609510978393608045)
        ·
          refine ⟨91692611103566616897603017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244513629609510978393608045 91692611103566616897603017)
          ·
            refine ⟨68769458327674962673202263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91692611103566616897603017 68769458327674962673202263)
            ·
              refine ⟨103154187491512444009803395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68769458327674962673202263 103154187491512444009803395)
              ·
                refine ⟨154731281237268666014705093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103154187491512444009803395 154731281237268666014705093)
                ·
                  refine ⟨29012115231987874877757205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154731281237268666014705093 29012115231987874877757205)
                  ·
                    refine ⟨1359942901499431634894869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29012115231987874877757205 1359942901499431634894869)
                    ·
                      rfl

theorem cell22_3972719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_3972719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972719 prefixEnd_3972719 := by exact prefixLift 3972719
  have htrace : WordTrace (prefixWord ++ tailWord_3972719) baseStart_3972719 baseEnd_3972719 := by
    simpa [prefixWord, tailWord_3972719, baseEnd_3972719] using wordTrace_append hprefix tailTrace_3972719
  have hstable : (prefixWord ++ tailWord_3972719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972719).length < 2 ^ (prefixWord ++ tailWord_3972719).sum := by decide
  have hdescent : baseEnd_3972719 < baseStart_3972719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972725 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3972725 : Nat := 118140960795 + 3972725 * 2 ^ 59
def prefixEnd_3972725 : Nat := 4983230072969 + 3 ^ 40 * 3972725 * 2
def baseEnd_3972725 : Nat := 1359944955422049619244851

theorem tailTrace_3972725 : CollatzResearch.WordTrace tailWord_3972725 prefixEnd_3972725 1359944955422049619244851 := by
  unfold tailWord_3972725
  simp only [CollatzResearch.WordTrace]
  refine ⟨144897184532503287257967629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96598123021668858171978419 144897184532503287257967629)
  ·
    refine ⟨54336444199688732721737861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144897184532503287257967629 54336444199688732721737861)
    ·
      refine ⟨10188083287441637385325849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54336444199688732721737861 10188083287441637385325849)
      ·
        refine ⟨7641062465581228038994387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188083287441637385325849 7641062465581228038994387)
        ·
          refine ⟨11461593698371842058491581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641062465581228038994387 11461593698371842058491581)
          ·
            refine ⟨4298097636889440771934343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11461593698371842058491581 4298097636889440771934343)
            ·
              refine ⟨6447146455334161157901515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298097636889440771934343 6447146455334161157901515)
              ·
                refine ⟨9670719683001241736852273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447146455334161157901515 9670719683001241736852273)
                ·
                  refine ⟨7253039762250931302639205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9670719683001241736852273 7253039762250931302639205)
                  ·
                    refine ⟨1359944955422049619244851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253039762250931302639205 1359944955422049619244851)
                    ·
                      rfl

theorem cell22_3972725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3972725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972725 prefixEnd_3972725 := by exact prefixLift 3972725
  have htrace : WordTrace (prefixWord ++ tailWord_3972725) baseStart_3972725 baseEnd_3972725 := by
    simpa [prefixWord, tailWord_3972725, baseEnd_3972725] using wordTrace_append hprefix tailTrace_3972725
  have hstable : (prefixWord ++ tailWord_3972725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972725).length < 2 ^ (prefixWord ++ tailWord_3972725).sum := by decide
  have hdescent : baseEnd_3972725 < baseStart_3972725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972744 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_3972744 : Nat := 118140960795 + 3972744 * 2 ^ 59
def prefixEnd_3972744 : Nat := 4983230072969 + 3 ^ 40 * 3972744 * 2
def baseEnd_3972744 : Nat := 1359951459510339903019793

theorem tailTrace_3972744 : CollatzResearch.WordTrace tailWord_3972744 prefixEnd_3972744 1359951459510339903019793 := by
  unfold tailWord_3972744
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448938759717226751454643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96598585012956302335272857 72448938759717226751454643)
  ·
    refine ⟨108673408139575840127181965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72448938759717226751454643 108673408139575840127181965)
    ·
      refine ⟨40752528052340940047693237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108673408139575840127181965 40752528052340940047693237)
      ·
        refine ⟨3820549504906963129471241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40752528052340940047693237 3820549504906963129471241)
        ·
          refine ⟨2865412128680222347103431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3820549504906963129471241 2865412128680222347103431)
          ·
            refine ⟨4298118193020333520655147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865412128680222347103431 4298118193020333520655147)
            ·
              refine ⟨6447177289530500280982721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298118193020333520655147 6447177289530500280982721)
              ·
                refine ⟨4835382967147875210737041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447177289530500280982721 4835382967147875210737041)
                ·
                  refine ⟨3626537225360906408052781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835382967147875210737041 3626537225360906408052781)
                  ·
                    refine ⟨1359951459510339903019793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626537225360906408052781 1359951459510339903019793)
                    ·
                      rfl

theorem cell22_3972744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_3972744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972744 prefixEnd_3972744 := by exact prefixLift 3972744
  have htrace : WordTrace (prefixWord ++ tailWord_3972744) baseStart_3972744 baseEnd_3972744 := by
    simpa [prefixWord, tailWord_3972744, baseEnd_3972744] using wordTrace_append hprefix tailTrace_3972744
  have hstable : (prefixWord ++ tailWord_3972744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972744).length < 2 ^ (prefixWord ++ tailWord_3972744).sum := by decide
  have hdescent : baseEnd_3972744 < baseStart_3972744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972789 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3972789 : Nat := 118140960795 + 3972789 * 2 ^ 59
def prefixEnd_3972789 : Nat := 4983230072969 + 3 ^ 40 * 3972789 * 2
def baseEnd_3972789 : Nat := 1359966863929974785644655

theorem tailTrace_3972789 : CollatzResearch.WordTrace tailWord_3972789 prefixEnd_3972789 1359966863929974785644655 := by
  unfold tailWord_3972789
  simp only [CollatzResearch.WordTrace]
  refine ⟨144899518804271426188297421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96599679202847617458864947 144899518804271426188297421)
  ·
    refine ⟨54337319551601784820611533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144899518804271426188297421 54337319551601784820611533)
    ·
      refine ⟨20376494831850669307729325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54337319551601784820611533 20376494831850669307729325)
      ·
        refine ⟨7641185561944000990398497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20376494831850669307729325 7641185561944000990398497)
        ·
          refine ⟨5730889171458000742798873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7641185561944000990398497 5730889171458000742798873)
          ·
            refine ⟨4298166878593500557099155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5730889171458000742798873 4298166878593500557099155)
            ·
              refine ⟨6447250317890250835648733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298166878593500557099155 6447250317890250835648733)
              ·
                refine ⟨2417718869208844063368275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6447250317890250835648733 2417718869208844063368275)
                ·
                  refine ⟨3626578303813266095052413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417718869208844063368275 3626578303813266095052413)
                  ·
                    refine ⟨1359966863929974785644655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626578303813266095052413 1359966863929974785644655)
                    ·
                      rfl

theorem cell22_3972789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3972789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972789 prefixEnd_3972789 := by exact prefixLift 3972789
  have htrace : WordTrace (prefixWord ++ tailWord_3972789) baseStart_3972789 baseEnd_3972789 := by
    simpa [prefixWord, tailWord_3972789, baseEnd_3972789] using wordTrace_append hprefix tailTrace_3972789
  have hstable : (prefixWord ++ tailWord_3972789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972789).length < 2 ^ (prefixWord ++ tailWord_3972789).sum := by decide
  have hdescent : baseEnd_3972789 < baseStart_3972789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972873 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_3972873 : Nat := 118140960795 + 3972873 * 2 ^ 59
def prefixEnd_3972873 : Nat := 4983230072969 + 3 ^ 40 * 3972873 * 2
def baseEnd_3972873 : Nat := 1359995618846626566544397

theorem tailTrace_3972873 : CollatzResearch.WordTrace tailWord_3972873 prefixEnd_3972873 1359995618846626566544397 := by
  unfold tailWord_3972873
  simp only [CollatzResearch.WordTrace]
  refine ⟨144902582535967108534355273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96601721690644739022903515 144902582535967108534355273)
  ·
    refine ⟨108676936901975331400766455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144902582535967108534355273 108676936901975331400766455)
    ·
      refine ⟨163015405352962997101149683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108676936901975331400766455 163015405352962997101149683)
      ·
        refine ⟨244523108029444495651724525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163015405352962997101149683 244523108029444495651724525)
        ·
          refine ⟨91696165511041685869396697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244523108029444495651724525 91696165511041685869396697)
          ·
            refine ⟨68772124133281264402047523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91696165511041685869396697 68772124133281264402047523)
            ·
              refine ⟨103158186199921896603071285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68772124133281264402047523 103158186199921896603071285)
              ·
                refine ⟨9671079956242677806537933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103158186199921896603071285 9671079956242677806537933)
                ·
                  refine ⟨3626654983591004177451725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9671079956242677806537933 3626654983591004177451725)
                  ·
                    refine ⟨1359995618846626566544397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626654983591004177451725 1359995618846626566544397)
                    ·
                      rfl

theorem cell22_3972873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_3972873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972873 prefixEnd_3972873 := by exact prefixLift 3972873
  have htrace : WordTrace (prefixWord ++ tailWord_3972873) baseStart_3972873 baseEnd_3972873 := by
    simpa [prefixWord, tailWord_3972873, baseEnd_3972873] using wordTrace_append hprefix tailTrace_3972873
  have hstable : (prefixWord ++ tailWord_3972873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972873).length < 2 ^ (prefixWord ++ tailWord_3972873).sum := by decide
  have hdescent : baseEnd_3972873 < baseStart_3972873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972890 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_3972890 : Nat := 118140960795 + 3972890 * 2 ^ 59
def prefixEnd_3972890 : Nat := 4983230072969 + 3 ^ 40 * 3972890 * 2
def baseEnd_3972890 : Nat := 1360001438294044188869345

theorem tailTrace_3972890 : CollatzResearch.WordTrace tailWord_3972890 prefixEnd_3972890 1360001438294044188869345 := by
  unfold tailWord_3972890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36225800644226380109431031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96602135051270346958482749 36225800644226380109431031)
  ·
    refine ⟨54338700966339570164146547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36225800644226380109431031 54338700966339570164146547)
    ·
      refine ⟨81508051449509355246219821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54338700966339570164146547 81508051449509355246219821)
      ·
        refine ⟨30565519293566008217332433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81508051449509355246219821 30565519293566008217332433)
        ·
          refine ⟨22924139470174506162999325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30565519293566008217332433 22924139470174506162999325)
          ·
            refine ⟨8596552301315439811124747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22924139470174506162999325 8596552301315439811124747)
            ·
              refine ⟨12894828451973159716687121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596552301315439811124747 12894828451973159716687121)
              ·
                refine ⟨9671121338979869787515341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12894828451973159716687121 9671121338979869787515341)
                ·
                  refine ⟨3626670502117451170318253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9671121338979869787515341 3626670502117451170318253)
                  ·
                    refine ⟨1360001438294044188869345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626670502117451170318253 1360001438294044188869345)
                    ·
                      rfl

theorem cell22_3972890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_3972890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972890 prefixEnd_3972890 := by exact prefixLift 3972890
  have htrace : WordTrace (prefixWord ++ tailWord_3972890) baseStart_3972890 baseEnd_3972890 := by
    simpa [prefixWord, tailWord_3972890, baseEnd_3972890] using wordTrace_append hprefix tailTrace_3972890
  have hstable : (prefixWord ++ tailWord_3972890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972890).length < 2 ^ (prefixWord ++ tailWord_3972890).sum := by decide
  have hdescent : baseEnd_3972890 < baseStart_3972890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3972920 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_3972920 : Nat := 118140960795 + 3972920 * 2 ^ 59
def prefixEnd_3972920 : Nat := 4983230072969 + 3 ^ 40 * 3972920 * 2
def baseEnd_3972920 : Nat := 453337235969044703539751

theorem tailTrace_3972920 : CollatzResearch.WordTrace tailWord_3972920 prefixEnd_3972920 453337235969044703539751 := by
  unfold tailWord_3972920
  simp only [CollatzResearch.WordTrace]
  refine ⟨72452148383398417780658107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96602864511197890374210809 72452148383398417780658107)
  ·
    refine ⟨108678222575097626670987161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72452148383398417780658107 108678222575097626670987161)
    ·
      refine ⟨81508666931323220003240371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108678222575097626670987161 81508666931323220003240371)
      ·
        refine ⟨122263000396984830004860557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81508666931323220003240371 122263000396984830004860557)
        ·
          refine ⟨45848625148869311251822709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122263000396984830004860557 45848625148869311251822709)
          ·
            refine ⟨4298308607706497929858379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45848625148869311251822709 4298308607706497929858379)
            ·
              refine ⟨6447462911559746894787569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298308607706497929858379 6447462911559746894787569)
              ·
                refine ⟨4835597183669810171090677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447462911559746894787569 4835597183669810171090677)
                ·
                  refine ⟨453337235969044703539751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4835597183669810171090677 453337235969044703539751)
                  ·
                    rfl

theorem cell22_3972920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_3972920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3972920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3972920 prefixEnd_3972920 := by exact prefixLift 3972920
  have htrace : WordTrace (prefixWord ++ tailWord_3972920) baseStart_3972920 baseEnd_3972920 := by
    simpa [prefixWord, tailWord_3972920, baseEnd_3972920] using wordTrace_append hprefix tailTrace_3972920
  have hstable : (prefixWord ++ tailWord_3972920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3972920).length < 2 ^ (prefixWord ++ tailWord_3972920).sum := by decide
  have hdescent : baseEnd_3972920 < baseStart_3972920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3972920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973010 : List Nat := [3, 2, 3, 2, 1, 1, 2, 8]
def baseStart_3973010 : Nat := 118140960795 + 3973010 * 2 ^ 59
def prefixEnd_3973010 : Nat := 4983230072969 + 3 ^ 40 * 3973010 * 2
def baseEnd_3973010 : Nat := 151115835194044875096553

theorem tailTrace_3973010 : CollatzResearch.WordTrace tailWord_3973010 prefixEnd_3973010 151115835194044875096553 := by
  unfold tailWord_3973010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36226894834117695233023121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96605052890980520621394989 36226894834117695233023121)
  ·
    refine ⟨27170171125588271424767341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36226894834117695233023121 27170171125588271424767341)
    ·
      refine ⟨10188814172095601784287753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27170171125588271424767341 10188814172095601784287753)
      ·
        refine ⟨7641610629071701338215815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10188814172095601784287753 7641610629071701338215815)
        ·
          refine ⟨11462415943607552007323723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7641610629071701338215815 11462415943607552007323723)
          ·
            refine ⟨17193623915411328010985585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11462415943607552007323723 17193623915411328010985585)
            ·
              refine ⟨12895217936558496008239189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17193623915411328010985585 12895217936558496008239189)
              ·
                refine ⟨151115835194044875096553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12895217936558496008239189 151115835194044875096553)
                ·
                  rfl

theorem cell22_3973010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_3973010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973010 prefixEnd_3973010 := by exact prefixLift 3973010
  have htrace : WordTrace (prefixWord ++ tailWord_3973010) baseStart_3973010 baseEnd_3973010 := by
    simpa [prefixWord, tailWord_3973010, baseEnd_3973010] using wordTrace_append hprefix tailTrace_3973010
  have hstable : (prefixWord ++ tailWord_3973010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973010).length < 2 ^ (prefixWord ++ tailWord_3973010).sum := by decide
  have hdescent : baseEnd_3973010 < baseStart_3973010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973012 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3973012 : Nat := 118140960795 + 3973012 * 2 ^ 59
def prefixEnd_3973012 : Nat := 4983230072969 + 3 ^ 40 * 3973012 * 2
def baseEnd_3973012 : Nat := 1360043201387276537318971

theorem tailTrace_3973012 : CollatzResearch.WordTrace tailWord_3973012 prefixEnd_3973012 1360043201387276537318971 := by
  unfold tailWord_3973012
  simp only [CollatzResearch.WordTrace]
  refine ⟨72453826141231767636832645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96605101521642356849110193 72453826141231767636832645)
  ·
    refine ⟨13585092401480956431906121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72453826141231767636832645 13585092401480956431906121)
    ·
      refine ⟨10188819301110717323929591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13585092401480956431906121 10188819301110717323929591)
      ·
        refine ⟨15283228951666075985894387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188819301110717323929591 15283228951666075985894387)
        ·
          refine ⟨22924843427499113978841581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15283228951666075985894387 22924843427499113978841581)
          ·
            refine ⟨8596816285312167742065593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22924843427499113978841581 8596816285312167742065593)
            ·
              refine ⟨6447612213984125806549195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8596816285312167742065593 6447612213984125806549195)
              ·
                refine ⟨9671418320976188709823793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447612213984125806549195 9671418320976188709823793)
                ·
                  refine ⟨7253563740732141532367845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9671418320976188709823793 7253563740732141532367845)
                  ·
                    refine ⟨1360043201387276537318971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7253563740732141532367845 1360043201387276537318971)
                    ·
                      rfl

theorem cell22_3973012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3973012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973012 prefixEnd_3973012 := by exact prefixLift 3973012
  have htrace : WordTrace (prefixWord ++ tailWord_3973012) baseStart_3973012 baseEnd_3973012 := by
    simpa [prefixWord, tailWord_3973012, baseEnd_3973012] using wordTrace_append hprefix tailTrace_3973012
  have hstable : (prefixWord ++ tailWord_3973012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973012).length < 2 ^ (prefixWord ++ tailWord_3973012).sum := by decide
  have hdescent : baseEnd_3973012 < baseStart_3973012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973044 : List Nat := [2, 5, 2, 1, 2, 2, 1, 7]
def baseStart_3973044 : Nat := 118140960795 + 3973044 * 2 ^ 59
def prefixEnd_3973044 : Nat := 4983230072969 + 3 ^ 40 * 3973044 * 2
def baseEnd_3973044 : Nat := 151117128404582124502097

theorem tailTrace_3973044 : CollatzResearch.WordTrace tailWord_3973044 prefixEnd_3973044 151117128404582124502097 := by
  unfold tailWord_3973044
  simp only [CollatzResearch.WordTrace]
  refine ⟨72454409709173802369415093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96605879612231736492553457 72454409709173802369415093)
  ·
    refine ⟨6792600910235043972132665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72454409709173802369415093 6792600910235043972132665)
    ·
      refine ⟨5094450682676282979099499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6792600910235043972132665 5094450682676282979099499)
      ·
        refine ⟨7641676024014424468649249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094450682676282979099499 7641676024014424468649249)
        ·
          refine ⟨5731257018010818351486937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7641676024014424468649249 5731257018010818351486937)
          ·
            refine ⟨4298442763508113763615203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731257018010818351486937 4298442763508113763615203)
            ·
              refine ⟨6447664145262170645422805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298442763508113763615203 6447664145262170645422805)
              ·
                refine ⟨151117128404582124502097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6447664145262170645422805 151117128404582124502097)
                ·
                  rfl

theorem cell22_3973044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_3973044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973044 prefixEnd_3973044 := by exact prefixLift 3973044
  have htrace : WordTrace (prefixWord ++ tailWord_3973044) baseStart_3973044 baseEnd_3973044 := by
    simpa [prefixWord, tailWord_3973044, baseEnd_3973044] using wordTrace_append hprefix tailTrace_3973044
  have hstable : (prefixWord ++ tailWord_3973044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973044).length < 2 ^ (prefixWord ++ tailWord_3973044).sum := by decide
  have hdescent : baseEnd_3973044 < baseStart_3973044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973115 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 1, 5]
def baseStart_3973115 : Nat := 118140960795 + 3973115 * 2 ^ 59
def prefixEnd_3973115 : Nat := 4983230072969 + 3 ^ 40 * 3973115 * 2
def baseEnd_3973115 : Nat := 1360078460392218601993655

theorem tailTrace_3973115 : CollatzResearch.WordTrace tailWord_3973115 prefixEnd_3973115 1360078460392218601993655 := by
  unfold tailWord_3973115
  simp only [CollatzResearch.WordTrace]
  refine ⟨144911409001090383864664799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96607606000726922576443199 144911409001090383864664799)
  ·
    refine ⟨217367113501635575796997199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144911409001090383864664799 217367113501635575796997199)
    ·
      refine ⟨326050670252453363695495799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217367113501635575796997199 326050670252453363695495799)
      ·
        refine ⟨489076005378680045543243699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326050670252453363695495799 489076005378680045543243699)
        ·
          refine ⟨733614008068020068314865549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489076005378680045543243699 733614008068020068314865549)
          ·
            refine ⟨275105253025507525618074581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733614008068020068314865549 275105253025507525618074581)
            ·
              refine ⟨6447779367785332631673623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 275105253025507525618074581 6447779367785332631673623)
              ·
                refine ⟨9671669051677998947510435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6447779367785332631673623 9671669051677998947510435)
                ·
                  refine ⟨14507503577516998421265653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671669051677998947510435 14507503577516998421265653)
                  ·
                    refine ⟨1360078460392218601993655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14507503577516998421265653 1360078460392218601993655)
                    ·
                      rfl

theorem cell22_3973115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_3973115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973115 prefixEnd_3973115 := by exact prefixLift 3973115
  have htrace : WordTrace (prefixWord ++ tailWord_3973115) baseStart_3973115 baseEnd_3973115 := by
    simpa [prefixWord, tailWord_3973115, baseEnd_3973115] using wordTrace_append hprefix tailTrace_3973115
  have hstable : (prefixWord ++ tailWord_3973115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973115).length < 2 ^ (prefixWord ++ tailWord_3973115).sum := by decide
  have hdescent : baseEnd_3973115 < baseStart_3973115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973162 : List Nat := [3, 1, 4, 1, 2, 2, 2, 7]
def baseStart_3973162 : Nat := 118140960795 + 3973162 * 2 ^ 59
def prefixEnd_3973162 : Nat := 4983230072969 + 3 ^ 40 * 3973162 * 2
def baseEnd_3973162 : Nat := 151121616605858460674279

theorem tailTrace_3973162 : CollatzResearch.WordTrace tailWord_3973162 prefixEnd_3973162 151121616605858460674279 := by
  unfold tailWord_3973162
  simp only [CollatzResearch.WordTrace]
  refine ⟨36228280807980027722906435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96608748821280073927750493 36228280807980027722906435)
  ·
    refine ⟨54342421211970041584359653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36228280807980027722906435 54342421211970041584359653)
    ·
      refine ⟨10189203977244382797067435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54342421211970041584359653 10189203977244382797067435)
      ·
        refine ⟨15283805965866574195601153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189203977244382797067435 15283805965866574195601153)
        ·
          refine ⟨11462854474399930646700865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15283805965866574195601153 11462854474399930646700865)
          ·
            refine ⟨8597140855799947985025649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11462854474399930646700865 8597140855799947985025649)
            ·
              refine ⟨6447855641849960988769237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8597140855799947985025649 6447855641849960988769237)
              ·
                refine ⟨151121616605858460674279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6447855641849960988769237 151121616605858460674279)
                ·
                  rfl

theorem cell22_3973162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_3973162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973162 prefixEnd_3973162 := by exact prefixLift 3973162
  have htrace : WordTrace (prefixWord ++ tailWord_3973162) baseStart_3973162 baseEnd_3973162 := by
    simpa [prefixWord, tailWord_3973162, baseEnd_3973162] using wordTrace_append hprefix tailTrace_3973162
  have hstable : (prefixWord ++ tailWord_3973162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973162).length < 2 ^ (prefixWord ++ tailWord_3973162).sum := by decide
  have hdescent : baseEnd_3973162 < baseStart_3973162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973166 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_3973166 : Nat := 118140960795 + 3973166 * 2 ^ 59
def prefixEnd_3973166 : Nat := 4983230072969 + 3 ^ 40 * 3973166 * 2
def baseEnd_3973166 : Nat := 1360095918734471468968499

theorem tailTrace_3973166 : CollatzResearch.WordTrace tailWord_3973166 prefixEnd_3973166 1360095918734471468968499 := by
  unfold tailWord_3973166
  simp only [CollatzResearch.WordTrace]
  refine ⟨18114158640488202446846419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96608846082603746383180901 18114158640488202446846419)
  ·
    refine ⟨27171237960732303670269629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18114158640488202446846419 27171237960732303670269629)
    ·
      refine ⟨10189214235274613876351111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27171237960732303670269629 10189214235274613876351111)
      ·
        refine ⟨15283821352911920814526667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189214235274613876351111 15283821352911920814526667)
        ·
          refine ⟨22925732029367881221790001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15283821352911920814526667 22925732029367881221790001)
          ·
            refine ⟨17194299022025910916342501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22925732029367881221790001 17194299022025910916342501)
            ·
              refine ⟨3223931066629858296814219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17194299022025910916342501 3223931066629858296814219)
              ·
                refine ⟨4835896599944787445221329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223931066629858296814219 4835896599944787445221329)
                ·
                  refine ⟨3626922449958590583915997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4835896599944787445221329 3626922449958590583915997)
                  ·
                    refine ⟨1360095918734471468968499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626922449958590583915997 1360095918734471468968499)
                    ·
                      rfl

theorem cell22_3973166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_3973166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973166 prefixEnd_3973166 := by exact prefixLift 3973166
  have htrace : WordTrace (prefixWord ++ tailWord_3973166) baseStart_3973166 baseEnd_3973166 := by
    simpa [prefixWord, tailWord_3973166, baseEnd_3973166] using wordTrace_append hprefix tailTrace_3973166
  have hstable : (prefixWord ++ tailWord_3973166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973166).length < 2 ^ (prefixWord ++ tailWord_3973166).sum := by decide
  have hdescent : baseEnd_3973166 < baseStart_3973166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973194 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 1, 3]
def baseStart_3973194 : Nat := 118140960795 + 3973194 * 2 ^ 59
def prefixEnd_3973194 : Nat := 4983230072969 + 3 ^ 40 * 3973194 * 2
def baseEnd_3973194 : Nat := 1360105503706688729268413

theorem tailTrace_3973194 : CollatzResearch.WordTrace tailWord_3973194 prefixEnd_3973194 1360105503706688729268413 := by
  unfold tailWord_3973194
  simp only [CollatzResearch.WordTrace]
  refine ⟨36228572591951045089197659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96609526911869453571193757 36228572591951045089197659)
  ·
    refine ⟨54342858887926567633796489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36228572591951045089197659 54342858887926567633796489)
    ·
      refine ⟨40757144165944925725347367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54342858887926567633796489 40757144165944925725347367)
      ·
        refine ⟨61135716248917388588021051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40757144165944925725347367 61135716248917388588021051)
        ·
          refine ⟨91703574373376082882031577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61135716248917388588021051 91703574373376082882031577)
          ·
            refine ⟨68777680780032062161523683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91703574373376082882031577 68777680780032062161523683)
            ·
              refine ⟨103166521170048093242285525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68777680780032062161523683 103166521170048093242285525)
              ·
                refine ⟨2417965339923002185366067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 103166521170048093242285525 2417965339923002185366067)
                ·
                  refine ⟨3626948009884503278049101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417965339923002185366067 3626948009884503278049101)
                  ·
                    refine ⟨1360105503706688729268413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3626948009884503278049101 1360105503706688729268413)
                    ·
                      rfl

theorem cell22_3973194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_3973194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973194 prefixEnd_3973194 := by exact prefixLift 3973194
  have htrace : WordTrace (prefixWord ++ tailWord_3973194) baseStart_3973194 baseEnd_3973194 := by
    simpa [prefixWord, tailWord_3973194, baseEnd_3973194] using wordTrace_append hprefix tailTrace_3973194
  have hstable : (prefixWord ++ tailWord_3973194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973194).length < 2 ^ (prefixWord ++ tailWord_3973194).sum := by decide
  have hdescent : baseEnd_3973194 < baseStart_3973194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973295 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_3973295 : Nat := 118140960795 + 3973295 * 2 ^ 59
def prefixEnd_3973295 : Nat := 4983230072969 + 3 ^ 40 * 3973295 * 2
def baseEnd_3973295 : Nat := 1360140078070758132493103

theorem tailTrace_3973295 : CollatzResearch.WordTrace tailWord_3973295 prefixEnd_3973295 1360140078070758132493103 := by
  unfold tailWord_3973295
  simp only [CollatzResearch.WordTrace]
  refine ⟨144917974140438274606217339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96611982760292183070811559 144917974140438274606217339)
  ·
    refine ⟨217376961210657411909326009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144917974140438274606217339 217376961210657411909326009)
    ·
      refine ⟨163032720907993058931994507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217376961210657411909326009 163032720907993058931994507)
      ·
        refine ⟨244549081361989588397991761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163032720907993058931994507 244549081361989588397991761)
        ·
          refine ⟨183411811021492191298493821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244549081361989588397991761 183411811021492191298493821)
          ·
            refine ⟨68779429133059571736935183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183411811021492191298493821 68779429133059571736935183)
            ·
              refine ⟨103169143699589357605402775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68779429133059571736935183 103169143699589357605402775)
              ·
                refine ⟨154753715549384036408104163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103169143699589357605402775 154753715549384036408104163)
                ·
                  refine ⟨232130573324076054612156245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154753715549384036408104163 232130573324076054612156245)
                  ·
                    refine ⟨1360140078070758132493103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232130573324076054612156245 1360140078070758132493103)
                    ·
                      rfl

theorem cell22_3973295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_3973295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973295 prefixEnd_3973295 := by exact prefixLift 3973295
  have htrace : WordTrace (prefixWord ++ tailWord_3973295) baseStart_3973295 baseEnd_3973295 := by
    simpa [prefixWord, tailWord_3973295, baseEnd_3973295] using wordTrace_append hprefix tailTrace_3973295
  have hstable : (prefixWord ++ tailWord_3973295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973295).length < 2 ^ (prefixWord ++ tailWord_3973295).sum := by decide
  have hdescent : baseEnd_3973295 < baseStart_3973295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973329 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_3973329 : Nat := 118140960795 + 3973329 * 2 ^ 59
def prefixEnd_3973329 : Nat := 4983230072969 + 3 ^ 40 * 3973329 * 2
def baseEnd_3973329 : Nat := 1360151716965593377142999

theorem tailTrace_3973329 : CollatzResearch.WordTrace tailWord_3973329 prefixEnd_3973329 1360151716965593377142999 := by
  unfold tailWord_3973329
  simp only [CollatzResearch.WordTrace]
  refine ⟨144919214222315098412955041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96612809481543398941970027 144919214222315098412955041)
  ·
    refine ⟨108689410666736323809716281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144919214222315098412955041 108689410666736323809716281)
    ·
      refine ⟨81517058000052242857287211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108689410666736323809716281 81517058000052242857287211)
      ·
        refine ⟨122275587000078364285930817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81517058000052242857287211 122275587000078364285930817)
        ·
          refine ⟨91706690250058773214448113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122275587000078364285930817 91706690250058773214448113)
          ·
            refine ⟨68780017687544079910836085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91706690250058773214448113 68780017687544079910836085)
            ·
              refine ⟨6448126658207257491640883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68780017687544079910836085 6448126658207257491640883)
              ·
                refine ⟨9672189987310886237461325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448126658207257491640883 9672189987310886237461325)
                ·
                  refine ⟨3627071245241582339047997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9672189987310886237461325 3627071245241582339047997)
                  ·
                    refine ⟨1360151716965593377142999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627071245241582339047997 1360151716965593377142999)
                    ·
                      rfl

theorem cell22_3973329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_3973329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973329 prefixEnd_3973329 := by exact prefixLift 3973329
  have htrace : WordTrace (prefixWord ++ tailWord_3973329) baseStart_3973329 baseEnd_3973329 := by
    simpa [prefixWord, tailWord_3973329, baseEnd_3973329] using wordTrace_append hprefix tailTrace_3973329
  have hstable : (prefixWord ++ tailWord_3973329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973329).length < 2 ^ (prefixWord ++ tailWord_3973329).sum := by decide
  have hdescent : baseEnd_3973329 < baseStart_3973329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973374 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3973374 : Nat := 118140960795 + 3973374 * 2 ^ 59
def prefixEnd_3973374 : Nat := 4983230072969 + 3 ^ 40 * 3973374 * 2
def baseEnd_3973374 : Nat := 1360167121385228259767861

theorem tailTrace_3973374 : CollatzResearch.WordTrace tailWord_3973374 prefixEnd_3973374 1360167121385228259767861 := by
  unfold tailWord_3973374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115106938394008887292897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96613903671434714065562117 18115106938394008887292897)
  ·
    refine ⟨13586330203795506665469673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18115106938394008887292897 13586330203795506665469673)
    ·
      refine ⟨10189747652846629999102255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13586330203795506665469673 10189747652846629999102255)
      ·
        refine ⟨15284621479269944998653383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189747652846629999102255 15284621479269944998653383)
        ·
          refine ⟨22926932218904917497980075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15284621479269944998653383 22926932218904917497980075)
          ·
            refine ⟨34390398328357376246970113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22926932218904917497980075 34390398328357376246970113)
            ·
              refine ⟨25792798746268032185227585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34390398328357376246970113 25792798746268032185227585)
              ·
                refine ⟨19344599059701024138920689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25792798746268032185227585 19344599059701024138920689)
                ·
                  refine ⟨14508449294775768104190517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19344599059701024138920689 14508449294775768104190517)
                  ·
                    refine ⟨1360167121385228259767861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14508449294775768104190517 1360167121385228259767861)
                    ·
                      rfl

theorem cell22_3973374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3973374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973374 prefixEnd_3973374 := by exact prefixLift 3973374
  have htrace : WordTrace (prefixWord ++ tailWord_3973374) baseStart_3973374 baseEnd_3973374 := by
    simpa [prefixWord, tailWord_3973374, baseEnd_3973374] using wordTrace_append hprefix tailTrace_3973374
  have hstable : (prefixWord ++ tailWord_3973374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973374).length < 2 ^ (prefixWord ++ tailWord_3973374).sum := by decide
  have hdescent : baseEnd_3973374 < baseStart_3973374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973387 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 6]
def baseStart_3973387 : Nat := 118140960795 + 3973387 * 2 ^ 59
def prefixEnd_3973387 : Nat := 4983230072969 + 3 ^ 40 * 3973387 * 2
def baseEnd_3973387 : Nat := 453390523850300186397607

theorem tailTrace_3973387 : CollatzResearch.WordTrace tailWord_3973387 prefixEnd_3973387 453390523850300186397607 := by
  unfold tailWord_3973387
  simp only [CollatzResearch.WordTrace]
  refine ⟨144921329656104974318566415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96614219770736649545710943 144921329656104974318566415)
  ·
    refine ⟨217381994484157461477849623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144921329656104974318566415 217381994484157461477849623)
    ·
      refine ⟨326072991726236192216774435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217381994484157461477849623 326072991726236192216774435)
      ·
        refine ⟨489109487589354288325161653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326072991726236192216774435 489109487589354288325161653)
        ·
          refine ⟨45854014461501964530483905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 489109487589354288325161653 45854014461501964530483905)
          ·
            refine ⟨34390510846126473397862929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45854014461501964530483905 34390510846126473397862929)
            ·
              refine ⟨25792883134594855048397197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34390510846126473397862929 25792883134594855048397197)
              ·
                refine ⟨9672331175473070643148949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25792883134594855048397197 9672331175473070643148949)
                ·
                  refine ⟨453390523850300186397607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9672331175473070643148949 453390523850300186397607)
                  ·
                    rfl

theorem cell22_3973387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_3973387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973387 prefixEnd_3973387 := by exact prefixLift 3973387
  have htrace : WordTrace (prefixWord ++ tailWord_3973387) baseStart_3973387 baseEnd_3973387 := by
    simpa [prefixWord, tailWord_3973387, baseEnd_3973387] using wordTrace_append hprefix tailTrace_3973387
  have hstable : (prefixWord ++ tailWord_3973387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973387).length < 2 ^ (prefixWord ++ tailWord_3973387).sum := by decide
  have hdescent : baseEnd_3973387 < baseStart_3973387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973464 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_3973464 : Nat := 118140960795 + 3973464 * 2 ^ 59
def prefixEnd_3973464 : Nat := 4983230072969 + 3 ^ 40 * 3973464 * 2
def baseEnd_3973464 : Nat := 1360197930224498025017585

theorem tailTrace_3973464 : CollatzResearch.WordTrace tailWord_3973464 prefixEnd_3973464 1360197930224498025017585 := by
  unfold tailWord_3973464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72462069038413008234559723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96616092051217344312746297 72462069038413008234559723)
  ·
    refine ⟨108693103557619512351839585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72462069038413008234559723 108693103557619512351839585)
    ·
      refine ⟨81519827668214634263879689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108693103557619512351839585 81519827668214634263879689)
      ·
        refine ⟨61139870751160975697909767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81519827668214634263879689 61139870751160975697909767)
        ·
          refine ⟨91709806126741463546864651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61139870751160975697909767 91709806126741463546864651)
          ·
            refine ⟨137564709190112195320296977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91709806126741463546864651 137564709190112195320296977)
            ·
              refine ⟨103173531892584146490222733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137564709190112195320296977 103173531892584146490222733)
              ·
                refine ⟨38690074459719054933833525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103173531892584146490222733 38690074459719054933833525)
                ·
                  refine ⟨3627194480598661400046893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38690074459719054933833525 3627194480598661400046893)
                  ·
                    refine ⟨1360197930224498025017585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627194480598661400046893 1360197930224498025017585)
                    ·
                      rfl

theorem cell22_3973464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_3973464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973464 prefixEnd_3973464 := by exact prefixLift 3973464
  have htrace : WordTrace (prefixWord ++ tailWord_3973464) baseStart_3973464 baseEnd_3973464 := by
    simpa [prefixWord, tailWord_3973464, baseEnd_3973464] using wordTrace_append hprefix tailTrace_3973464
  have hstable : (prefixWord ++ tailWord_3973464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973464).length < 2 ^ (prefixWord ++ tailWord_3973464).sum := by decide
  have hdescent : baseEnd_3973464 < baseStart_3973464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973549 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3973549 : Nat := 118140960795 + 3973549 * 2 ^ 59
def prefixEnd_3973549 : Nat := 4983230072969 + 3 ^ 40 * 3973549 * 2
def baseEnd_3973549 : Nat := 1360227027461586136642325

theorem tailTrace_3973549 : CollatzResearch.WordTrace tailWord_3973549 prefixEnd_3973549 1360227027461586136642325 := by
  unfold tailWord_3973549
  simp only [CollatzResearch.WordTrace]
  refine ⟨144927238281518075985963701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96618158854345383990642467 144927238281518075985963701)
  ·
    refine ⟨13586928588892319623684097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 144927238281518075985963701 13586928588892319623684097)
    ·
      refine ⟨10190196441669239717763073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13586928588892319623684097 10190196441669239717763073)
      ·
        refine ⟨7642647331251929788322305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10190196441669239717763073 7642647331251929788322305)
        ·
          refine ⟨5731985498438947341241729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7642647331251929788322305 5731985498438947341241729)
          ·
            refine ⟨4298989123829210505931297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731985498438947341241729 4298989123829210505931297)
            ·
              refine ⟨3224241842871907879448473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298989123829210505931297 3224241842871907879448473)
              ·
                refine ⟨2418181382153930909586355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224241842871907879448473 2418181382153930909586355)
                ·
                  refine ⟨3627272073230896364379533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418181382153930909586355 3627272073230896364379533)
                  ·
                    refine ⟨1360227027461586136642325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627272073230896364379533 1360227027461586136642325)
                    ·
                      rfl

theorem cell22_3973549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3973549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973549 prefixEnd_3973549 := by exact prefixLift 3973549
  have htrace : WordTrace (prefixWord ++ tailWord_3973549) baseStart_3973549 baseEnd_3973549 := by
    simpa [prefixWord, tailWord_3973549, baseEnd_3973549] using wordTrace_append hprefix tailTrace_3973549
  have hstable : (prefixWord ++ tailWord_3973549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973549).length < 2 ^ (prefixWord ++ tailWord_3973549).sum := by decide
  have hdescent : baseEnd_3973549 < baseStart_3973549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973554 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_3973554 : Nat := 118140960795 + 3973554 * 2 ^ 59
def prefixEnd_3973554 : Nat := 4983230072969 + 3 ^ 40 * 3973554 * 2
def baseEnd_3973554 : Nat := 1360228739063767790267309

theorem tailTrace_3973554 : CollatzResearch.WordTrace tailWord_3973554 prefixEnd_3973554 1360228739063767790267309 := by
  unfold tailWord_3973554
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231855161624990459973929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96618280430999974559930477 36231855161624990459973929)
  ·
    refine ⟨27173891371218742844980447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36231855161624990459973929 27173891371218742844980447)
    ·
      refine ⟨40760837056828114267470671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27173891371218742844980447 40760837056828114267470671)
      ·
        refine ⟨61141255585242171401206007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40760837056828114267470671 61141255585242171401206007)
        ·
          refine ⟨91711883377863257101809011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61141255585242171401206007 91711883377863257101809011)
          ·
            refine ⟨137567825066794885652713517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91711883377863257101809011 137567825066794885652713517)
            ·
              refine ⟨51587934400048082119767569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137567825066794885652713517 51587934400048082119767569)
              ·
                refine ⟨38690950800036061589825677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51587934400048082119767569 38690950800036061589825677)
                ·
                  refine ⟨14509106550013523096184629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38690950800036061589825677 14509106550013523096184629)
                  ·
                    refine ⟨1360228739063767790267309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14509106550013523096184629 1360228739063767790267309)
                    ·
                      rfl

theorem cell22_3973554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_3973554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973554 prefixEnd_3973554 := by exact prefixLift 3973554
  have htrace : WordTrace (prefixWord ++ tailWord_3973554) baseStart_3973554 baseEnd_3973554 := by
    simpa [prefixWord, tailWord_3973554, baseEnd_3973554] using wordTrace_append hprefix tailTrace_3973554
  have hstable : (prefixWord ++ tailWord_3973554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973554).length < 2 ^ (prefixWord ++ tailWord_3973554).sum := by decide
  have hdescent : baseEnd_3973554 < baseStart_3973554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973590 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_3973590 : Nat := 118140960795 + 3973590 * 2 ^ 59
def prefixEnd_3973590 : Nat := 4983230072969 + 3 ^ 40 * 3973590 * 2
def baseEnd_3973590 : Nat := 453413687533158565455733

theorem tailTrace_3973590 : CollatzResearch.WordTrace tailWord_3973590 prefixEnd_3973590 453413687533158565455733 := by
  unfold tailWord_3973590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058045854648096249262889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96619155782913026658804149 9058045854648096249262889)
  ·
    refine ⟨6793534390986072186947167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9058045854648096249262889 6793534390986072186947167)
    ·
      refine ⟨10190301586479108280420751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6793534390986072186947167 10190301586479108280420751)
      ·
        refine ⟨15285452379718662420631127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10190301586479108280420751 15285452379718662420631127)
        ·
          refine ⟨22928178569577993630946691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15285452379718662420631127 22928178569577993630946691)
          ·
            refine ⟨34392267854366990446420037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22928178569577993630946691 34392267854366990446420037)
            ·
              refine ⟨6448550222693810708703757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34392267854366990446420037 6448550222693810708703757)
              ·
                refine ⟨2418206333510179015763909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6448550222693810708703757 2418206333510179015763909)
                ·
                  refine ⟨453413687533158565455733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418206333510179015763909 453413687533158565455733)
                  ·
                    rfl

theorem cell22_3973590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_3973590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973590 prefixEnd_3973590 := by exact prefixLift 3973590
  have htrace : WordTrace (prefixWord ++ tailWord_3973590) baseStart_3973590 baseEnd_3973590 := by
    simpa [prefixWord, tailWord_3973590, baseEnd_3973590] using wordTrace_append hprefix tailTrace_3973590
  have hstable : (prefixWord ++ tailWord_3973590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973590).length < 2 ^ (prefixWord ++ tailWord_3973590).sum := by decide
  have hdescent : baseEnd_3973590 < baseStart_3973590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973633 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3973633 : Nat := 118140960795 + 3973633 * 2 ^ 59
def prefixEnd_3973633 : Nat := 4983230072969 + 3 ^ 40 * 3973633 * 2
def baseEnd_3973633 : Nat := 1360255782378237917542067

theorem tailTrace_3973633 : CollatzResearch.WordTrace tailWord_3973633 prefixEnd_3973633 1360255782378237917542067 := by
  unfold tailWord_3973633
  simp only [CollatzResearch.WordTrace]
  refine ⟨144930302013213758332021553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96620201342142505554681035 144930302013213758332021553)
  ·
    refine ⟨108697726509910318749016165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144930302013213758332021553 108697726509910318749016165)
    ·
      refine ⟨20380823720608184765440531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108697726509910318749016165 20380823720608184765440531)
      ·
        refine ⟨30571235580912277148160797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20380823720608184765440531 30571235580912277148160797)
        ·
          refine ⟨11464213342842103930560299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30571235580912277148160797 11464213342842103930560299)
          ·
            refine ⟨17196320014263155895840449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464213342842103930560299 17196320014263155895840449)
            ·
              refine ⟨12897240010697366921880337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17196320014263155895840449 12897240010697366921880337)
              ·
                refine ⟨9672930008023025191410253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12897240010697366921880337 9672930008023025191410253)
                ·
                  refine ⟨3627348753008634446778845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9672930008023025191410253 3627348753008634446778845)
                  ·
                    refine ⟨1360255782378237917542067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627348753008634446778845 1360255782378237917542067)
                    ·
                      rfl

theorem cell22_3973633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3973633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973633 prefixEnd_3973633 := by exact prefixLift 3973633
  have htrace : WordTrace (prefixWord ++ tailWord_3973633) baseStart_3973633 baseEnd_3973633 := by
    simpa [prefixWord, tailWord_3973633, baseEnd_3973633] using wordTrace_append hprefix tailTrace_3973633
  have hstable : (prefixWord ++ tailWord_3973633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973633).length < 2 ^ (prefixWord ++ tailWord_3973633).sum := by decide
  have hdescent : baseEnd_3973633 < baseStart_3973633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973646 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_3973646 : Nat := 118140960795 + 3973646 * 2 ^ 59
def prefixEnd_3973646 : Nat := 4983230072969 + 3 ^ 40 * 3973646 * 2
def baseEnd_3973646 : Nat := 453420077514636738989009

theorem tailTrace_3973646 : CollatzResearch.WordTrace tailWord_3973646 prefixEnd_3973646 453420077514636738989009 := by
  unfold tailWord_3973646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18116347020270832694030599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96620517441444441034829861 18116347020270832694030599)
  ·
    refine ⟨27174520530406249041045899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18116347020270832694030599 27174520530406249041045899)
    ·
      refine ⟨40761780795609373561568849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27174520530406249041045899 40761780795609373561568849)
      ·
        refine ⟨30571335596707030171176637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40761780795609373561568849 30571335596707030171176637)
        ·
          refine ⟨11464250848765136314191239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30571335596707030171176637 11464250848765136314191239)
          ·
            refine ⟨17196376273147704471286859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464250848765136314191239 17196376273147704471286859)
            ·
              refine ⟨25794564409721556706930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17196376273147704471286859 25794564409721556706930289)
              ·
                refine ⟨19345923307291167530197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25794564409721556706930289 19345923307291167530197717)
                ·
                  refine ⟨453420077514636738989009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19345923307291167530197717 453420077514636738989009)
                  ·
                    rfl

theorem cell22_3973646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_3973646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973646 prefixEnd_3973646 := by exact prefixLift 3973646
  have htrace : WordTrace (prefixWord ++ tailWord_3973646) baseStart_3973646 baseEnd_3973646 := by
    simpa [prefixWord, tailWord_3973646, baseEnd_3973646] using wordTrace_append hprefix tailTrace_3973646
  have hstable : (prefixWord ++ tailWord_3973646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973646).length < 2 ^ (prefixWord ++ tailWord_3973646).sum := by decide
  have hdescent : baseEnd_3973646 < baseStart_3973646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973667 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 1, 3]
def baseStart_3973667 : Nat := 118140960795 + 3973667 * 2 ^ 59
def prefixEnd_3973667 : Nat := 4983230072969 + 3 ^ 40 * 3973667 * 2
def baseEnd_3973667 : Nat := 1360267421273073162191963

theorem tailTrace_3973667 : CollatzResearch.WordTrace tailWord_3973667 prefixEnd_3973667 1360267421273073162191963 := by
  unfold tailWord_3973667
  simp only [CollatzResearch.WordTrace]
  refine ⟨144931542095090582138759255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96621028063393721425839503 144931542095090582138759255)
  ·
    refine ⟨217397313142635873208138883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144931542095090582138759255 217397313142635873208138883)
    ·
      refine ⟨326095969713953809812208325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217397313142635873208138883 326095969713953809812208325)
      ·
        refine ⟨61142994321366339339789061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326095969713953809812208325 61142994321366339339789061)
        ·
          refine ⟨11464311435256188626210449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61142994321366339339789061 11464311435256188626210449)
          ·
            refine ⟨8598233576442141469657837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11464311435256188626210449 8598233576442141469657837)
            ·
              refine ⟨3224337591165803051121689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8598233576442141469657837 3224337591165803051121689)
              ·
                refine ⟨2418253193374352288341267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224337591165803051121689 2418253193374352288341267)
                ·
                  refine ⟨3627379790061528432511901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418253193374352288341267 3627379790061528432511901)
                  ·
                    refine ⟨1360267421273073162191963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627379790061528432511901 1360267421273073162191963)
                    ·
                      rfl

theorem cell22_3973667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 3].length) (baseStart_3973667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973667 prefixEnd_3973667 := by exact prefixLift 3973667
  have htrace : WordTrace (prefixWord ++ tailWord_3973667) baseStart_3973667 baseEnd_3973667 := by
    simpa [prefixWord, tailWord_3973667, baseEnd_3973667] using wordTrace_append hprefix tailTrace_3973667
  have hstable : (prefixWord ++ tailWord_3973667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973667).length < 2 ^ (prefixWord ++ tailWord_3973667).sum := by decide
  have hdescent : baseEnd_3973667 < baseStart_3973667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973693 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3973693 : Nat := 118140960795 + 3973693 * 2 ^ 59
def prefixEnd_3973693 : Nat := 4983230072969 + 3 ^ 40 * 3973693 * 2
def baseEnd_3973693 : Nat := 1360276321604417761041883

theorem tailTrace_3973693 : CollatzResearch.WordTrace tailWord_3973693 prefixEnd_3973693 1360276321604417761041883 := by
  unfold tailWord_3973693
  simp only [CollatzResearch.WordTrace]
  refine ⟨144932490392996388579205733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96621660261997592386137155 144932490392996388579205733)
  ·
    refine ⟨27174841948686822858601075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144932490392996388579205733 27174841948686822858601075)
    ·
      refine ⟨40762262923030234287901613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27174841948686822858601075 40762262923030234287901613)
      ·
        refine ⟨15285848596136337857963105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40762262923030234287901613 15285848596136337857963105)
        ·
          refine ⟨11464386447102253393472329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15285848596136337857963105 11464386447102253393472329)
          ·
            refine ⟨8598289835326690045104247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11464386447102253393472329 8598289835326690045104247)
            ·
              refine ⟨12897434752990035067656371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8598289835326690045104247 12897434752990035067656371)
              ·
                refine ⟨19346152129485052601484557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12897434752990035067656371 19346152129485052601484557)
                ·
                  refine ⟨7254807048556894725556709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19346152129485052601484557 7254807048556894725556709)
                  ·
                    refine ⟨1360276321604417761041883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7254807048556894725556709 1360276321604417761041883)
                    ·
                      rfl

theorem cell22_3973693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3973693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973693 prefixEnd_3973693 := by exact prefixLift 3973693
  have htrace : WordTrace (prefixWord ++ tailWord_3973693) baseStart_3973693 baseEnd_3973693 := by
    simpa [prefixWord, tailWord_3973693, baseEnd_3973693] using wordTrace_append hprefix tailTrace_3973693
  have hstable : (prefixWord ++ tailWord_3973693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973693).length < 2 ^ (prefixWord ++ tailWord_3973693).sum := by decide
  have hdescent : baseEnd_3973693 < baseStart_3973693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973706 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3973706 : Nat := 118140960795 + 3973706 * 2 ^ 59
def prefixEnd_3973706 : Nat := 4983230072969 + 3 ^ 40 * 3973706 * 2
def baseEnd_3973706 : Nat := 1360280771770090060466843

theorem tailTrace_3973706 : CollatzResearch.WordTrace tailWord_3973706 prefixEnd_3973706 1360280771770090060466843 := by
  unfold tailWord_3973706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36233241135487322949857243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96621976361299527866285981 36233241135487322949857243)
  ·
    refine ⟨54349861703230984424785865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36233241135487322949857243 54349861703230984424785865)
    ·
      refine ⟨40762396277423238318589399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54349861703230984424785865 40762396277423238318589399)
      ·
        refine ⟨61143594416134857477884099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40762396277423238318589399 61143594416134857477884099)
        ·
          refine ⟨91715391624202286216826149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61143594416134857477884099 91715391624202286216826149)
          ·
            refine ⟨17196635929537928665654903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91715391624202286216826149 17196635929537928665654903)
            ·
              refine ⟨25794953894306892998482355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17196635929537928665654903 25794953894306892998482355)
              ·
                refine ⟨38692430841460339497723533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25794953894306892998482355 38692430841460339497723533)
                ·
                  refine ⟨14509661565547627311646325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38692430841460339497723533 14509661565547627311646325)
                  ·
                    refine ⟨1360280771770090060466843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14509661565547627311646325 1360280771770090060466843)
                    ·
                      rfl

theorem cell22_3973706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3973706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973706 prefixEnd_3973706 := by exact prefixLift 3973706
  have htrace : WordTrace (prefixWord ++ tailWord_3973706) baseStart_3973706 baseEnd_3973706 := by
    simpa [prefixWord, tailWord_3973706, baseEnd_3973706] using wordTrace_append hprefix tailTrace_3973706
  have hstable : (prefixWord ++ tailWord_3973706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973706).length < 2 ^ (prefixWord ++ tailWord_3973706).sum := by decide
  have hdescent : baseEnd_3973706 < baseStart_3973706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973708 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_3973708 : Nat := 118140960795 + 3973708 * 2 ^ 59
def prefixEnd_3973708 : Nat := 4983230072969 + 3 ^ 40 * 3973708 * 2
def baseEnd_3973708 : Nat := 453427152136987573972279

theorem tailTrace_3973708 : CollatzResearch.WordTrace tailWord_3973708 prefixEnd_3973708 453427152136987573972279 := by
  unfold tailWord_3973708
  simp only [CollatzResearch.WordTrace]
  refine ⟨72466518743971023070500889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96622024991961364094001185 72466518743971023070500889)
  ·
    refine ⟨54349889057978267302875667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72466518743971023070500889 54349889057978267302875667)
    ·
      refine ⟨81524833586967400954313501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54349889057978267302875667 81524833586967400954313501)
      ·
        refine ⟨30571812595112775357867563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81524833586967400954313501 30571812595112775357867563)
        ·
          refine ⟨45857718892669163036801345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30571812595112775357867563 45857718892669163036801345)
          ·
            refine ⟨34393289169501872277601009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45857718892669163036801345 34393289169501872277601009)
            ·
              refine ⟨25794966877126404208200757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34393289169501872277601009 25794966877126404208200757)
              ·
                refine ⟨2418278144730600394518821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25794966877126404208200757 2418278144730600394518821)
                ·
                  refine ⟨453427152136987573972279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418278144730600394518821 453427152136987573972279)
                  ·
                    rfl

theorem cell22_3973708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_3973708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973708 prefixEnd_3973708 := by exact prefixLift 3973708
  have htrace : WordTrace (prefixWord ++ tailWord_3973708) baseStart_3973708 baseEnd_3973708 := by
    simpa [prefixWord, tailWord_3973708, baseEnd_3973708] using wordTrace_append hprefix tailTrace_3973708
  have hstable : (prefixWord ++ tailWord_3973708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973708).length < 2 ^ (prefixWord ++ tailWord_3973708).sum := by decide
  have hdescent : baseEnd_3973708 < baseStart_3973708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973753 : List Nat := [1, 2, 1, 3, 3, 3, 3, 6]
def baseStart_3973753 : Nat := 118140960795 + 3973753 * 2 ^ 59
def prefixEnd_3973753 : Nat := 4983230072969 + 3 ^ 40 * 3973753 * 2
def baseEnd_3973753 : Nat := 151144095647844178282411

theorem tailTrace_3973753 : CollatzResearch.WordTrace tailWord_3973753 prefixEnd_3973753 151144095647844178282411 := by
  unfold tailWord_3973753
  simp only [CollatzResearch.WordTrace]
  refine ⟨144934678772779018826389913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96623119181852679217593275 144934678772779018826389913)
  ·
    refine ⟨108701009079584264119792435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144934678772779018826389913 108701009079584264119792435)
    ·
      refine ⟨163051513619376396179688653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108701009079584264119792435 163051513619376396179688653)
      ·
        refine ⟨61144317607266148567383245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163051513619376396179688653 61144317607266148567383245)
        ·
          refine ⟨22929119102724805712768717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61144317607266148567383245 22929119102724805712768717)
          ·
            refine ⟨8598419663521802142288269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22929119102724805712768717 8598419663521802142288269)
            ·
              refine ⟨3224407373820675803358101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8598419663521802142288269 3224407373820675803358101)
              ·
                refine ⟨151144095647844178282411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3224407373820675803358101 151144095647844178282411)
                ·
                  rfl

theorem cell22_3973753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 6].length) (baseStart_3973753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973753 prefixEnd_3973753 := by exact prefixLift 3973753
  have htrace : WordTrace (prefixWord ++ tailWord_3973753) baseStart_3973753 baseEnd_3973753 := by
    simpa [prefixWord, tailWord_3973753, baseEnd_3973753] using wordTrace_append hprefix tailTrace_3973753
  have hstable : (prefixWord ++ tailWord_3973753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973753).length < 2 ^ (prefixWord ++ tailWord_3973753).sum := by decide
  have hdescent : baseEnd_3973753 < baseStart_3973753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973785 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 1, 3]
def baseStart_3973785 : Nat := 118140960795 + 3973785 * 2 ^ 59
def prefixEnd_3973785 : Nat := 4983230072969 + 3 ^ 40 * 3973785 * 2
def baseEnd_3973785 : Nat := 1360307815084560187741601

theorem tailTrace_3973785 : CollatzResearch.WordTrace tailWord_3973785 prefixEnd_3973785 1360307815084560187741601 := by
  unfold tailWord_3973785
  simp only [CollatzResearch.WordTrace]
  refine ⟨144935845908663088291554809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96623897272442058861036539 144935845908663088291554809)
  ·
    refine ⟨108701884431497316218666107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144935845908663088291554809 108701884431497316218666107)
    ·
      refine ⟨163052826647245974327999161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108701884431497316218666107 163052826647245974327999161)
      ·
        refine ⟨122289619985434480745999371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163052826647245974327999161 122289619985434480745999371)
        ·
          refine ⟨183434429978151721118999057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122289619985434480745999371 183434429978151721118999057)
          ·
            refine ⟨137575822483613790839249293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183434429978151721118999057 137575822483613790839249293)
            ·
              refine ⟨51590933431355171564718485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137575822483613790839249293 51590933431355171564718485)
              ·
                refine ⟨2418325004594773667096179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51590933431355171564718485 2418325004594773667096179)
                ·
                  refine ⟨3627487506892160500644269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418325004594773667096179 3627487506892160500644269)
                  ·
                    refine ⟨1360307815084560187741601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627487506892160500644269 1360307815084560187741601)
                    ·
                      rfl

theorem cell22_3973785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_3973785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973785 prefixEnd_3973785 := by exact prefixLift 3973785
  have htrace : WordTrace (prefixWord ++ tailWord_3973785) baseStart_3973785 baseEnd_3973785 := by
    simpa [prefixWord, tailWord_3973785, baseEnd_3973785] using wordTrace_append hprefix tailTrace_3973785
  have hstable : (prefixWord ++ tailWord_3973785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973785).length < 2 ^ (prefixWord ++ tailWord_3973785).sum := by decide
  have hdescent : baseEnd_3973785 < baseStart_3973785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973892 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_3973892 : Nat := 118140960795 + 3973892 * 2 ^ 59
def prefixEnd_3973892 : Nat := 4983230072969 + 3 ^ 40 * 3973892 * 2
def baseEnd_3973892 : Nat := 1360344443371247575316273

theorem tailTrace_3973892 : CollatzResearch.WordTrace tailWord_3973892 prefixEnd_3973892 1360344443371247575316273 := by
  unfold tailWord_3973892
  simp only [CollatzResearch.WordTrace]
  refine ⟨72469874259637722782849965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96626499012850297043799953 72469874259637722782849965)
  ·
    refine ⟨27176202847364146043568737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72469874259637722782849965 27176202847364146043568737)
    ·
      refine ⟨20382152135523109532676553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27176202847364146043568737 20382152135523109532676553)
      ·
        refine ⟨15286614101642332149507415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20382152135523109532676553 15286614101642332149507415)
        ·
          refine ⟨22929921152463498224261123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15286614101642332149507415 22929921152463498224261123)
          ·
            refine ⟨34394881728695247336391685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22929921152463498224261123 34394881728695247336391685)
            ·
              refine ⟨6449040324130358875573441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34394881728695247336391685 6449040324130358875573441)
              ·
                refine ⟨4836780243097769156680081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449040324130358875573441 4836780243097769156680081)
                ·
                  refine ⟨3627585182323326867510061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836780243097769156680081 3627585182323326867510061)
                  ·
                    refine ⟨1360344443371247575316273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627585182323326867510061 1360344443371247575316273)
                    ·
                      rfl

theorem cell22_3973892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_3973892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973892 prefixEnd_3973892 := by exact prefixLift 3973892
  have htrace : WordTrace (prefixWord ++ tailWord_3973892) baseStart_3973892 baseEnd_3973892 := by
    simpa [prefixWord, tailWord_3973892, baseEnd_3973892] using wordTrace_append hprefix tailTrace_3973892
  have hstable : (prefixWord ++ tailWord_3973892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973892).length < 2 ^ (prefixWord ++ tailWord_3973892).sum := by decide
  have hdescent : baseEnd_3973892 < baseStart_3973892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973920 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_3973920 : Nat := 118140960795 + 3973920 * 2 ^ 59
def prefixEnd_3973920 : Nat := 4983230072969 + 3 ^ 40 * 3973920 * 2
def baseEnd_3973920 : Nat := 1360354028343464835616187

theorem tailTrace_3973920 : CollatzResearch.WordTrace tailWord_3973920 prefixEnd_3973920 1360354028343464835616187 := by
  unfold tailWord_3973920
  simp only [CollatzResearch.WordTrace]
  refine ⟨72470384881587003173859607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96627179842116004231812809 72470384881587003173859607)
  ·
    refine ⟨108705577322380504760789411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72470384881587003173859607 108705577322380504760789411)
    ·
      refine ⟨163058365983570757141184117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108705577322380504760789411 163058365983570757141184117)
      ·
        refine ⟨15286721810959758481986011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163058365983570757141184117 15286721810959758481986011)
        ·
          refine ⟨22930082716439637722979017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15286721810959758481986011 22930082716439637722979017)
          ·
            refine ⟨17197562037329728292234263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22930082716439637722979017 17197562037329728292234263)
            ·
              refine ⟨25796343055994592438351395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17197562037329728292234263 25796343055994592438351395)
              ·
                refine ⟨38694514583991888657527093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25796343055994592438351395 38694514583991888657527093)
                ·
                  refine ⟨3627610742249239561643165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38694514583991888657527093 3627610742249239561643165)
                  ·
                    refine ⟨1360354028343464835616187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627610742249239561643165 1360354028343464835616187)
                    ·
                      rfl

theorem cell22_3973920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_3973920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973920 prefixEnd_3973920 := by exact prefixLift 3973920
  have htrace : WordTrace (prefixWord ++ tailWord_3973920) baseStart_3973920 baseEnd_3973920 := by
    simpa [prefixWord, tailWord_3973920, baseEnd_3973920] using wordTrace_append hprefix tailTrace_3973920
  have hstable : (prefixWord ++ tailWord_3973920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973920).length < 2 ^ (prefixWord ++ tailWord_3973920).sum := by decide
  have hdescent : baseEnd_3973920 < baseStart_3973920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3973924 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_3973924 : Nat := 118140960795 + 3973924 * 2 ^ 59
def prefixEnd_3973924 : Nat := 4983230072969 + 3 ^ 40 * 3973924 * 2
def baseEnd_3973924 : Nat := 1360355397625210158516175

theorem tailTrace_3973924 : CollatzResearch.WordTrace tailWord_3973924 prefixEnd_3973924 1360355397625210158516175 := by
  unfold tailWord_3973924
  simp only [CollatzResearch.WordTrace]
  refine ⟨72470457827579757515432413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96627277103439676687243217 72470457827579757515432413)
  ·
    refine ⟨27176421685342409068287155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72470457827579757515432413 27176421685342409068287155)
    ·
      refine ⟨40764632528013613602430733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27176421685342409068287155 40764632528013613602430733)
      ·
        refine ⟨15286737198005105100911525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40764632528013613602430733 15286737198005105100911525)
        ·
          refine ⟨2866263224625957206420911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15286737198005105100911525 2866263224625957206420911)
          ·
            refine ⟨4299394836938935809631367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866263224625957206420911 4299394836938935809631367)
            ·
              refine ⟨6449092255408403714447051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299394836938935809631367 6449092255408403714447051)
              ·
                refine ⟨9673638383112605571670577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449092255408403714447051 9673638383112605571670577)
                ·
                  refine ⟨7255228787334454178752933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9673638383112605571670577 7255228787334454178752933)
                  ·
                    refine ⟨1360355397625210158516175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255228787334454178752933 1360355397625210158516175)
                    ·
                      rfl

theorem cell22_3973924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_3973924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3973924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3973924 prefixEnd_3973924 := by exact prefixLift 3973924
  have htrace : WordTrace (prefixWord ++ tailWord_3973924) baseStart_3973924 baseEnd_3973924 := by
    simpa [prefixWord, tailWord_3973924, baseEnd_3973924] using wordTrace_append hprefix tailTrace_3973924
  have hstable : (prefixWord ++ tailWord_3973924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3973924).length < 2 ^ (prefixWord ++ tailWord_3973924).sum := by decide
  have hdescent : baseEnd_3973924 < baseStart_3973924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3973924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974008 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_3974008 : Nat := 118140960795 + 3974008 * 2 ^ 59
def prefixEnd_3974008 : Nat := 4983230072969 + 3 ^ 40 * 3974008 * 2
def baseEnd_3974008 : Nat := 1360384152541861939415917

theorem tailTrace_3974008 : CollatzResearch.WordTrace tailWord_3974008 prefixEnd_3974008 1360384152541861939415917 := by
  unfold tailWord_3974008
  simp only [CollatzResearch.WordTrace]
  refine ⟨72471989693427598688461339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96629319591236798251281785 72471989693427598688461339)
  ·
    refine ⟨108707984540141398032692009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72471989693427598688461339 108707984540141398032692009)
    ·
      refine ⟨81530988405106048524519007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108707984540141398032692009 81530988405106048524519007)
      ·
        refine ⟨122296482607659072786778511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81530988405106048524519007 122296482607659072786778511)
        ·
          refine ⟨183444723911488609180167767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122296482607659072786778511 183444723911488609180167767)
          ·
            refine ⟨275167085867232913770251651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183444723911488609180167767 275167085867232913770251651)
            ·
              refine ⟨412750628800849370655377477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275167085867232913770251651 412750628800849370655377477)
              ·
                refine ⟨77390742900159256997883277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412750628800849370655377477 77390742900159256997883277)
                ·
                  refine ⟨29021528587559721374206229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77390742900159256997883277 29021528587559721374206229)
                  ·
                    refine ⟨1360384152541861939415917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29021528587559721374206229 1360384152541861939415917)
                    ·
                      rfl

theorem cell22_3974008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_3974008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974008 prefixEnd_3974008 := by exact prefixLift 3974008
  have htrace : WordTrace (prefixWord ++ tailWord_3974008) baseStart_3974008 baseEnd_3974008 := by
    simpa [prefixWord, tailWord_3974008, baseEnd_3974008] using wordTrace_append hprefix tailTrace_3974008
  have hstable : (prefixWord ++ tailWord_3974008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974008).length < 2 ^ (prefixWord ++ tailWord_3974008).sum := by decide
  have hdescent : baseEnd_3974008 < baseStart_3974008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974018 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3974018 : Nat := 118140960795 + 3974018 * 2 ^ 59
def prefixEnd_3974018 : Nat := 4983230072969 + 3 ^ 40 * 3974018 * 2
def baseEnd_3974018 : Nat := 453462525248741748888629

theorem tailTrace_3974018 : CollatzResearch.WordTrace tailWord_3974018 prefixEnd_3974018 453462525248741748888629 := by
  unfold tailWord_3974018
  simp only [CollatzResearch.WordTrace]
  refine ⟨36236086029204742271196677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96629562744545979389857805 36236086029204742271196677)
  ·
    refine ⟨6794266130475889175849377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36236086029204742271196677 6794266130475889175849377)
    ·
      refine ⟨5095699597856916881887033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6794266130475889175849377 5095699597856916881887033)
      ·
        refine ⟨3821774698392687661415275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5095699597856916881887033 3821774698392687661415275)
        ·
          refine ⟨5732662047589031492122913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821774698392687661415275 5732662047589031492122913)
          ·
            refine ⟨4299496535691773619092185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5732662047589031492122913 4299496535691773619092185)
            ·
              refine ⟨3224622401768830214319139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4299496535691773619092185 3224622401768830214319139)
              ·
                refine ⟨4836933602653245321478709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224622401768830214319139 4836933602653245321478709)
                ·
                  refine ⟨453462525248741748888629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4836933602653245321478709 453462525248741748888629)
                  ·
                    rfl

theorem cell22_3974018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3974018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974018 prefixEnd_3974018 := by exact prefixLift 3974018
  have htrace : WordTrace (prefixWord ++ tailWord_3974018) baseStart_3974018 baseEnd_3974018 := by
    simpa [prefixWord, tailWord_3974018, baseEnd_3974018] using wordTrace_append hprefix tailTrace_3974018
  have hstable : (prefixWord ++ tailWord_3974018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974018).length < 2 ^ (prefixWord ++ tailWord_3974018).sum := by decide
  have hdescent : baseEnd_3974018 < baseStart_3974018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974106 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_3974106 : Nat := 118140960795 + 3974106 * 2 ^ 59
def prefixEnd_3974106 : Nat := 4983230072969 + 3 ^ 40 * 3974106 * 2
def baseEnd_3974106 : Nat := 1360417699944622350465617

theorem tailTrace_3974106 : CollatzResearch.WordTrace tailWord_3974106 prefixEnd_3974106 1360417699944622350465617 := by
  unfold tailWord_3974106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36236888435125040028497543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96631702493666773409326781 36236888435125040028497543)
  ·
    refine ⟨54355332652687560042746315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36236888435125040028497543 54355332652687560042746315)
    ·
      refine ⟨81532998979031340064119473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54355332652687560042746315 81532998979031340064119473)
      ·
        refine ⟨61149749234273505048089605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81532998979031340064119473 61149749234273505048089605)
        ·
          refine ⟨11465577981426282196516801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61149749234273505048089605 11465577981426282196516801)
          ·
            refine ⟨8599183486069711647387601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11465577981426282196516801 8599183486069711647387601)
            ·
              refine ⟨6449387614552283735540701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599183486069711647387601 6449387614552283735540701)
              ·
                refine ⟨2418520355457106400827763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6449387614552283735540701 2418520355457106400827763)
                ·
                  refine ⟨3627780533185659601241645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418520355457106400827763 3627780533185659601241645)
                  ·
                    refine ⟨1360417699944622350465617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627780533185659601241645 1360417699944622350465617)
                    ·
                      rfl

theorem cell22_3974106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_3974106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974106 prefixEnd_3974106 := by exact prefixLift 3974106
  have htrace : WordTrace (prefixWord ++ tailWord_3974106) baseStart_3974106 baseEnd_3974106 := by
    simpa [prefixWord, tailWord_3974106, baseEnd_3974106] using wordTrace_append hprefix tailTrace_3974106
  have hstable : (prefixWord ++ tailWord_3974106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974106).length < 2 ^ (prefixWord ++ tailWord_3974106).sum := by decide
  have hdescent : baseEnd_3974106 < baseStart_3974106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974119 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 5]
def baseStart_3974119 : Nat := 118140960795 + 3974119 * 2 ^ 59
def prefixEnd_3974119 : Nat := 4983230072969 + 3 ^ 40 * 3974119 * 2
def baseEnd_3974119 : Nat := 453474050036764883296859

theorem tailTrace_3974119 : CollatzResearch.WordTrace tailWord_3974119 prefixEnd_3974119 453474050036764883296859 := by
  unfold tailWord_3974119
  simp only [CollatzResearch.WordTrace]
  refine ⟨144948027889453063334213411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96632018592968708889475607 144948027889453063334213411)
  ·
    refine ⟨217422041834179595001320117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144948027889453063334213411 217422041834179595001320117)
    ·
      refine ⟨20383316421954337031373761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217422041834179595001320117 20383316421954337031373761)
      ·
        refine ⟨15287487316465752773530321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20383316421954337031373761 15287487316465752773530321)
        ·
          refine ⟨11465615487349314580147741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15287487316465752773530321 11465615487349314580147741)
          ·
            refine ⟨4299605807755992967555403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11465615487349314580147741 4299605807755992967555403)
            ·
              refine ⟨6449408711633989451333105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299605807755992967555403 6449408711633989451333105)
              ·
                refine ⟨4837056533725492088499829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449408711633989451333105 4837056533725492088499829)
                ·
                  refine ⟨453474050036764883296859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4837056533725492088499829 453474050036764883296859)
                  ·
                    rfl

theorem cell22_3974119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 5].length) (baseStart_3974119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974119 prefixEnd_3974119 := by exact prefixLift 3974119
  have htrace : WordTrace (prefixWord ++ tailWord_3974119) baseStart_3974119 baseEnd_3974119 := by
    simpa [prefixWord, tailWord_3974119, baseEnd_3974119] using wordTrace_append hprefix tailTrace_3974119
  have hstable : (prefixWord ++ tailWord_3974119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974119).length < 2 ^ (prefixWord ++ tailWord_3974119).sum := by decide
  have hdescent : baseEnd_3974119 < baseStart_3974119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974175 : List Nat := [1, 1, 2, 4, 1, 3, 10]
def baseStart_3974175 : Nat := 118140960795 + 3974175 * 2 ^ 59
def prefixEnd_3974175 : Nat := 4983230072969 + 3 ^ 40 * 3974175 * 2
def baseEnd_3974175 : Nat := 50386715557582561870015

theorem tailTrace_3974175 : CollatzResearch.WordTrace tailWord_3974175 prefixEnd_3974175 50386715557582561870015 := by
  unfold tailWord_3974175
  simp only [CollatzResearch.WordTrace]
  refine ⟨144950070377250184898251979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96633380251500123265501319 144950070377250184898251979)
  ·
    refine ⟨217425105565875277347377969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144950070377250184898251979 217425105565875277347377969)
    ·
      refine ⟨163068829174406458010533477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217425105565875277347377969 163068829174406458010533477)
      ·
        refine ⟨30575405470201210876975027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163068829174406458010533477 30575405470201210876975027)
        ·
          refine ⟨45863108205301816315462541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30575405470201210876975027 45863108205301816315462541)
          ·
            refine ⟨17198665576988181118298453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45863108205301816315462541 17198665576988181118298453)
            ·
              refine ⟨50386715557582561870015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17198665576988181118298453 50386715557582561870015)
              ·
                rfl

theorem cell22_3974175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 10].length) (baseStart_3974175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974175 prefixEnd_3974175 := by exact prefixLift 3974175
  have htrace : WordTrace (prefixWord ++ tailWord_3974175) baseStart_3974175 baseEnd_3974175 := by
    simpa [prefixWord, tailWord_3974175, baseEnd_3974175] using wordTrace_append hprefix tailTrace_3974175
  have hstable : (prefixWord ++ tailWord_3974175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974175).length < 2 ^ (prefixWord ++ tailWord_3974175).sum := by decide
  have hdescent : baseEnd_3974175 < baseStart_3974175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974177 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_3974177 : Nat := 118140960795 + 3974177 * 2 ^ 59
def prefixEnd_3974177 : Nat := 4983230072969 + 3 ^ 40 * 3974177 * 2
def baseEnd_3974177 : Nat := 1360442004695601831940399

theorem tailTrace_3974177 : CollatzResearch.WordTrace tailWord_3974177 prefixEnd_3974177 1360442004695601831940399 := by
  unfold tailWord_3974177
  simp only [CollatzResearch.WordTrace]
  refine ⟨144950143323242939239824785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96633428882161959493216523 144950143323242939239824785)
  ·
    refine ⟨108712607492432204429868589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144950143323242939239824785 108712607492432204429868589)
    ·
      refine ⟨40767227809662076661200721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108712607492432204429868589 40767227809662076661200721)
      ·
        refine ⟨30575420857246557495900541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40767227809662076661200721 30575420857246557495900541)
        ·
          refine ⟨11465782821467459060962703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30575420857246557495900541 11465782821467459060962703)
          ·
            refine ⟨17198674232201188591444055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11465782821467459060962703 17198674232201188591444055)
            ·
              refine ⟨25798011348301782887166083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17198674232201188591444055 25798011348301782887166083)
              ·
                refine ⟨38697017022452674330749125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25798011348301782887166083 38697017022452674330749125)
                ·
                  refine ⟨7255690691709876437015461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38697017022452674330749125 7255690691709876437015461)
                  ·
                    refine ⟨1360442004695601831940399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255690691709876437015461 1360442004695601831940399)
                    ·
                      rfl

theorem cell22_3974177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_3974177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974177 prefixEnd_3974177 := by exact prefixLift 3974177
  have htrace : WordTrace (prefixWord ++ tailWord_3974177) baseStart_3974177 baseEnd_3974177 := by
    simpa [prefixWord, tailWord_3974177, baseEnd_3974177] using wordTrace_append hprefix tailTrace_3974177
  have hstable : (prefixWord ++ tailWord_3974177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974177).length < 2 ^ (prefixWord ++ tailWord_3974177).sum := by decide
  have hdescent : baseEnd_3974177 < baseStart_3974177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974207 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 5, 3]
def baseStart_3974207 : Nat := 118140960795 + 3974207 * 2 ^ 59
def prefixEnd_3974207 : Nat := 4983230072969 + 3 ^ 40 * 3974207 * 2
def baseEnd_3974207 : Nat := 1360452274308691753690307

theorem tailTrace_3974207 : CollatzResearch.WordTrace tailWord_3974207 prefixEnd_3974207 1360452274308691753690307 := by
  unfold tailWord_3974207
  simp only [CollatzResearch.WordTrace]
  refine ⟨144951237513134254363416875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96634158342089502908944583 144951237513134254363416875)
  ·
    refine ⟨217426856269701381545125313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144951237513134254363416875 217426856269701381545125313)
    ·
      refine ⟨163070142202276036158843985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217426856269701381545125313 163070142202276036158843985)
      ·
        refine ⟨122302606651707027119132989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163070142202276036158843985 122302606651707027119132989)
        ·
          refine ⟨45863477494390135169674871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122302606651707027119132989 45863477494390135169674871)
          ·
            refine ⟨68795216241585202754512307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45863477494390135169674871 68795216241585202754512307)
            ·
              refine ⟨103192824362377804131768461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68795216241585202754512307 103192824362377804131768461)
              ·
                refine ⟨38697309135891676549413173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103192824362377804131768461 38697309135891676549413173)
                ·
                  refine ⟨3627872731489844676507485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38697309135891676549413173 3627872731489844676507485)
                  ·
                    refine ⟨1360452274308691753690307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627872731489844676507485 1360452274308691753690307)
                    ·
                      rfl

theorem cell22_3974207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 3].length) (baseStart_3974207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974207 prefixEnd_3974207 := by exact prefixLift 3974207
  have htrace : WordTrace (prefixWord ++ tailWord_3974207) baseStart_3974207 baseEnd_3974207 := by
    simpa [prefixWord, tailWord_3974207, baseEnd_3974207] using wordTrace_append hprefix tailTrace_3974207
  have hstable : (prefixWord ++ tailWord_3974207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974207).length < 2 ^ (prefixWord ++ tailWord_3974207).sum := by decide
  have hdescent : baseEnd_3974207 < baseStart_3974207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974230 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3974230 : Nat := 118140960795 + 3974230 * 2 ^ 59
def prefixEnd_3974230 : Nat := 4983230072969 + 3 ^ 40 * 3974230 * 2
def baseEnd_3974230 : Nat := 1360460147678727360365237

theorem tailTrace_3974230 : CollatzResearch.WordTrace tailWord_3974230 prefixEnd_3974230 1360460147678727360365237 := by
  unfold tailWord_3974230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059504774503183080719009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 96634717594700619527669429 9059504774503183080719009)
  ·
    refine ⟨6794628580877387310539257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9059504774503183080719009 6794628580877387310539257)
    ·
      refine ⟨5095971435658040482904443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6794628580877387310539257 5095971435658040482904443)
      ·
        refine ⟨7643957153487060724356665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095971435658040482904443 7643957153487060724356665)
        ·
          refine ⟨5732967865115295543267499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7643957153487060724356665 5732967865115295543267499)
          ·
            refine ⟨8599451797672943314901249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732967865115295543267499 8599451797672943314901249)
            ·
              refine ⟨6449588848254707486175937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599451797672943314901249 6449588848254707486175937)
              ·
                refine ⟨4837191636191030614631953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449588848254707486175937 4837191636191030614631953)
                ·
                  refine ⟨3627893727143272960973965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4837191636191030614631953 3627893727143272960973965)
                  ·
                    refine ⟨1360460147678727360365237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3627893727143272960973965 1360460147678727360365237)
                    ·
                      rfl

theorem cell22_3974230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3974230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974230 prefixEnd_3974230 := by exact prefixLift 3974230
  have htrace : WordTrace (prefixWord ++ tailWord_3974230) baseStart_3974230 baseEnd_3974230 := by
    simpa [prefixWord, tailWord_3974230, baseEnd_3974230] using wordTrace_append hprefix tailTrace_3974230
  have hstable : (prefixWord ++ tailWord_3974230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974230).length < 2 ^ (prefixWord ++ tailWord_3974230).sum := by decide
  have hdescent : baseEnd_3974230 < baseStart_3974230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974252 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_3974252 : Nat := 118140960795 + 3974252 * 2 ^ 59
def prefixEnd_3974252 : Nat := 4983230072969 + 3 ^ 40 * 3974252 * 2
def baseEnd_3974252 : Nat := 1360467678728326636315169

theorem tailTrace_3974252 : CollatzResearch.WordTrace tailWord_3974252 prefixEnd_3974252 1360467678728326636315169 := by
  unfold tailWord_3974252
  simp only [CollatzResearch.WordTrace]
  refine ⟨72476439398985613524402505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96635252531980818032536673 72476439398985613524402505)
  ·
    refine ⟨54357329549239210143301879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72476439398985613524402505 54357329549239210143301879)
    ·
      refine ⟨81535994323858815214952819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54357329549239210143301879 81535994323858815214952819)
      ·
        refine ⟨122303991485788222822429229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81535994323858815214952819 122303991485788222822429229)
        ·
          refine ⟨45863996807170583558410961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122303991485788222822429229 45863996807170583558410961)
          ·
            refine ⟨34397997605377937668808221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45863996807170583558410961 34397997605377937668808221)
            ·
              refine ⟨12899249102016726625803083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34397997605377937668808221 12899249102016726625803083)
              ·
                refine ⟨19348873653025089938704625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12899249102016726625803083 19348873653025089938704625)
                ·
                  refine ⟨14511655239768817454028469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19348873653025089938704625 14511655239768817454028469)
                  ·
                    refine ⟨1360467678728326636315169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14511655239768817454028469 1360467678728326636315169)
                    ·
                      rfl

theorem cell22_3974252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_3974252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974252 prefixEnd_3974252 := by exact prefixLift 3974252
  have htrace : WordTrace (prefixWord ++ tailWord_3974252) baseStart_3974252 baseEnd_3974252 := by
    simpa [prefixWord, tailWord_3974252, baseEnd_3974252] using wordTrace_append hprefix tailTrace_3974252
  have hstable : (prefixWord ++ tailWord_3974252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974252).length < 2 ^ (prefixWord ++ tailWord_3974252).sum := by decide
  have hdescent : baseEnd_3974252 < baseStart_3974252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974254 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_3974254 : Nat := 118140960795 + 3974254 * 2 ^ 59
def prefixEnd_3974254 : Nat := 4983230072969 + 3 ^ 40 * 3974254 * 2
def baseEnd_3974254 : Nat := 453489454456399765921721

theorem tailTrace_3974254 : CollatzResearch.WordTrace tailWord_3974254 prefixEnd_3974254 453489454456399765921721 := by
  unfold tailWord_3974254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119118967995497673797227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96635301162642654260251877 18119118967995497673797227)
  ·
    refine ⟨27178678451993246510695841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18119118967995497673797227 27178678451993246510695841)
    ·
      refine ⟨20384008838994934883021881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27178678451993246510695841 20384008838994934883021881)
      ·
        refine ⟨15288006629246201162266411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20384008838994934883021881 15288006629246201162266411)
        ·
          refine ⟨22932009943869301743399617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288006629246201162266411 22932009943869301743399617)
          ·
            refine ⟨17199007457901976307549713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22932009943869301743399617 17199007457901976307549713)
            ·
              refine ⟨12899255593426482230662285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17199007457901976307549713 12899255593426482230662285)
              ·
                refine ⟨4837220847534930836498357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12899255593426482230662285 4837220847534930836498357)
                ·
                  refine ⟨453489454456399765921721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4837220847534930836498357 453489454456399765921721)
                  ·
                    rfl

theorem cell22_3974254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_3974254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974254 prefixEnd_3974254 := by exact prefixLift 3974254
  have htrace : WordTrace (prefixWord ++ tailWord_3974254) baseStart_3974254 baseEnd_3974254 := by
    simpa [prefixWord, tailWord_3974254, baseEnd_3974254] using wordTrace_append hprefix tailTrace_3974254
  have hstable : (prefixWord ++ tailWord_3974254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974254).length < 2 ^ (prefixWord ++ tailWord_3974254).sum := by decide
  have hdescent : baseEnd_3974254 < baseStart_3974254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974282 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_3974282 : Nat := 118140960795 + 3974282 * 2 ^ 59
def prefixEnd_3974282 : Nat := 4983230072969 + 3 ^ 40 * 3974282 * 2
def baseEnd_3974282 : Nat := 453492649447138852688359

theorem tailTrace_3974282 : CollatzResearch.WordTrace tailWord_3974282 prefixEnd_3974282 453492649447138852688359 := by
  unfold tailWord_3974282
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238493246965635543099275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96635981991908361448264733 36238493246965635543099275)
  ·
    refine ⟨54357739870448453314648913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36238493246965635543099275 54357739870448453314648913)
    ·
      refine ⟨40768304902836339985986685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54357739870448453314648913 40768304902836339985986685)
      ·
        refine ⟨15288114338563627494745007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40768304902836339985986685 15288114338563627494745007)
        ·
          refine ⟨22932171507845441242117511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288114338563627494745007 22932171507845441242117511)
          ·
            refine ⟨34398257261768161863176267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22932171507845441242117511 34398257261768161863176267)
            ·
              refine ⟨51597385892652242794764401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34398257261768161863176267 51597385892652242794764401)
              ·
                refine ⟨38698039419489182096073301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51597385892652242794764401 38698039419489182096073301)
                ·
                  refine ⟨453492649447138852688359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38698039419489182096073301 453492649447138852688359)
                  ·
                    rfl

theorem cell22_3974282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_3974282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974282 prefixEnd_3974282 := by exact prefixLift 3974282
  have htrace : WordTrace (prefixWord ++ tailWord_3974282) baseStart_3974282 baseEnd_3974282 := by
    simpa [prefixWord, tailWord_3974282, baseEnd_3974282] using wordTrace_append hprefix tailTrace_3974282
  have hstable : (prefixWord ++ tailWord_3974282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974282).length < 2 ^ (prefixWord ++ tailWord_3974282).sum := by decide
  have hdescent : baseEnd_3974282 < baseStart_3974282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974327 : List Nat := [1, 1, 3, 1, 4, 1, 3, 8]
def baseStart_3974327 : Nat := 118140960795 + 3974327 * 2 ^ 59
def prefixEnd_3974327 : Nat := 4983230072969 + 3 ^ 40 * 3974327 * 2
def baseEnd_3974327 : Nat := 151165928084561271187771

theorem tailTrace_3974327 : CollatzResearch.WordTrace tailWord_3974327 prefixEnd_3974327 151165928084561271187771 := by
  unfold tailWord_3974327
  simp only [CollatzResearch.WordTrace]
  refine ⟨144955614272699514857785235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96637076181799676571856823 144955614272699514857785235)
  ·
    refine ⟨217433421409049272286677853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144955614272699514857785235 217433421409049272286677853)
    ·
      refine ⟨81537533028393477107504195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217433421409049272286677853 81537533028393477107504195)
      ·
        refine ⟨122306299542590215661256293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81537533028393477107504195 122306299542590215661256293)
        ·
          refine ⟨22932431164235665436485555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122306299542590215661256293 22932431164235665436485555)
          ·
            refine ⟨34398646746353498154728333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22932431164235665436485555 34398646746353498154728333)
            ·
              refine ⟨12899492529882561808023125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34398646746353498154728333 12899492529882561808023125)
              ·
                refine ⟨151165928084561271187771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12899492529882561808023125 151165928084561271187771)
                ·
                  rfl

theorem cell22_3974327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 8].length) (baseStart_3974327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974327 prefixEnd_3974327 := by exact prefixLift 3974327
  have htrace : WordTrace (prefixWord ++ tailWord_3974327) baseStart_3974327 baseEnd_3974327 := by
    simpa [prefixWord, tailWord_3974327, baseEnd_3974327] using wordTrace_append hprefix tailTrace_3974327
  have hstable : (prefixWord ++ tailWord_3974327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974327).length < 2 ^ (prefixWord ++ tailWord_3974327).sum := by decide
  have hdescent : baseEnd_3974327 < baseStart_3974327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974436 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3974436 : Nat := 118140960795 + 3974436 * 2 ^ 59
def prefixEnd_3974436 : Nat := 4983230072969 + 3 ^ 40 * 3974436 * 2
def baseEnd_3974436 : Nat := 1360530665688611489714605

theorem tailTrace_3974436 : CollatzResearch.WordTrace tailWord_3974436 prefixEnd_3974436 1360530665688611489714605 := by
  unfold tailWord_3974436
  simp only [CollatzResearch.WordTrace]
  refine ⟨72479794914652313236751581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96639726552869750982335441 72479794914652313236751581)
  ·
    refine ⟨27179923092994617463781843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72479794914652313236751581 27179923092994617463781843)
    ·
      refine ⟨40769884639491926195672765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27179923092994617463781843 40769884639491926195672765)
      ·
        refine ⟨15288706739809472323377287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40769884639491926195672765 15288706739809472323377287)
        ·
          refine ⟨22933060109714208485065931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288706739809472323377287 22933060109714208485065931)
          ·
            refine ⟨34399590164571312727598897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22933060109714208485065931 34399590164571312727598897)
            ·
              refine ⟨25799692623428484545699173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34399590164571312727598897 25799692623428484545699173)
              ·
                refine ⟨4837442366892840852318595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25799692623428484545699173 4837442366892840852318595)
                ·
                  refine ⟨7256163550339261278477893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837442366892840852318595 7256163550339261278477893)
                  ·
                    refine ⟨1360530665688611489714605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256163550339261278477893 1360530665688611489714605)
                    ·
                      rfl

theorem cell22_3974436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3974436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974436 prefixEnd_3974436 := by exact prefixLift 3974436
  have htrace : WordTrace (prefixWord ++ tailWord_3974436) baseStart_3974436 baseEnd_3974436 := by
    simpa [prefixWord, tailWord_3974436, baseEnd_3974436] using wordTrace_append hprefix tailTrace_3974436
  have hstable : (prefixWord ++ tailWord_3974436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974436).length < 2 ^ (prefixWord ++ tailWord_3974436).sum := by decide
  have hdescent : baseEnd_3974436 < baseStart_3974436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974451 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 4]
def baseStart_3974451 : Nat := 118140960795 + 3974451 * 2 ^ 59
def prefixEnd_3974451 : Nat := 4983230072969 + 3 ^ 40 * 3974451 * 2
def baseEnd_3974451 : Nat := 453511933498385483529853

theorem tailTrace_3974451 : CollatzResearch.WordTrace tailWord_3974451 prefixEnd_3974451 453511933498385483529853 := by
  unfold tailWord_3974451
  simp only [CollatzResearch.WordTrace]
  refine ⟨144960136924250284035299207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96640091282833522690199471 144960136924250284035299207)
  ·
    refine ⟨217440205386375426052948811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144960136924250284035299207 217440205386375426052948811)
    ·
      refine ⟨326160308079563139079423217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217440205386375426052948811 326160308079563139079423217)
      ·
        refine ⟨244620231059672354309567413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326160308079563139079423217 244620231059672354309567413)
        ·
          refine ⟨22933146661844283216521945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244620231059672354309567413 22933146661844283216521945)
          ·
            refine ⟨17199859996383212412391459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22933146661844283216521945 17199859996383212412391459)
            ·
              refine ⟨25799789994574818618587189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17199859996383212412391459 25799789994574818618587189)
              ·
                refine ⟨2418730311991389245492549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25799789994574818618587189 2418730311991389245492549)
                ·
                  refine ⟨453511933498385483529853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418730311991389245492549 453511933498385483529853)
                  ·
                    rfl

theorem cell22_3974451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 4].length) (baseStart_3974451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974451 prefixEnd_3974451 := by exact prefixLift 3974451
  have htrace : WordTrace (prefixWord ++ tailWord_3974451) baseStart_3974451 baseEnd_3974451 := by
    simpa [prefixWord, tailWord_3974451, baseEnd_3974451] using wordTrace_append hprefix tailTrace_3974451
  have hstable : (prefixWord ++ tailWord_3974451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974451).length < 2 ^ (prefixWord ++ tailWord_3974451).sum := by decide
  have hdescent : baseEnd_3974451 < baseStart_3974451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974453 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3974453 : Nat := 118140960795 + 3974453 * 2 ^ 59
def prefixEnd_3974453 : Nat := 4983230072969 + 3 ^ 40 * 3974453 * 2
def baseEnd_3974453 : Nat := 1360536485136029112039553

theorem tailTrace_3974453 : CollatzResearch.WordTrace tailWord_3974453 prefixEnd_3974453 1360536485136029112039553 := by
  unfold tailWord_3974453
  simp only [CollatzResearch.WordTrace]
  refine ⟨144960209870243038376872013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96640139913495358917914675 144960209870243038376872013)
  ·
    refine ⟨54360078701341139391327005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144960209870243038376872013 54360078701341139391327005)
    ·
      refine ⟨20385029513002927271747627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54360078701341139391327005 20385029513002927271747627)
      ·
        refine ⟨30577544269504390907621441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20385029513002927271747627 30577544269504390907621441)
        ·
          refine ⟨22933158202128293180716081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30577544269504390907621441 22933158202128293180716081)
          ·
            refine ⟨17199868651596219885537061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22933158202128293180716081 17199868651596219885537061)
            ·
              refine ⟨3224975372174291228538199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17199868651596219885537061 3224975372174291228538199)
              ·
                refine ⟨4837463058261436842807299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224975372174291228538199 4837463058261436842807299)
                ·
                  refine ⟨7256194587392155264210949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837463058261436842807299 7256194587392155264210949)
                  ·
                    refine ⟨1360536485136029112039553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256194587392155264210949 1360536485136029112039553)
                    ·
                      rfl

theorem cell22_3974453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3974453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974453 prefixEnd_3974453 := by exact prefixLift 3974453
  have htrace : WordTrace (prefixWord ++ tailWord_3974453) baseStart_3974453 baseEnd_3974453 := by
    simpa [prefixWord, tailWord_3974453, baseEnd_3974453] using wordTrace_append hprefix tailTrace_3974453
  have hstable : (prefixWord ++ tailWord_3974453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974453).length < 2 ^ (prefixWord ++ tailWord_3974453).sum := by decide
  have hdescent : baseEnd_3974453 < baseStart_3974453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974464 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_3974464 : Nat := 118140960795 + 3974464 * 2 ^ 59
def prefixEnd_3974464 : Nat := 4983230072969 + 3 ^ 40 * 3974464 * 2
def baseEnd_3974464 : Nat := 1360540250660828750014519

theorem tailTrace_3974464 : CollatzResearch.WordTrace tailWord_3974464 prefixEnd_3974464 1360540250660828750014519 := by
  unfold tailWord_3974464
  simp only [CollatzResearch.WordTrace]
  refine ⟨72480305536601593627761223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96640407382135458170348297 72480305536601593627761223)
  ·
    refine ⟨108720458304902390441641835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72480305536601593627761223 108720458304902390441641835)
    ·
      refine ⟨163080687457353585662462753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108720458304902390441641835 163080687457353585662462753)
      ·
        refine ⟨122310515593015189246847065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163080687457353585662462753 122310515593015189246847065)
        ·
          refine ⟨91732886694761391935135299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122310515593015189246847065 91732886694761391935135299)
          ·
            refine ⟨137599330042142087902702949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91732886694761391935135299 137599330042142087902702949)
            ·
              refine ⟨25799874382901641481756803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137599330042142087902702949 25799874382901641481756803)
              ·
                refine ⟨38699811574352462222635205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25799874382901641481756803 38699811574352462222635205)
                ·
                  refine ⟨7256214670191086666744101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38699811574352462222635205 7256214670191086666744101)
                  ·
                    refine ⟨1360540250660828750014519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256214670191086666744101 1360540250660828750014519)
                    ·
                      rfl

theorem cell22_3974464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_3974464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974464 prefixEnd_3974464 := by exact prefixLift 3974464
  have htrace : WordTrace (prefixWord ++ tailWord_3974464) baseStart_3974464 baseEnd_3974464 := by
    simpa [prefixWord, tailWord_3974464, baseEnd_3974464] using wordTrace_append hprefix tailTrace_3974464
  have hstable : (prefixWord ++ tailWord_3974464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974464).length < 2 ^ (prefixWord ++ tailWord_3974464).sum := by decide
  have hdescent : baseEnd_3974464 < baseStart_3974464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974468 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_3974468 : Nat := 118140960795 + 3974468 * 2 ^ 59
def prefixEnd_3974468 : Nat := 4983230072969 + 3 ^ 40 * 3974468 * 2
def baseEnd_3974468 : Nat := 453513873314191357638169

theorem tailTrace_3974468 : CollatzResearch.WordTrace tailWord_3974468 prefixEnd_3974468 453513873314191357638169 := by
  unfold tailWord_3974468
  simp only [CollatzResearch.WordTrace]
  refine ⟨72480378482594347969334029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96640504643459130625778705 72480378482594347969334029)
  ·
    refine ⟨27180141930972880488500261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72480378482594347969334029 27180141930972880488500261)
    ·
      refine ⟨5096276612057415091593799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27180141930972880488500261 5096276612057415091593799)
      ·
        refine ⟨7644414918086122637390699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096276612057415091593799 7644414918086122637390699)
        ·
          refine ⟨11466622377129183956086049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644414918086122637390699 11466622377129183956086049)
          ·
            refine ⟨8599966782846887967064537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11466622377129183956086049 8599966782846887967064537)
            ·
              refine ⟨6449975087135165975298403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599966782846887967064537 6449975087135165975298403)
              ·
                refine ⟨9674962630702748962947605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449975087135165975298403 9674962630702748962947605)
                ·
                  refine ⟨453513873314191357638169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9674962630702748962947605 453513873314191357638169)
                  ·
                    rfl

theorem cell22_3974468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_3974468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974468 prefixEnd_3974468 := by exact prefixLift 3974468
  have htrace : WordTrace (prefixWord ++ tailWord_3974468) baseStart_3974468 baseEnd_3974468 := by
    simpa [prefixWord, tailWord_3974468, baseEnd_3974468] using wordTrace_append hprefix tailTrace_3974468
  have hstable : (prefixWord ++ tailWord_3974468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974468).length < 2 ^ (prefixWord ++ tailWord_3974468).sum := by decide
  have hdescent : baseEnd_3974468 < baseStart_3974468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974483 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 2, 3]
def baseStart_3974483 : Nat := 118140960795 + 3974483 * 2 ^ 59
def prefixEnd_3974483 : Nat := 4983230072969 + 3 ^ 40 * 3974483 * 2
def baseEnd_3974483 : Nat := 1360546754749119033789461

theorem tailTrace_3974483 : CollatzResearch.WordTrace tailWord_3974483 prefixEnd_3974483 1360546754749119033789461 := by
  unfold tailWord_3974483
  simp only [CollatzResearch.WordTrace]
  refine ⟨144961304060134353500464103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96640869373422902333642735 144961304060134353500464103)
  ·
    refine ⟨217441956090201530250696155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144961304060134353500464103 217441956090201530250696155)
    ·
      refine ⟨326162934135302295376044233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217441956090201530250696155 326162934135302295376044233)
      ·
        refine ⟨244622200601476721532033175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326162934135302295376044233 244622200601476721532033175)
        ·
          refine ⟨366933300902215082298049763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244622200601476721532033175 366933300902215082298049763)
          ·
            refine ⟨550399951353322623447074645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366933300902215082298049763 550399951353322623447074645)
            ·
              refine ⟨3224999714960874746760203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 550399951353322623447074645 3224999714960874746760203)
              ·
                refine ⟨4837499572441312120140305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224999714960874746760203 4837499572441312120140305)
                ·
                  refine ⟨3628124679330984090105229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4837499572441312120140305 3628124679330984090105229)
                  ·
                    refine ⟨1360546754749119033789461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628124679330984090105229 1360546754749119033789461)
                    ·
                      rfl

theorem cell22_3974483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 2, 3].length) (baseStart_3974483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974483 prefixEnd_3974483 := by exact prefixLift 3974483
  have htrace : WordTrace (prefixWord ++ tailWord_3974483) baseStart_3974483 baseEnd_3974483 := by
    simpa [prefixWord, tailWord_3974483, baseEnd_3974483] using wordTrace_append hprefix tailTrace_3974483
  have hstable : (prefixWord ++ tailWord_3974483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974483).length < 2 ^ (prefixWord ++ tailWord_3974483).sum := by decide
  have hdescent : baseEnd_3974483 < baseStart_3974483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974496 : List Nat := [2, 1, 1, 3, 4, 1, 4, 6]
def baseStart_3974496 : Nat := 118140960795 + 3974496 * 2 ^ 59
def prefixEnd_3974496 : Nat := 4983230072969 + 3 ^ 40 * 3974496 * 2
def baseEnd_3974496 : Nat := 151172356101643481468269

theorem tailTrace_3974496 : CollatzResearch.WordTrace tailWord_3974496 prefixEnd_3974496 151172356101643481468269 := by
  unfold tailWord_3974496
  simp only [CollatzResearch.WordTrace]
  refine ⟨72480889104543628360343671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96641185472724837813791561 72480889104543628360343671)
  ·
    refine ⟨108721333656815442540515507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72480889104543628360343671 108721333656815442540515507)
    ·
      refine ⟨163082000485223163810773261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108721333656815442540515507 163082000485223163810773261)
      ·
        refine ⟨61155750181958686429039973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163082000485223163810773261 61155750181958686429039973)
        ·
          refine ⟨11466703159117253705444995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61155750181958686429039973 11466703159117253705444995)
          ·
            refine ⟨17200054738675880558167493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466703159117253705444995 17200054738675880558167493)
            ·
              refine ⟨3225010263501727604656405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17200054738675880558167493 3225010263501727604656405)
              ·
                refine ⟨151172356101643481468269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3225010263501727604656405 151172356101643481468269)
                ·
                  rfl

theorem cell22_3974496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_3974496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974496 prefixEnd_3974496 := by exact prefixLift 3974496
  have htrace : WordTrace (prefixWord ++ tailWord_3974496) baseStart_3974496 baseEnd_3974496 := by
    simpa [prefixWord, tailWord_3974496, baseEnd_3974496] using wordTrace_append hprefix tailTrace_3974496
  have hstable : (prefixWord ++ tailWord_3974496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974496).length < 2 ^ (prefixWord ++ tailWord_3974496).sum := by decide
  have hdescent : baseEnd_3974496 < baseStart_3974496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974524 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3974524 : Nat := 118140960795 + 3974524 * 2 ^ 59
def prefixEnd_3974524 : Nat := 4983230072969 + 3 ^ 40 * 3974524 * 2
def baseEnd_3974524 : Nat := 453520263295669531171445

theorem tailTrace_3974524 : CollatzResearch.WordTrace tailWord_3974524 prefixEnd_3974524 453520263295669531171445 := by
  unfold tailWord_3974524
  simp only [CollatzResearch.WordTrace]
  refine ⟨72481399726492908751353313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96641866301990545001804417 72481399726492908751353313)
  ·
    refine ⟨54361049794869681563514985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72481399726492908751353313 54361049794869681563514985)
    ·
      refine ⟨40770787346152261172636239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54361049794869681563514985 40770787346152261172636239)
      ·
        refine ⟨61156181019228391758954359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40770787346152261172636239 61156181019228391758954359)
        ·
          refine ⟨91734271528842587638431539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61156181019228391758954359 91734271528842587638431539)
          ·
            refine ⟨137601407293263881457647309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91734271528842587638431539 137601407293263881457647309)
            ·
              refine ⟨51600527734973955546617741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137601407293263881457647309 51600527734973955546617741)
              ·
                refine ⟨19350197900615233329981653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51600527734973955546617741 19350197900615233329981653)
                ·
                  refine ⟨453520263295669531171445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19350197900615233329981653 453520263295669531171445)
                  ·
                    rfl

theorem cell22_3974524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3974524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974524 prefixEnd_3974524 := by exact prefixLift 3974524
  have htrace : WordTrace (prefixWord ++ tailWord_3974524) baseStart_3974524 baseEnd_3974524 := by
    simpa [prefixWord, tailWord_3974524, baseEnd_3974524] using wordTrace_append hprefix tailTrace_3974524
  have hstable : (prefixWord ++ tailWord_3974524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974524).length < 2 ^ (prefixWord ++ tailWord_3974524).sum := by decide
  have hdescent : baseEnd_3974524 < baseStart_3974524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974528 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 1, 3]
def baseStart_3974528 : Nat := 118140960795 + 3974528 * 2 ^ 59
def prefixEnd_3974528 : Nat := 4983230072969 + 3 ^ 40 * 3974528 * 2
def baseEnd_3974528 : Nat := 1360562159168753916414323

theorem tailTrace_3974528 : CollatzResearch.WordTrace tailWord_3974528 prefixEnd_3974528 1360562159168753916414323 := by
  unfold tailWord_3974528
  simp only [CollatzResearch.WordTrace]
  refine ⟨72481472672485663092926119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96641963563314217457234825 72481472672485663092926119)
  ·
    refine ⟨108722209008728494639389179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72481472672485663092926119 108722209008728494639389179)
    ·
      refine ⟨163083313513092741959083769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108722209008728494639389179 163083313513092741959083769)
      ·
        refine ⟨122312485134819556469312827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163083313513092741959083769 122312485134819556469312827)
        ·
          refine ⟨183468727702229334703969241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122312485134819556469312827 183468727702229334703969241)
          ·
            refine ⟨137601545776672001027976931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183468727702229334703969241 137601545776672001027976931)
            ·
              refine ⟨206402318665008001541965397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137601545776672001027976931 206402318665008001541965397)
              ·
                refine ⟨2418777171855562518069907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 206402318665008001541965397 2418777171855562518069907)
                ·
                  refine ⟨3628165757783343777104861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418777171855562518069907 3628165757783343777104861)
                  ·
                    refine ⟨1360562159168753916414323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628165757783343777104861 1360562159168753916414323)
                    ·
                      rfl

theorem cell22_3974528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_3974528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974528 prefixEnd_3974528 := by exact prefixLift 3974528
  have htrace : WordTrace (prefixWord ++ tailWord_3974528) baseStart_3974528 baseEnd_3974528 := by
    simpa [prefixWord, tailWord_3974528, baseEnd_3974528] using wordTrace_append hprefix tailTrace_3974528
  have hstable : (prefixWord ++ tailWord_3974528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974528).length < 2 ^ (prefixWord ++ tailWord_3974528).sum := by decide
  have hdescent : baseEnd_3974528 < baseStart_3974528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974539 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_3974539 : Nat := 118140960795 + 3974539 * 2 ^ 59
def prefixEnd_3974539 : Nat := 4983230072969 + 3 ^ 40 * 3974539 * 2
def baseEnd_3974539 : Nat := 1360565924693553554389289

theorem tailTrace_3974539 : CollatzResearch.WordTrace tailWord_3974539 prefixEnd_3974539 1360565924693553554389289 := by
  unfold tailWord_3974539
  simp only [CollatzResearch.WordTrace]
  refine ⟨144963346547931475064502671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96642231031954316709668447 144963346547931475064502671)
  ·
    refine ⟨217445019821897212596754007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144963346547931475064502671 217445019821897212596754007)
    ·
      refine ⟨326167529732845818895131011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217445019821897212596754007 326167529732845818895131011)
      ·
        refine ⟨489251294599268728342696517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326167529732845818895131011 489251294599268728342696517)
        ·
          refine ⟨91734617737362886564255597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489251294599268728342696517 91734617737362886564255597)
          ·
            refine ⟨34400481651511082461595849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91734617737362886564255597 34400481651511082461595849)
            ·
              refine ⟨25800361238633311846196887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34400481651511082461595849 25800361238633311846196887)
              ·
                refine ⟨38700541857949967769295331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25800361238633311846196887 38700541857949967769295331)
                ·
                  refine ⟨58050812786924951653942997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38700541857949967769295331 58050812786924951653942997)
                  ·
                    refine ⟨1360565924693553554389289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58050812786924951653942997 1360565924693553554389289)
                    ·
                      rfl

theorem cell22_3974539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_3974539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974539 prefixEnd_3974539 := by exact prefixLift 3974539
  have htrace : WordTrace (prefixWord ++ tailWord_3974539) baseStart_3974539 baseEnd_3974539 := by
    simpa [prefixWord, tailWord_3974539, baseEnd_3974539] using wordTrace_append hprefix tailTrace_3974539
  have hstable : (prefixWord ++ tailWord_3974539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974539).length < 2 ^ (prefixWord ++ tailWord_3974539).sum := by decide
  have hdescent : baseEnd_3974539 < baseStart_3974539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974601 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_3974601 : Nat := 118140960795 + 3974601 * 2 ^ 59
def prefixEnd_3974601 : Nat := 4983230072969 + 3 ^ 40 * 3974601 * 2
def baseEnd_3974601 : Nat := 1360587148560606059339099

theorem tailTrace_3974601 : CollatzResearch.WordTrace tailWord_3974601 prefixEnd_3974601 1360587148560606059339099 := by
  unfold tailWord_3974601
  simp only [CollatzResearch.WordTrace]
  refine ⟨144965607873706859653259657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96643738582471239768839771 144965607873706859653259657)
  ·
    refine ⟨108724205905280144739944743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144965607873706859653259657 108724205905280144739944743)
    ·
      refine ⟨163086308857920217109917115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108724205905280144739944743 163086308857920217109917115)
      ·
        refine ⟨244629463286880325664875673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163086308857920217109917115 244629463286880325664875673)
        ·
          refine ⟨183472097465160244248656755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244629463286880325664875673 183472097465160244248656755)
          ·
            refine ⟨275208146197740366372985133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183472097465160244248656755 275208146197740366372985133)
            ·
              refine ⟨103203054824152637389869425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275208146197740366372985133 103203054824152637389869425)
              ·
                refine ⟨77402291118114478042402069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103203054824152637389869425 77402291118114478042402069)
                ·
                  refine ⟨3628232396161616158237597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77402291118114478042402069 3628232396161616158237597)
                  ·
                    refine ⟨1360587148560606059339099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628232396161616158237597 1360587148560606059339099)
                    ·
                      rfl

theorem cell22_3974601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_3974601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974601 prefixEnd_3974601 := by exact prefixLift 3974601
  have htrace : WordTrace (prefixWord ++ tailWord_3974601) baseStart_3974601 baseEnd_3974601 := by
    simpa [prefixWord, tailWord_3974601, baseEnd_3974601] using wordTrace_append hprefix tailTrace_3974601
  have hstable : (prefixWord ++ tailWord_3974601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974601).length < 2 ^ (prefixWord ++ tailWord_3974601).sum := by decide
  have hdescent : baseEnd_3974601 < baseStart_3974601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974631 : List Nat := [1, 1, 5, 2, 1, 3, 9]
def baseStart_3974631 : Nat := 118140960795 + 3974631 * 2 ^ 59
def prefixEnd_3974631 : Nat := 4983230072969 + 3 ^ 40 * 3974631 * 2
def baseEnd_3974631 : Nat := 50392496969396147447741

theorem tailTrace_3974631 : CollatzResearch.WordTrace tailWord_3974631 prefixEnd_3974631 50392496969396147447741 := by
  unfold tailWord_3974631
  simp only [CollatzResearch.WordTrace]
  refine ⟨144966702063598174776851747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96644468042398783184567831 144966702063598174776851747)
  ·
    refine ⟨217450053095397262165277621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144966702063598174776851747 217450053095397262165277621)
    ·
      refine ⟨20385942477693493327994777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217450053095397262165277621 20385942477693493327994777)
      ·
        refine ⟨15289456858270119995996083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20385942477693493327994777 15289456858270119995996083)
        ·
          refine ⟨22934185287405179993994125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289456858270119995996083 22934185287405179993994125)
          ·
            refine ⟨8600319482776942497747797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22934185287405179993994125 8600319482776942497747797)
            ·
              refine ⟨50392496969396147447741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8600319482776942497747797 50392496969396147447741)
              ·
                rfl

theorem cell22_3974631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 9].length) (baseStart_3974631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974631 prefixEnd_3974631 := by exact prefixLift 3974631
  have htrace : WordTrace (prefixWord ++ tailWord_3974631) baseStart_3974631 baseEnd_3974631 := by
    simpa [prefixWord, tailWord_3974631, baseEnd_3974631] using wordTrace_append hprefix tailTrace_3974631
  have hstable : (prefixWord ++ tailWord_3974631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974631).length < 2 ^ (prefixWord ++ tailWord_3974631).sum := by decide
  have hdescent : baseEnd_3974631 < baseStart_3974631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974706 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_3974706 : Nat := 118140960795 + 3974706 * 2 ^ 59
def prefixEnd_3974706 : Nat := 4983230072969 + 3 ^ 40 * 3974706 * 2
def baseEnd_3974706 : Nat := 1360623092206420785463777

theorem tailTrace_3974706 : CollatzResearch.WordTrace tailWord_3974706 prefixEnd_3974706 1360623092206420785463777 := by
  unfold tailWord_3974706
  simp only [CollatzResearch.WordTrace]
  refine ⟨36242359384581615646457993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96646291692217641723887981 36242359384581615646457993)
  ·
    refine ⟨27181769538436211734843495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36242359384581615646457993 27181769538436211734843495)
    ·
      refine ⟨40772654307654317602265243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27181769538436211734843495 40772654307654317602265243)
      ·
        refine ⟨61158981461481476403397865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40772654307654317602265243 61158981461481476403397865)
        ·
          refine ⟨45869236096111107302548399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61158981461481476403397865 45869236096111107302548399)
          ·
            refine ⟨68803854144166660953822599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45869236096111107302548399 68803854144166660953822599)
            ·
              refine ⟨103205781216249991430733899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68803854144166660953822599 103205781216249991430733899)
              ·
                refine ⟨154808671824374987146100849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103205781216249991430733899 154808671824374987146100849)
                ·
                  refine ⟨116106503868281240359575637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154808671824374987146100849 116106503868281240359575637)
                  ·
                    refine ⟨1360623092206420785463777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 116106503868281240359575637 1360623092206420785463777)
                    ·
                      rfl

theorem cell22_3974706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_3974706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974706 prefixEnd_3974706 := by exact prefixLift 3974706
  have htrace : WordTrace (prefixWord ++ tailWord_3974706) baseStart_3974706 baseEnd_3974706 := by
    simpa [prefixWord, tailWord_3974706, baseEnd_3974706] using wordTrace_append hprefix tailTrace_3974706
  have hstable : (prefixWord ++ tailWord_3974706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974706).length < 2 ^ (prefixWord ++ tailWord_3974706).sum := by decide
  have hdescent : baseEnd_3974706 < baseStart_3974706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974751 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_3974751 : Nat := 118140960795 + 3974751 * 2 ^ 59
def prefixEnd_3974751 : Nat := 4983230072969 + 3 ^ 40 * 3974751 * 2
def baseEnd_3974751 : Nat := 1360638496626055668088639

theorem tailTrace_3974751 : CollatzResearch.WordTrace tailWord_3974751 prefixEnd_3974751 1360638496626055668088639 := by
  unfold tailWord_3974751
  simp only [CollatzResearch.WordTrace]
  refine ⟨144971078823163435271220107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96647385882108956847480071 144971078823163435271220107)
  ·
    refine ⟨217456618234745152906830161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144971078823163435271220107 217456618234745152906830161)
    ·
      refine ⟨163092463676058864680122621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217456618234745152906830161 163092463676058864680122621)
      ·
        refine ⟨61159673878522074255045983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163092463676058864680122621 61159673878522074255045983)
        ·
          refine ⟨91739510817783111382568975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61159673878522074255045983 91739510817783111382568975)
          ·
            refine ⟨137609266226674667073853463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91739510817783111382568975 137609266226674667073853463)
            ·
              refine ⟨206413899340012000610780195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137609266226674667073853463 206413899340012000610780195)
              ·
                refine ⟨309620849010018000916170293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206413899340012000610780195 309620849010018000916170293)
                ·
                  refine ⟨29026954594689187585890965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 309620849010018000916170293 29026954594689187585890965)
                  ·
                    refine ⟨1360638496626055668088639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29026954594689187585890965 1360638496626055668088639)
                    ·
                      rfl

theorem cell22_3974751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_3974751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974751 prefixEnd_3974751 := by exact prefixLift 3974751
  have htrace : WordTrace (prefixWord ++ tailWord_3974751) baseStart_3974751 baseEnd_3974751 := by
    simpa [prefixWord, tailWord_3974751, baseEnd_3974751] using wordTrace_append hprefix tailTrace_3974751
  have hstable : (prefixWord ++ tailWord_3974751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974751).length < 2 ^ (prefixWord ++ tailWord_3974751).sum := by decide
  have hdescent : baseEnd_3974751 < baseStart_3974751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974755 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 4]
def baseStart_3974755 : Nat := 118140960795 + 3974755 * 2 ^ 59
def prefixEnd_3974755 : Nat := 4983230072969 + 3 ^ 40 * 3974755 * 2
def baseEnd_3974755 : Nat := 453546621969266996996209

theorem tailTrace_3974755 : CollatzResearch.WordTrace tailWord_3974755 prefixEnd_3974755 453546621969266996996209 := by
  unfold tailWord_3974755
  simp only [CollatzResearch.WordTrace]
  refine ⟨144971224715148943954365719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96647483143432629302910479 144971224715148943954365719)
  ·
    refine ⟨217456837072723415931548579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144971224715148943954365719 217456837072723415931548579)
    ·
      refine ⟨326185255609085123897322869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217456837072723415931548579 326185255609085123897322869)
      ·
        refine ⟨30579867713351730365374019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326185255609085123897322869 30579867713351730365374019)
        ·
          refine ⟨45869801570027595548061029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30579867713351730365374019 45869801570027595548061029)
          ·
            refine ⟨8600587794380174165261443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45869801570027595548061029 8600587794380174165261443)
            ·
              refine ⟨12900881691570261247892165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600587794380174165261443 12900881691570261247892165)
              ·
                refine ⟨2418915317169423983979781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12900881691570261247892165 2418915317169423983979781)
                ·
                  refine ⟨453546621969266996996209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418915317169423983979781 453546621969266996996209)
                  ·
                    rfl

theorem cell22_3974755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 4].length) (baseStart_3974755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974755 prefixEnd_3974755 := by exact prefixLift 3974755
  have htrace : WordTrace (prefixWord ++ tailWord_3974755) baseStart_3974755 baseEnd_3974755 := by
    simpa [prefixWord, tailWord_3974755, baseEnd_3974755] using wordTrace_append hprefix tailTrace_3974755
  have hstable : (prefixWord ++ tailWord_3974755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974755).length < 2 ^ (prefixWord ++ tailWord_3974755).sum := by decide
  have hdescent : baseEnd_3974755 < baseStart_3974755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974770 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_3974770 : Nat := 118140960795 + 3974770 * 2 ^ 59
def prefixEnd_3974770 : Nat := 4983230072969 + 3 ^ 40 * 3974770 * 2
def baseEnd_3974770 : Nat := 1360645000714345951863581

theorem tailTrace_3974770 : CollatzResearch.WordTrace tailWord_3974770 prefixEnd_3974770 1360645000714345951863581 := by
  unfold tailWord_3974770
  simp only [CollatzResearch.WordTrace]
  refine ⟨36242942952523650379040441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96647847873396401010774509 36242942952523650379040441)
  ·
    refine ⟨27182207214392737784280331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36242942952523650379040441 27182207214392737784280331)
    ·
      refine ⟨40773310821589106676420497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27182207214392737784280331 40773310821589106676420497)
      ·
        refine ⟨30579983116191830007315373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40773310821589106676420497 30579983116191830007315373)
        ·
          refine ⟨11467493668571936252743265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30579983116191830007315373 11467493668571936252743265)
          ·
            refine ⟨8600620251428952189557449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11467493668571936252743265 8600620251428952189557449)
            ·
              refine ⟨6450465188571714142168087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8600620251428952189557449 6450465188571714142168087)
              ·
                refine ⟨9675697782857571213252131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450465188571714142168087 9675697782857571213252131)
                ·
                  refine ⟨14513546674286356819878197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675697782857571213252131 14513546674286356819878197)
                  ·
                    refine ⟨1360645000714345951863581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14513546674286356819878197 1360645000714345951863581)
                    ·
                      rfl

theorem cell22_3974770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_3974770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974770 prefixEnd_3974770 := by exact prefixLift 3974770
  have htrace : WordTrace (prefixWord ++ tailWord_3974770) baseStart_3974770 baseEnd_3974770 := by
    simpa [prefixWord, tailWord_3974770, baseEnd_3974770] using wordTrace_append hprefix tailTrace_3974770
  have hstable : (prefixWord ++ tailWord_3974770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974770).length < 2 ^ (prefixWord ++ tailWord_3974770).sum := by decide
  have hdescent : baseEnd_3974770 < baseStart_3974770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974785 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3974785 : Nat := 118140960795 + 3974785 * 2 ^ 59
def prefixEnd_3974785 : Nat := 4983230072969 + 3 ^ 40 * 3974785 * 2
def baseEnd_3974785 : Nat := 1360650135520890912738535

theorem tailTrace_3974785 : CollatzResearch.WordTrace tailWord_3974785 prefixEnd_3974785 1360650135520890912738535 := by
  unfold tailWord_3974785
  simp only [CollatzResearch.WordTrace]
  refine ⟨144972318905040259077957809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96648212603360172718638539 144972318905040259077957809)
  ·
    refine ⟨108729239178780194308468357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144972318905040259077957809 108729239178780194308468357)
    ·
      refine ⟨20386732346021286432837817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108729239178780194308468357 20386732346021286432837817)
      ·
        refine ⟨15290049259515964824628363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20386732346021286432837817 15290049259515964824628363)
        ·
          refine ⟨22935073889273947236942545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290049259515964824628363 22935073889273947236942545)
          ·
            refine ⟨17201305416955460427706909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22935073889273947236942545 17201305416955460427706909)
            ·
              refine ⟨6450489531358297660390091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17201305416955460427706909 6450489531358297660390091)
              ·
                refine ⟨9675734297037446490585137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450489531358297660390091 9675734297037446490585137)
                ·
                  refine ⟨7256800722778084867938853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675734297037446490585137 7256800722778084867938853)
                  ·
                    refine ⟨1360650135520890912738535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256800722778084867938853 1360650135520890912738535)
                    ·
                      rfl

theorem cell22_3974785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3974785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974785 prefixEnd_3974785 := by exact prefixLift 3974785
  have htrace : WordTrace (prefixWord ++ tailWord_3974785) baseStart_3974785 baseEnd_3974785 := by
    simpa [prefixWord, tailWord_3974785, baseEnd_3974785] using wordTrace_append hprefix tailTrace_3974785
  have hstable : (prefixWord ++ tailWord_3974785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974785).length < 2 ^ (prefixWord ++ tailWord_3974785).sum := by decide
  have hdescent : baseEnd_3974785 < baseStart_3974785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974866 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 1, 3]
def baseStart_3974866 : Nat := 118140960795 + 3974866 * 2 ^ 59
def prefixEnd_3974866 : Nat := 4983230072969 + 3 ^ 40 * 3974866 * 2
def baseEnd_3974866 : Nat := 1360677863476233701463287

theorem tailTrace_3974866 : CollatzResearch.WordTrace tailWord_3974866 prefixEnd_3974866 1360677863476233701463287 := by
  unfold tailWord_3974866
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243818304436702477914113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96650182145164539941104301 36243818304436702477914113)
  ·
    refine ⟨27182863728327526858435585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36243818304436702477914113 27182863728327526858435585)
    ·
      refine ⟨20387147796245645143826689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27182863728327526858435585 20387147796245645143826689)
      ·
        refine ⟨15290360847184233857870017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20387147796245645143826689 15290360847184233857870017)
        ·
          refine ⟨11467770635388175393402513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290360847184233857870017 11467770635388175393402513)
          ·
            refine ⟨8600827976541131545051885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11467770635388175393402513 8600827976541131545051885)
            ·
              refine ⟨3225310491202924329394457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8600827976541131545051885 3225310491202924329394457)
              ·
                refine ⟨2418982868402193247045843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225310491202924329394457 2418982868402193247045843)
                ·
                  refine ⟨3628474302603289870568765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418982868402193247045843 3628474302603289870568765)
                  ·
                    refine ⟨1360677863476233701463287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628474302603289870568765 1360677863476233701463287)
                    ·
                      rfl

theorem cell22_3974866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_3974866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974866 prefixEnd_3974866 := by exact prefixLift 3974866
  have htrace : WordTrace (prefixWord ++ tailWord_3974866) baseStart_3974866 baseEnd_3974866 := by
    simpa [prefixWord, tailWord_3974866, baseEnd_3974866] using wordTrace_append hprefix tailTrace_3974866
  have hstable : (prefixWord ++ tailWord_3974866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974866).length < 2 ^ (prefixWord ++ tailWord_3974866).sum := by decide
  have hdescent : baseEnd_3974866 < baseStart_3974866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974903 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_3974903 : Nat := 118140960795 + 3974903 * 2 ^ 59
def prefixEnd_3974903 : Nat := 4983230072969 + 3 ^ 40 * 3974903 * 2
def baseEnd_3974903 : Nat := 1360690529332377938288173

theorem tailTrace_3974903 : CollatzResearch.WordTrace tailWord_3974903 prefixEnd_3974903 1360690529332377938288173 := by
  unfold tailWord_3974903
  simp only [CollatzResearch.WordTrace]
  refine ⟨144976622718612765230753363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96651081812408510153835575 144976622718612765230753363)
  ·
    refine ⟨217464934077919147846130045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144976622718612765230753363 217464934077919147846130045)
    ·
      refine ⟨81549350279219680442298767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217464934077919147846130045 81549350279219680442298767)
      ·
        refine ⟨122324025418829520663448151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81549350279219680442298767 122324025418829520663448151)
        ·
          refine ⟨183486038128244280995172227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122324025418829520663448151 183486038128244280995172227)
          ·
            refine ⟨275229057192366421492758341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183486038128244280995172227 275229057192366421492758341)
            ·
              refine ⟨51605448223568704029892189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275229057192366421492758341 51605448223568704029892189)
              ·
                refine ⟨19352043083838264011209571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51605448223568704029892189 19352043083838264011209571)
                ·
                  refine ⟨29028064625757396016814357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19352043083838264011209571 29028064625757396016814357)
                  ·
                    refine ⟨1360690529332377938288173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29028064625757396016814357 1360690529332377938288173)
                    ·
                      rfl

theorem cell22_3974903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_3974903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974903 prefixEnd_3974903 := by exact prefixLift 3974903
  have htrace : WordTrace (prefixWord ++ tailWord_3974903) baseStart_3974903 baseEnd_3974903 := by
    simpa [prefixWord, tailWord_3974903, baseEnd_3974903] using wordTrace_append hprefix tailTrace_3974903
  have hstable : (prefixWord ++ tailWord_3974903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974903).length < 2 ^ (prefixWord ++ tailWord_3974903).sum := by decide
  have hdescent : baseEnd_3974903 < baseStart_3974903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974920 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_3974920 : Nat := 118140960795 + 3974920 * 2 ^ 59
def prefixEnd_3974920 : Nat := 4983230072969 + 3 ^ 40 * 3974920 * 2
def baseEnd_3974920 : Nat := 1360696348779795560613121

theorem tailTrace_3974920 : CollatzResearch.WordTrace tailWord_3974920 prefixEnd_3974920 1360696348779795560613121 := by
  unfold tailWord_3974920
  simp only [CollatzResearch.WordTrace]
  refine ⟨72488621379775588567061107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96651495173034118089414809 72488621379775588567061107)
  ·
    refine ⟨108732932069663382850591661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72488621379775588567061107 108732932069663382850591661)
    ·
      refine ⟨40774849526123768568971873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108732932069663382850591661 40774849526123768568971873)
      ·
        refine ⟨30581137144592826426728905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40774849526123768568971873 30581137144592826426728905)
        ·
          refine ⟨22935852858444619820046679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30581137144592826426728905 22935852858444619820046679)
          ·
            refine ⟨34403779287666929730070019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22935852858444619820046679 34403779287666929730070019)
            ·
              refine ⟨51605668931500394595105029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34403779287666929730070019 51605668931500394595105029)
              ·
                refine ⟨9676062924656323986582193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51605668931500394595105029 9676062924656323986582193)
                ·
                  refine ⟨7257047193492242989936645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9676062924656323986582193 7257047193492242989936645)
                  ·
                    refine ⟨1360696348779795560613121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257047193492242989936645 1360696348779795560613121)
                    ·
                      rfl

theorem cell22_3974920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_3974920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974920 prefixEnd_3974920 := by exact prefixLift 3974920
  have htrace : WordTrace (prefixWord ++ tailWord_3974920) baseStart_3974920 baseEnd_3974920 := by
    simpa [prefixWord, tailWord_3974920, baseEnd_3974920] using wordTrace_append hprefix tailTrace_3974920
  have hstable : (prefixWord ++ tailWord_3974920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974920).length < 2 ^ (prefixWord ++ tailWord_3974920).sum := by decide
  have hdescent : baseEnd_3974920 < baseStart_3974920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974922 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_3974922 : Nat := 118140960795 + 3974922 * 2 ^ 59
def prefixEnd_3974922 : Nat := 4983230072969 + 3 ^ 40 * 3974922 * 2
def baseEnd_3974922 : Nat := 1360697033420668222063115

theorem tailTrace_3974922 : CollatzResearch.WordTrace tailWord_3974922 prefixEnd_3974922 1360697033420668222063115 := by
  unfold tailWord_3974922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36244328926385982868923755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96651543803695954317130013 36244328926385982868923755)
  ·
    refine ⟨54366493389578974303385633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36244328926385982868923755 54366493389578974303385633)
    ·
      refine ⟨40774870042184230727539225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54366493389578974303385633 40774870042184230727539225)
      ·
        refine ⟨30581152531638173045654419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40774870042184230727539225 30581152531638173045654419)
        ·
          refine ⟨45871728797457259568481629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30581152531638173045654419 45871728797457259568481629)
          ·
            refine ⟨17201898299046472338180611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45871728797457259568481629 17201898299046472338180611)
            ·
              refine ⟨25802847448569708507270917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17201898299046472338180611 25802847448569708507270917)
              ·
                refine ⟨4838033896606820345113297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25802847448569708507270917 4838033896606820345113297)
                ·
                  refine ⟨3628525422455115258834973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838033896606820345113297 3628525422455115258834973)
                  ·
                    refine ⟨1360697033420668222063115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628525422455115258834973 1360697033420668222063115)
                    ·
                      rfl

theorem cell22_3974922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_3974922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974922 prefixEnd_3974922 := by exact prefixLift 3974922
  have htrace : WordTrace (prefixWord ++ tailWord_3974922) baseStart_3974922 baseEnd_3974922 := by
    simpa [prefixWord, tailWord_3974922, baseEnd_3974922] using wordTrace_append hprefix tailTrace_3974922
  have hstable : (prefixWord ++ tailWord_3974922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974922).length < 2 ^ (prefixWord ++ tailWord_3974922).sum := by decide
  have hdescent : baseEnd_3974922 < baseStart_3974922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974935 : List Nat := [1, 1, 3, 4, 2, 1, 3, 7]
def baseStart_3974935 : Nat := 118140960795 + 3974935 * 2 ^ 59
def prefixEnd_3974935 : Nat := 4983230072969 + 3 ^ 40 * 3974935 * 2
def baseEnd_3974935 : Nat := 151189053731815613498675

theorem tailTrace_3974935 : CollatzResearch.WordTrace tailWord_3974935 prefixEnd_3974935 151189053731815613498675 := by
  unfold tailWord_3974935
  simp only [CollatzResearch.WordTrace]
  refine ⟨144977789854496834695918259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96651859902997889797278839 144977789854496834695918259)
  ·
    refine ⟨217466684781745252043877389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144977789854496834695918259 217466684781745252043877389)
    ·
      refine ⟨81550006793154469516454021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217466684781745252043877389 81550006793154469516454021)
      ·
        refine ⟨15290626273716463034335129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81550006793154469516454021 15290626273716463034335129)
        ·
          refine ⟨11467969705287347275751347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290626273716463034335129 11467969705287347275751347)
          ·
            refine ⟨17201954557931020913627021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11467969705287347275751347 17201954557931020913627021)
            ·
              refine ⟨6450732959224132842610133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17201954557931020913627021 6450732959224132842610133)
              ·
                refine ⟨151189053731815613498675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6450732959224132842610133 151189053731815613498675)
                ·
                  rfl

theorem cell22_3974935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 7].length) (baseStart_3974935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974935 prefixEnd_3974935 := by exact prefixLift 3974935
  have htrace : WordTrace (prefixWord ++ tailWord_3974935) baseStart_3974935 baseEnd_3974935 := by
    simpa [prefixWord, tailWord_3974935, baseEnd_3974935] using wordTrace_append hprefix tailTrace_3974935
  have hstable : (prefixWord ++ tailWord_3974935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974935).length < 2 ^ (prefixWord ++ tailWord_3974935).sum := by decide
  have hdescent : baseEnd_3974935 < baseStart_3974935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974952 : List Nat := [2, 1, 5, 1, 1, 3, 3, 6]
def baseStart_3974952 : Nat := 118140960795 + 3974952 * 2 ^ 59
def prefixEnd_3974952 : Nat := 4983230072969 + 3 ^ 40 * 3974952 * 2
def baseEnd_3974952 : Nat := 151189700337084238201447

theorem tailTrace_3974952 : CollatzResearch.WordTrace tailWord_3974952 prefixEnd_3974952 151189700337084238201447 := by
  unfold tailWord_3974952
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489204947717623299643555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96652273263623497732858073 72489204947717623299643555)
  ·
    refine ⟨108733807421576434949465333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72489204947717623299643555 108733807421576434949465333)
    ·
      refine ⟨10193794445772790776512375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108733807421576434949465333 10193794445772790776512375)
      ·
        refine ⟨15290691668659186164768563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193794445772790776512375 15290691668659186164768563)
        ·
          refine ⟨22936037502988779247152845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290691668659186164768563 22936037502988779247152845)
          ·
            refine ⟨8601014063620792217682317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22936037502988779247152845 8601014063620792217682317)
            ·
              refine ⟨3225380273857797081630869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8601014063620792217682317 3225380273857797081630869)
              ·
                refine ⟨151189700337084238201447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3225380273857797081630869 151189700337084238201447)
                ·
                  rfl

theorem cell22_3974952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_3974952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974952 prefixEnd_3974952 := by exact prefixLift 3974952
  have htrace : WordTrace (prefixWord ++ tailWord_3974952) baseStart_3974952 baseEnd_3974952 := by
    simpa [prefixWord, tailWord_3974952, baseEnd_3974952] using wordTrace_append hprefix tailTrace_3974952
  have hstable : (prefixWord ++ tailWord_3974952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974952).length < 2 ^ (prefixWord ++ tailWord_3974952).sum := by decide
  have hdescent : baseEnd_3974952 < baseStart_3974952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3974984 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 1, 3]
def baseStart_3974984 : Nat := 118140960795 + 3974984 * 2 ^ 59
def prefixEnd_3974984 : Nat := 4983230072969 + 3 ^ 40 * 3974984 * 2
def baseEnd_3974984 : Nat := 1360718257287720727012925

theorem tailTrace_3974984 : CollatzResearch.WordTrace tailWord_3974984 prefixEnd_3974984 1360718257287720727012925 := by
  unfold tailWord_3974984
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489788515659658032226003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96653051354212877376301337 72489788515659658032226003)
  ·
    refine ⟨108734682773489487048339005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72489788515659658032226003 108734682773489487048339005)
    ·
      refine ⟨40775506040058557643127127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108734682773489487048339005 40775506040058557643127127)
      ·
        refine ⟨61163259060087836464690691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40775506040058557643127127 61163259060087836464690691)
        ·
          refine ⟨91744888590131754697036037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61163259060087836464690691 91744888590131754697036037)
          ·
            refine ⟨17202166610649704005694257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91744888590131754697036037 17202166610649704005694257)
            ·
              refine ⟨12901624957987278004270693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17202166610649704005694257 12901624957987278004270693)
              ·
                refine ⟨2419054679622614625800755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12901624957987278004270693 2419054679622614625800755)
                ·
                  refine ⟨3628582019433921938701133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419054679622614625800755 3628582019433921938701133)
                  ·
                    refine ⟨1360718257287720727012925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628582019433921938701133 1360718257287720727012925)
                    ·
                      rfl

theorem cell22_3974984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_3974984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3974984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3974984 prefixEnd_3974984 := by exact prefixLift 3974984
  have htrace : WordTrace (prefixWord ++ tailWord_3974984) baseStart_3974984 baseEnd_3974984 := by
    simpa [prefixWord, tailWord_3974984, baseEnd_3974984] using wordTrace_append hprefix tailTrace_3974984
  have hstable : (prefixWord ++ tailWord_3974984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3974984).length < 2 ^ (prefixWord ++ tailWord_3974984).sum := by decide
  have hdescent : baseEnd_3974984 < baseStart_3974984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3974984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975074 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3975074 : Nat := 118140960795 + 3975074 * 2 ^ 59
def prefixEnd_3975074 : Nat := 4983230072969 + 3 ^ 40 * 3975074 * 2
def baseEnd_3975074 : Nat := 1360749066126990492262649

theorem tailTrace_3975074 : CollatzResearch.WordTrace tailWord_3975074 prefixEnd_3975074 1360749066126990492262649 := by
  unfold tailWord_3975074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36245714900248315358807069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96655239733995507623485517 36245714900248315358807069)
  ·
    refine ⟨13592143087593118259552651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36245714900248315358807069 13592143087593118259552651)
    ·
      refine ⟨20388214631389677389328977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13592143087593118259552651 20388214631389677389328977)
      ·
        refine ⟨15291160973542258041996733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20388214631389677389328977 15291160973542258041996733)
        ·
          refine ⟨5734185365078346765748775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15291160973542258041996733 5734185365078346765748775)
          ·
            refine ⟨8601278047617520148623163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734185365078346765748775 8601278047617520148623163)
            ·
              refine ⟨12901917071426280222934745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601278047617520148623163 12901917071426280222934745)
              ·
                refine ⟨9676437803569710167201059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12901917071426280222934745 9676437803569710167201059)
                ·
                  refine ⟨14514656705354565250801589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9676437803569710167201059 14514656705354565250801589)
                  ·
                    refine ⟨1360749066126990492262649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14514656705354565250801589 1360749066126990492262649)
                    ·
                      rfl

theorem cell22_3975074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3975074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975074 prefixEnd_3975074 := by exact prefixLift 3975074
  have htrace : WordTrace (prefixWord ++ tailWord_3975074) baseStart_3975074 baseEnd_3975074 := by
    simpa [prefixWord, tailWord_3975074, baseEnd_3975074] using wordTrace_append hprefix tailTrace_3975074
  have hstable : (prefixWord ++ tailWord_3975074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975074).length < 2 ^ (prefixWord ++ tailWord_3975074).sum := by decide
  have hdescent : baseEnd_3975074 < baseStart_3975074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975179 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 1, 4]
def baseStart_3975179 : Nat := 118140960795 + 3975179 * 2 ^ 59
def prefixEnd_3975179 : Nat := 4983230072969 + 3 ^ 40 * 3975179 * 2
def baseEnd_3975179 : Nat := 1360785009772805218387327

theorem tailTrace_3975179 : CollatzResearch.WordTrace tailWord_3975179 prefixEnd_3975179 1360785009772805218387327 := by
  unfold tailWord_3975179
  simp only [CollatzResearch.WordTrace]
  refine ⟨144986689265612864367800591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96657792843741909578533727 144986689265612864367800591)
  ·
    refine ⟨217480033898419296551700887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144986689265612864367800591 217480033898419296551700887)
    ·
      refine ⟨326220050847628944827551331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217480033898419296551700887 326220050847628944827551331)
      ·
        refine ⟨489330076271443417241326997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326220050847628944827551331 489330076271443417241326997)
        ·
          refine ⟨22937347325223910183187203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 489330076271443417241326997 22937347325223910183187203)
          ·
            refine ⟨34406020987835865274780805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22937347325223910183187203 34406020987835865274780805)
            ·
              refine ⟨6451128935219224739021401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34406020987835865274780805 6451128935219224739021401)
              ·
                refine ⟨4838346701414418554266051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451128935219224739021401 4838346701414418554266051)
                ·
                  refine ⟨7257520052121627831399077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838346701414418554266051 7257520052121627831399077)
                  ·
                    refine ⟨1360785009772805218387327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257520052121627831399077 1360785009772805218387327)
                    ·
                      rfl

theorem cell22_3975179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 4].length) (baseStart_3975179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975179 prefixEnd_3975179 := by exact prefixLift 3975179
  have htrace : WordTrace (prefixWord ++ tailWord_3975179) baseStart_3975179 baseEnd_3975179 := by
    simpa [prefixWord, tailWord_3975179, baseEnd_3975179] using wordTrace_append hprefix tailTrace_3975179
  have hstable : (prefixWord ++ tailWord_3975179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975179).length < 2 ^ (prefixWord ++ tailWord_3975179).sum := by decide
  have hdescent : baseEnd_3975179 < baseStart_3975179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975192 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3975192 : Nat := 118140960795 + 3975192 * 2 ^ 59
def prefixEnd_3975192 : Nat := 4983230072969 + 3 ^ 40 * 3975192 * 2
def baseEnd_3975192 : Nat := 1360789459938477517812287

theorem tailTrace_3975192 : CollatzResearch.WordTrace tailWord_3975192 prefixEnd_3975192 1360789459938477517812287 := by
  unfold tailWord_3975192
  simp only [CollatzResearch.WordTrace]
  refine ⟨72493581707282883794011915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96658108943043845058682553 72493581707282883794011915)
  ·
    refine ⟨108740372560924325691017873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72493581707282883794011915 108740372560924325691017873)
    ·
      refine ⟨81555279420693244268263405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108740372560924325691017873 81555279420693244268263405)
      ·
        refine ⟨30583229782759966600598777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81555279420693244268263405 30583229782759966600598777)
        ·
          refine ⟨22937422337069974950449083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30583229782759966600598777 22937422337069974950449083)
          ·
            refine ⟨34406133505604962425673625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22937422337069974950449083 34406133505604962425673625)
            ·
              refine ⟨25804600129203721819255219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34406133505604962425673625 25804600129203721819255219)
              ·
                refine ⟨38706900193805582728882829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25804600129203721819255219 38706900193805582728882829)
                ·
                  refine ⟨14515087572677093523331061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38706900193805582728882829 14515087572677093523331061)
                  ·
                    refine ⟨1360789459938477517812287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14515087572677093523331061 1360789459938477517812287)
                    ·
                      rfl

theorem cell22_3975192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3975192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975192 prefixEnd_3975192 := by exact prefixLift 3975192
  have htrace : WordTrace (prefixWord ++ tailWord_3975192) baseStart_3975192 baseEnd_3975192 := by
    simpa [prefixWord, tailWord_3975192, baseEnd_3975192] using wordTrace_append hprefix tailTrace_3975192
  have hstable : (prefixWord ++ tailWord_3975192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975192).length < 2 ^ (prefixWord ++ tailWord_3975192).sum := by decide
  have hdescent : baseEnd_3975192 < baseStart_3975192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975230 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3975230 : Nat := 118140960795 + 3975230 * 2 ^ 59
def prefixEnd_3975230 : Nat := 4983230072969 + 3 ^ 40 * 3975230 * 2
def baseEnd_3975230 : Nat := 1360802468115058085362171

theorem tailTrace_3975230 : CollatzResearch.WordTrace tailWord_3975230 prefixEnd_3975230 1360802468115058085362171 := by
  unfold tailWord_3975230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123568673553512509738393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96659032925618733385271429 18123568673553512509738393)
  ·
    refine ⟨13592676505165134382303795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18123568673553512509738393 13592676505165134382303795)
    ·
      refine ⟨20389014757747701573455693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13592676505165134382303795 20389014757747701573455693)
      ·
        refine ⟨7645880534155388090045885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20389014757747701573455693 7645880534155388090045885)
        ·
          refine ⟨2867205200308270533767207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7645880534155388090045885 2867205200308270533767207)
          ·
            refine ⟨4300807800462405800650811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867205200308270533767207 4300807800462405800650811)
            ·
              refine ⟨6451211700693608700976217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300807800462405800650811 6451211700693608700976217)
              ·
                refine ⟨4838408775520206525732163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451211700693608700976217 4838408775520206525732163)
                ·
                  refine ⟨7257613163280309788598245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838408775520206525732163 7257613163280309788598245)
                  ·
                    refine ⟨1360802468115058085362171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257613163280309788598245 1360802468115058085362171)
                    ·
                      rfl

theorem cell22_3975230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3975230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975230 prefixEnd_3975230 := by exact prefixLift 3975230
  have htrace : WordTrace (prefixWord ++ tailWord_3975230) baseStart_3975230 baseEnd_3975230 := by
    simpa [prefixWord, tailWord_3975230, baseEnd_3975230] using wordTrace_append hprefix tailTrace_3975230
  have hstable : (prefixWord ++ tailWord_3975230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975230).length < 2 ^ (prefixWord ++ tailWord_3975230).sum := by decide
  have hdescent : baseEnd_3975230 < baseStart_3975230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975267 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 7]
def baseStart_3975267 : Nat := 118140960795 + 3975267 * 2 ^ 59
def prefixEnd_3975267 : Nat := 4983230072969 + 3 ^ 40 * 3975267 * 2
def baseEnd_3975267 : Nat := 453605044657067440729019

theorem tailTrace_3975267 : CollatzResearch.WordTrace tailWord_3975267 prefixEnd_3975267 453605044657067440729019 := by
  unfold tailWord_3975267
  simp only [CollatzResearch.WordTrace]
  refine ⟨144989898889294055397004055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96659932592862703598002703 144989898889294055397004055)
  ·
    refine ⟨217484848333941083095506083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144989898889294055397004055 217484848333941083095506083)
    ·
      refine ⟨326227272500911624643259125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217484848333941083095506083 326227272500911624643259125)
      ·
        refine ⟨30583806796960464810305543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326227272500911624643259125 30583806796960464810305543)
        ·
          refine ⟨45875710195440697215458315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30583806796960464810305543 45875710195440697215458315)
          ·
            refine ⟨68813565293161045823187473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45875710195440697215458315 68813565293161045823187473)
            ·
              refine ⟨51610173969870784367390605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68813565293161045823187473 51610173969870784367390605)
              ·
                refine ⟨19353815238701544137771477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51610173969870784367390605 19353815238701544137771477)
                ·
                  refine ⟨453605044657067440729019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19353815238701544137771477 453605044657067440729019)
                  ·
                    rfl

theorem cell22_3975267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_3975267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975267 prefixEnd_3975267 := by exact prefixLift 3975267
  have htrace : WordTrace (prefixWord ++ tailWord_3975267) baseStart_3975267 baseEnd_3975267 := by
    simpa [prefixWord, tailWord_3975267, baseEnd_3975267] using wordTrace_append hprefix tailTrace_3975267
  have hstable : (prefixWord ++ tailWord_3975267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975267).length < 2 ^ (prefixWord ++ tailWord_3975267).sum := by decide
  have hdescent : baseEnd_3975267 < baseStart_3975267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975312 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_3975312 : Nat := 118140960795 + 3975312 * 2 ^ 59
def prefixEnd_3975312 : Nat := 4983230072969 + 3 ^ 40 * 3975312 * 2
def baseEnd_3975312 : Nat := 453610179463612401603973

theorem tailTrace_3975312 : CollatzResearch.WordTrace tailWord_3975312 prefixEnd_3975312 453610179463612401603973 := by
  unfold tailWord_3975312
  simp only [CollatzResearch.WordTrace]
  refine ⟨72495770087065514041196095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96661026782754018721594793 72495770087065514041196095)
  ·
    refine ⟨108743655130598271061794143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72495770087065514041196095 108743655130598271061794143)
    ·
      refine ⟨163115482695897406592691215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108743655130598271061794143 163115482695897406592691215)
      ·
        refine ⟨244673224043846109889036823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163115482695897406592691215 244673224043846109889036823)
        ·
          refine ⟨367009836065769164833555235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244673224043846109889036823 367009836065769164833555235)
          ·
            refine ⟨550514754098653747250332853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367009836065769164833555235 550514754098653747250332853)
            ·
              refine ⟨51610758196748788804718705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 550514754098653747250332853 51610758196748788804718705)
              ·
                refine ⟨38708068647561591603539029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51610758196748788804718705 38708068647561591603539029)
                ·
                  refine ⟨453610179463612401603973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38708068647561591603539029 453610179463612401603973)
                  ·
                    rfl

theorem cell22_3975312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_3975312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975312 prefixEnd_3975312 := by exact prefixLift 3975312
  have htrace : WordTrace (prefixWord ++ tailWord_3975312) baseStart_3975312 baseEnd_3975312 := by
    simpa [prefixWord, tailWord_3975312, baseEnd_3975312] using wordTrace_append hprefix tailTrace_3975312
  have hstable : (prefixWord ++ tailWord_3975312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975312).length < 2 ^ (prefixWord ++ tailWord_3975312).sum := by decide
  have hdescent : baseEnd_3975312 < baseStart_3975312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975329 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 6]
def baseStart_3975329 : Nat := 118140960795 + 3975329 * 2 ^ 59
def prefixEnd_3975329 : Nat := 4983230072969 + 3 ^ 40 * 3975329 * 2
def baseEnd_3975329 : Nat := 453612119279418275712289

theorem tailTrace_3975329 : CollatzResearch.WordTrace tailWord_3975329 prefixEnd_3975329 453612119279418275712289 := by
  unfold tailWord_3975329
  simp only [CollatzResearch.WordTrace]
  refine ⟨144992160215069439985761041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96661440143379626657174027 144992160215069439985761041)
  ·
    refine ⟨108744120161302079989320781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144992160215069439985761041 108744120161302079989320781)
    ·
      refine ⟨40779045060488279995995293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108744120161302079989320781 40779045060488279995995293)
      ·
        refine ⟨15292141897683104998498235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40779045060488279995995293 15292141897683104998498235)
        ·
          refine ⟨22938212846524657497747353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15292141897683104998498235 22938212846524657497747353)
          ·
            refine ⟨17203659634893493123310515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22938212846524657497747353 17203659634893493123310515)
            ·
              refine ⟨25805489452340239684965773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17203659634893493123310515 25805489452340239684965773)
              ·
                refine ⟨9677058544627589881862165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25805489452340239684965773 9677058544627589881862165)
                ·
                  refine ⟨453612119279418275712289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9677058544627589881862165 453612119279418275712289)
                  ·
                    rfl

theorem cell22_3975329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_3975329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975329 prefixEnd_3975329 := by exact prefixLift 3975329
  have htrace : WordTrace (prefixWord ++ tailWord_3975329) baseStart_3975329 baseEnd_3975329 := by
    simpa [prefixWord, tailWord_3975329, baseEnd_3975329] using wordTrace_append hprefix tailTrace_3975329
  have hstable : (prefixWord ++ tailWord_3975329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975329).length < 2 ^ (prefixWord ++ tailWord_3975329).sum := by decide
  have hdescent : baseEnd_3975329 < baseStart_3975329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975344 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_3975344 : Nat := 118140960795 + 3975344 * 2 ^ 59
def prefixEnd_3975344 : Nat := 4983230072969 + 3 ^ 40 * 3975344 * 2
def baseEnd_3975344 : Nat := 1360841492644799788011821

theorem tailTrace_3975344 : CollatzResearch.WordTrace tailWord_3975344 prefixEnd_3975344 1360841492644799788011821 := by
  unfold tailWord_3975344
  simp only [CollatzResearch.WordTrace]
  refine ⟨72496353655007548773778543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96661804873343398365038057 72496353655007548773778543)
  ·
    refine ⟨108744530482511323160667815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72496353655007548773778543 108744530482511323160667815)
    ·
      refine ⟨163116795723766984741001723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108744530482511323160667815 163116795723766984741001723)
      ·
        refine ⟨244675193585650477111502585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163116795723766984741001723 244675193585650477111502585)
        ·
          refine ⟨183506395189237857833626939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244675193585650477111502585 183506395189237857833626939)
          ·
            refine ⟨275259592783856786750440409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183506395189237857833626939 275259592783856786750440409)
            ·
              refine ⟨206444694587892590062830307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275259592783856786750440409 206444694587892590062830307)
              ·
                refine ⟨309667041881838885094245461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206444694587892590062830307 309667041881838885094245461)
                ·
                  refine ⟨3628910647052799434698189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 309667041881838885094245461 3628910647052799434698189)
                  ·
                    refine ⟨1360841492644799788011821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628910647052799434698189 1360841492644799788011821)
                    ·
                      rfl

theorem cell22_3975344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_3975344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975344 prefixEnd_3975344 := by exact prefixLift 3975344
  have htrace : WordTrace (prefixWord ++ tailWord_3975344) baseStart_3975344 baseEnd_3975344 := by
    simpa [prefixWord, tailWord_3975344, baseEnd_3975344] using wordTrace_append hprefix tailTrace_3975344
  have hstable : (prefixWord ++ tailWord_3975344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975344).length < 2 ^ (prefixWord ++ tailWord_3975344).sum := by decide
  have hdescent : baseEnd_3975344 < baseStart_3975344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975359 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_3975359 : Nat := 118140960795 + 3975359 * 2 ^ 59
def prefixEnd_3975359 : Nat := 4983230072969 + 3 ^ 40 * 3975359 * 2
def baseEnd_3975359 : Nat := 1360846627451344748886775

theorem tailTrace_3975359 : CollatzResearch.WordTrace tailWord_3975359 prefixEnd_3975359 1360846627451344748886775 := by
  unfold tailWord_3975359
  simp only [CollatzResearch.WordTrace]
  refine ⟨144993254404960755109353131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96662169603307170072902087 144993254404960755109353131)
  ·
    refine ⟨217489881607441132664029697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144993254404960755109353131 217489881607441132664029697)
    ·
      refine ⟨163117411205580849498022273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217489881607441132664029697 163117411205580849498022273)
      ·
        refine ⟨122338058404185637123516705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163117411205580849498022273 122338058404185637123516705)
        ·
          refine ⟨91753543803139227842637529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122338058404185637123516705 91753543803139227842637529)
          ·
            refine ⟨68815157852354420881978147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91753543803139227842637529 68815157852354420881978147)
            ·
              refine ⟨103222736778531631322967221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68815157852354420881978147 103222736778531631322967221)
              ·
                refine ⟨9677131572987340436528177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103222736778531631322967221 9677131572987340436528177)
                ·
                  refine ⟨7257848679740505327396133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9677131572987340436528177 7257848679740505327396133)
                  ·
                    refine ⟨1360846627451344748886775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257848679740505327396133 1360846627451344748886775)
                    ·
                      rfl

theorem cell22_3975359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_3975359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975359 prefixEnd_3975359 := by exact prefixLift 3975359
  have htrace : WordTrace (prefixWord ++ tailWord_3975359) baseStart_3975359 baseEnd_3975359 := by
    simpa [prefixWord, tailWord_3975359, baseEnd_3975359] using wordTrace_append hprefix tailTrace_3975359
  have hstable : (prefixWord ++ tailWord_3975359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975359).length < 2 ^ (prefixWord ++ tailWord_3975359).sum := by decide
  have hdescent : baseEnd_3975359 < baseStart_3975359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975374 : List Nat := [4, 1, 1, 1, 4, 1, 10]
def baseStart_3975374 : Nat := 118140960795 + 3975374 * 2 ^ 59
def prefixEnd_3975374 : Nat := 4983230072969 + 3 ^ 40 * 3975374 * 2
def baseEnd_3975374 : Nat := 50401917120662581843027

theorem tailTrace_3975374 : CollatzResearch.WordTrace tailWord_3975374 prefixEnd_3975374 50401917120662581843027 := by
  unfold tailWord_3975374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124225187488301583893647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96662534333270941780766117 18124225187488301583893647)
  ·
    refine ⟨27186337781232452375840471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18124225187488301583893647 27186337781232452375840471)
    ·
      refine ⟨40779506671848678563760707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27186337781232452375840471 40779506671848678563760707)
      ·
        refine ⟨61169260007773017845641061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40779506671848678563760707 61169260007773017845641061)
        ·
          refine ⟨11469236251457440846057699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61169260007773017845641061 11469236251457440846057699)
          ·
            refine ⟨17203854377186161269086549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469236251457440846057699 17203854377186161269086549)
            ·
              refine ⟨50401917120662581843027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17203854377186161269086549 50401917120662581843027)
              ·
                rfl

theorem cell22_3975374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 10].length) (baseStart_3975374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975374 prefixEnd_3975374 := by exact prefixLift 3975374
  have htrace : WordTrace (prefixWord ++ tailWord_3975374) baseStart_3975374 baseEnd_3975374 := by
    simpa [prefixWord, tailWord_3975374, baseEnd_3975374] using wordTrace_append hprefix tailTrace_3975374
  have hstable : (prefixWord ++ tailWord_3975374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975374).length < 2 ^ (prefixWord ++ tailWord_3975374).sum := by decide
  have hdescent : baseEnd_3975374 < baseStart_3975374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975395 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 2, 3]
def baseStart_3975395 : Nat := 118140960795 + 3975395 * 2 ^ 59
def prefixEnd_3975395 : Nat := 4983230072969 + 3 ^ 40 * 3975395 * 2
def baseEnd_3975395 : Nat := 1360858950987052654986665

theorem tailTrace_3975395 : CollatzResearch.WordTrace tailWord_3975395 prefixEnd_3975395 1360858950987052654986665 := by
  unfold tailWord_3975395
  simp only [CollatzResearch.WordTrace]
  refine ⟨144994567432830333257663639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96663044955220222171775759 144994567432830333257663639)
  ·
    refine ⟨217491851149245499886495459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144994567432830333257663639 217491851149245499886495459)
    ·
      refine ⟨326237776723868249829743189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217491851149245499886495459 326237776723868249829743189)
      ·
        refine ⟨3823098945982831052692303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 326237776723868249829743189 3823098945982831052692303)
        ·
          refine ⟨5734648418974246579038455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823098945982831052692303 5734648418974246579038455)
          ·
            refine ⟨8601972628461369868557683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734648418974246579038455 8601972628461369868557683)
            ·
              refine ⟨12902958942692054802836525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601972628461369868557683 12902958942692054802836525)
              ·
                refine ⟨4838609603509520551063697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12902958942692054802836525 4838609603509520551063697)
                ·
                  refine ⟨3628957202632140413297773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838609603509520551063697 3628957202632140413297773)
                  ·
                    refine ⟨1360858950987052654986665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628957202632140413297773 1360858950987052654986665)
                    ·
                      rfl

theorem cell22_3975395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 2, 3].length) (baseStart_3975395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975395 prefixEnd_3975395 := by exact prefixLift 3975395
  have htrace : WordTrace (prefixWord ++ tailWord_3975395) baseStart_3975395 baseEnd_3975395 := by
    simpa [prefixWord, tailWord_3975395, baseEnd_3975395] using wordTrace_append hprefix tailTrace_3975395
  have hstable : (prefixWord ++ tailWord_3975395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975395).length < 2 ^ (prefixWord ++ tailWord_3975395).sum := by decide
  have hdescent : baseEnd_3975395 < baseStart_3975395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975406 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3975406 : Nat := 118140960795 + 3975406 * 2 ^ 59
def prefixEnd_3975406 : Nat := 4983230072969 + 3 ^ 40 * 3975406 * 2
def baseEnd_3975406 : Nat := 1360862716511852292961631

theorem tailTrace_3975406 : CollatzResearch.WordTrace tailWord_3975406 prefixEnd_3975406 1360862716511852292961631 := by
  unfold tailWord_3975406
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124371079473810267039259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 96663312423860321424209381 18124371079473810267039259)
  ·
    refine ⟨27186556619210715400558889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18124371079473810267039259 27186556619210715400558889)
    ·
      refine ⟨20389917464408036550419167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27186556619210715400558889 20389917464408036550419167)
      ·
        refine ⟨30584876196612054825628751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389917464408036550419167 30584876196612054825628751)
        ·
          refine ⟨45877314294918082238443127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30584876196612054825628751 45877314294918082238443127)
          ·
            refine ⟨68815971442377123357664691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45877314294918082238443127 68815971442377123357664691)
            ·
              refine ⟨103223957163565685036497037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68815971442377123357664691 103223957163565685036497037)
              ·
                refine ⟨38708983936337131888686389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103223957163565685036497037 38708983936337131888686389)
                ·
                  refine ⟨3628967244031606114564349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38708983936337131888686389 3628967244031606114564349)
                  ·
                    refine ⟨1360862716511852292961631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628967244031606114564349 1360862716511852292961631)
                    ·
                      rfl

theorem cell22_3975406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3975406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975406 prefixEnd_3975406 := by exact prefixLift 3975406
  have htrace : WordTrace (prefixWord ++ tailWord_3975406) baseStart_3975406 baseEnd_3975406 := by
    simpa [prefixWord, tailWord_3975406, baseEnd_3975406] using wordTrace_append hprefix tailTrace_3975406
  have hstable : (prefixWord ++ tailWord_3975406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975406).length < 2 ^ (prefixWord ++ tailWord_3975406).sum := by decide
  have hdescent : baseEnd_3975406 < baseStart_3975406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975423 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 1, 3]
def baseStart_3975423 : Nat := 118140960795 + 3975423 * 2 ^ 59
def prefixEnd_3975423 : Nat := 4983230072969 + 3 ^ 40 * 3975423 * 2
def baseEnd_3975423 : Nat := 1360868535959269915286579

theorem tailTrace_3975423 : CollatzResearch.WordTrace tailWord_3975423 prefixEnd_3975423 1360868535959269915286579 := by
  unfold tailWord_3975423
  simp only [CollatzResearch.WordTrace]
  refine ⟨144995588676728894039682923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96663725784485929359788615 144995588676728894039682923)
  ·
    refine ⟨217493383015093341059524385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144995588676728894039682923 217493383015093341059524385)
    ·
      refine ⟨163120037261320005794643289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217493383015093341059524385 163120037261320005794643289)
      ·
        refine ⟨122340027945990004345982467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163120037261320005794643289 122340027945990004345982467)
        ·
          refine ⟨183510041918985006518973701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122340027945990004345982467 183510041918985006518973701)
          ·
            refine ⟨34408132859809688722307569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183510041918985006518973701 34408132859809688722307569)
            ·
              refine ⟨25806099644857266541730677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34408132859809688722307569 25806099644857266541730677)
              ·
                refine ⟨2419321841705368738287251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25806099644857266541730677 2419321841705368738287251)
                ·
                  refine ⟨3628982762558053107430877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419321841705368738287251 3628982762558053107430877)
                  ·
                    refine ⟨1360868535959269915286579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3628982762558053107430877 1360868535959269915286579)
                    ·
                      rfl

theorem cell22_3975423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_3975423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975423 prefixEnd_3975423 := by exact prefixLift 3975423
  have htrace : WordTrace (prefixWord ++ tailWord_3975423) baseStart_3975423 baseEnd_3975423 := by
    simpa [prefixWord, tailWord_3975423, baseEnd_3975423] using wordTrace_append hprefix tailTrace_3975423
  have hstable : (prefixWord ++ tailWord_3975423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975423).length < 2 ^ (prefixWord ++ tailWord_3975423).sum := by decide
  have hdescent : baseEnd_3975423 < baseStart_3975423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975436 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_3975436 : Nat := 118140960795 + 3975436 * 2 ^ 59
def prefixEnd_3975436 : Nat := 4983230072969 + 3 ^ 40 * 3975436 * 2
def baseEnd_3975436 : Nat := 453624328708314071570513

theorem tailTrace_3975436 : CollatzResearch.WordTrace tailWord_3975436 prefixEnd_3975436 453624328708314071570513 := by
  unfold tailWord_3975436
  simp only [CollatzResearch.WordTrace]
  refine ⟨72498031412840898629953081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96664041883787864839937441 72498031412840898629953081)
  ·
    refine ⟨54373523559630673972464811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72498031412840898629953081 54373523559630673972464811)
    ·
      refine ⟨81560285339446010958697217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54373523559630673972464811 81560285339446010958697217)
      ·
        refine ⟨61170214004584508219022913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81560285339446010958697217 61170214004584508219022913)
        ·
          refine ⟨45877660503438381164267185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61170214004584508219022913 45877660503438381164267185)
          ·
            refine ⟨34408245377578785873200389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45877660503438381164267185 34408245377578785873200389)
            ·
              refine ⟨6451546008296022351225073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34408245377578785873200389 6451546008296022351225073)
              ·
                refine ⟨4838659506222016763418805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451546008296022351225073 4838659506222016763418805)
                ·
                  refine ⟨453624328708314071570513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4838659506222016763418805 453624328708314071570513)
                  ·
                    rfl

theorem cell22_3975436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_3975436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975436 prefixEnd_3975436 := by exact prefixLift 3975436
  have htrace : WordTrace (prefixWord ++ tailWord_3975436) baseStart_3975436 baseEnd_3975436 := by
    simpa [prefixWord, tailWord_3975436, baseEnd_3975436] using wordTrace_append hprefix tailTrace_3975436
  have hstable : (prefixWord ++ tailWord_3975436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975436).length < 2 ^ (prefixWord ++ tailWord_3975436).sum := by decide
  have hdescent : baseEnd_3975436 < baseStart_3975436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975532 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_3975532 : Nat := 118140960795 + 3975532 * 2 ^ 59
def prefixEnd_3975532 : Nat := 4983230072969 + 3 ^ 40 * 3975532 * 2
def baseEnd_3975532 : Nat := 453635282962276654770415

theorem tailTrace_3975532 : CollatzResearch.WordTrace tailWord_3975532 prefixEnd_3975532 453635282962276654770415 := by
  unfold tailWord_3975532
  simp only [CollatzResearch.WordTrace]
  refine ⟨72499782116667002827700425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96666376155556003770267233 72499782116667002827700425)
  ·
    refine ⟨54374836587500252120775319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72499782116667002827700425 54374836587500252120775319)
    ·
      refine ⟨81562254881250378181162979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54374836587500252120775319 81562254881250378181162979)
      ·
        refine ⟨122343382321875567271744469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81562254881250378181162979 122343382321875567271744469)
        ·
          refine ⟨2867423023168958607931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 122343382321875567271744469 2867423023168958607931511)
          ·
            refine ⟨4301134534753437911897267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867423023168958607931511 4301134534753437911897267)
            ·
              refine ⟨6451701802130156867845901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4301134534753437911897267 6451701802130156867845901)
              ·
                refine ⟨2419388175798808825442213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6451701802130156867845901 2419388175798808825442213)
                ·
                  refine ⟨453635282962276654770415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2419388175798808825442213 453635282962276654770415)
                  ·
                    rfl

theorem cell22_3975532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_3975532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975532 prefixEnd_3975532 := by exact prefixLift 3975532
  have htrace : WordTrace (prefixWord ++ tailWord_3975532) baseStart_3975532 baseEnd_3975532 := by
    simpa [prefixWord, tailWord_3975532, baseEnd_3975532] using wordTrace_append hprefix tailTrace_3975532
  have hstable : (prefixWord ++ tailWord_3975532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975532).length < 2 ^ (prefixWord ++ tailWord_3975532).sum := by decide
  have hdescent : baseEnd_3975532 < baseStart_3975532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975556 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3975556 : Nat := 118140960795 + 3975556 * 2 ^ 59
def prefixEnd_3975556 : Nat := 4983230072969 + 3 ^ 40 * 3975556 * 2
def baseEnd_3975556 : Nat := 1360914064577301901711171

theorem tailTrace_3975556 : CollatzResearch.WordTrace tailWord_3975556 prefixEnd_3975556 1360914064577301901711171 := by
  unfold tailWord_3975556
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500219792623528877137261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96666959723498038502849681 72500219792623528877137261)
  ·
    refine ⟨27187582422233823328926473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72500219792623528877137261 27187582422233823328926473)
    ·
      refine ⟨20390686816675367496694855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27187582422233823328926473 20390686816675367496694855)
      ·
        refine ⟨30586030225013051245042283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20390686816675367496694855 30586030225013051245042283)
        ·
          refine ⟨45879045337519576867563425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30586030225013051245042283 45879045337519576867563425)
          ·
            refine ⟨34409284003139682650672569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45879045337519576867563425 34409284003139682650672569)
            ·
              refine ⟨25806963002354761988004427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34409284003139682650672569 25806963002354761988004427)
              ·
                refine ⟨38710444503532142982006641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25806963002354761988004427 38710444503532142982006641)
                ·
                  refine ⟨29032833377649107236504981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38710444503532142982006641 29032833377649107236504981)
                  ·
                    refine ⟨1360914064577301901711171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29032833377649107236504981 1360914064577301901711171)
                    ·
                      rfl

theorem cell22_3975556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3975556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975556 prefixEnd_3975556 := by exact prefixLift 3975556
  have htrace : WordTrace (prefixWord ++ tailWord_3975556) baseStart_3975556 baseEnd_3975556 := by
    simpa [prefixWord, tailWord_3975556, baseEnd_3975556] using wordTrace_append hprefix tailTrace_3975556
  have hstable : (prefixWord ++ tailWord_3975556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975556).length < 2 ^ (prefixWord ++ tailWord_3975556).sum := by decide
  have hdescent : baseEnd_3975556 < baseStart_3975556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975605 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 5]
def baseStart_3975605 : Nat := 118140960795 + 3975605 * 2 ^ 59
def prefixEnd_3975605 : Nat := 4983230072969 + 3 ^ 40 * 3975605 * 2
def baseEnd_3975605 : Nat := 453643612759560702412007

theorem tailTrace_3975605 : CollatzResearch.WordTrace tailWord_3975605 prefixEnd_3975605 453643612759560702412007 := by
  unfold tailWord_3975605
  simp only [CollatzResearch.WordTrace]
  refine ⟨145002226762069539122808269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96668151174713026081872179 145002226762069539122808269)
  ·
    refine ⟨54375835035776077171053101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145002226762069539122808269 54375835035776077171053101)
    ·
      refine ⟨20390938138416028939144913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54375835035776077171053101 20390938138416028939144913)
      ·
        refine ⟨15293203603812021704358685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20390938138416028939144913 15293203603812021704358685)
        ·
          refine ⟨5734951351429508139134507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15293203603812021704358685 5734951351429508139134507)
          ·
            refine ⟨8602427027144262208701761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734951351429508139134507 8602427027144262208701761)
            ·
              refine ⟨6451820270358196656526321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602427027144262208701761 6451820270358196656526321)
              ·
                refine ⟨4838865202768647492394741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451820270358196656526321 4838865202768647492394741)
                ·
                  refine ⟨453643612759560702412007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4838865202768647492394741 453643612759560702412007)
                  ·
                    rfl

theorem cell22_3975605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_3975605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975605 prefixEnd_3975605 := by exact prefixLift 3975605
  have htrace : WordTrace (prefixWord ++ tailWord_3975605) baseStart_3975605 baseEnd_3975605 := by
    simpa [prefixWord, tailWord_3975605, baseEnd_3975605] using wordTrace_append hprefix tailTrace_3975605
  have hstable : (prefixWord ++ tailWord_3975605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975605).length < 2 ^ (prefixWord ++ tailWord_3975605).sum := by decide
  have hdescent : baseEnd_3975605 < baseStart_3975605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975609 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 1, 3]
def baseStart_3975609 : Nat := 118140960795 + 3975609 * 2 ^ 59
def prefixEnd_3975609 : Nat := 4983230072969 + 3 ^ 40 * 3975609 * 2
def baseEnd_3975609 : Nat := 1360932207560427430136009

theorem tailTrace_3975609 : CollatzResearch.WordTrace tailWord_3975609 prefixEnd_3975609 1360932207560427430136009 := by
  unfold tailWord_3975609
  simp only [CollatzResearch.WordTrace]
  refine ⟨145002372654055047805953881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96668248436036698537302587 145002372654055047805953881)
  ·
    refine ⟨108751779490541285854465411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145002372654055047805953881 108751779490541285854465411)
    ·
      refine ⟨163127669235811928781698117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108751779490541285854465411 163127669235811928781698117)
      ·
        refine ⟨30586437981714736646568397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163127669235811928781698117 30586437981714736646568397)
        ·
          refine ⟨11469914243143026242463149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30586437981714736646568397 11469914243143026242463149)
          ·
            refine ⟨4301217841178634840923681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11469914243143026242463149 4301217841178634840923681)
            ·
              refine ⟨3225913380883976130692761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301217841178634840923681 3225913380883976130692761)
              ·
                refine ⟨2419435035662982098019571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225913380883976130692761 2419435035662982098019571)
                ·
                  refine ⟨3629152553494473147029357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419435035662982098019571 3629152553494473147029357)
                  ·
                    refine ⟨1360932207560427430136009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629152553494473147029357 1360932207560427430136009)
                    ·
                      rfl

theorem cell22_3975609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_3975609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975609 prefixEnd_3975609 := by exact prefixLift 3975609
  have htrace : WordTrace (prefixWord ++ tailWord_3975609) baseStart_3975609 baseEnd_3975609 := by
    simpa [prefixWord, tailWord_3975609, baseEnd_3975609] using wordTrace_append hprefix tailTrace_3975609
  have hstable : (prefixWord ++ tailWord_3975609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975609).length < 2 ^ (prefixWord ++ tailWord_3975609).sum := by decide
  have hdescent : baseEnd_3975609 < baseStart_3975609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975616 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_3975616 : Nat := 118140960795 + 3975616 * 2 ^ 59
def prefixEnd_3975616 : Nat := 4983230072969 + 3 ^ 40 * 3975616 * 2
def baseEnd_3975616 : Nat := 453644867934493915070329

theorem tailTrace_3975616 : CollatzResearch.WordTrace tailWord_3975616 prefixEnd_3975616 453644867934493915070329 := by
  unfold tailWord_3975616
  simp only [CollatzResearch.WordTrace]
  refine ⟨72501313982514844000729351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96668418643353125334305801 72501313982514844000729351)
  ·
    refine ⟨108751970973772266001094027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72501313982514844000729351 108751970973772266001094027)
    ·
      refine ⟨163127956460658399001641041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108751970973772266001094027 163127956460658399001641041)
      ·
        refine ⟨122345967345493799251230781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163127956460658399001641041 122345967345493799251230781)
        ·
          refine ⟨45879737754560174719211543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122345967345493799251230781 45879737754560174719211543)
          ·
            refine ⟨68819606631840262078817315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45879737754560174719211543 68819606631840262078817315)
            ·
              refine ⟨103229409947760393118225973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68819606631840262078817315 103229409947760393118225973)
              ·
                refine ⟨9677757182602536854833685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103229409947760393118225973 9677757182602536854833685)
                ·
                  refine ⟨453644867934493915070329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9677757182602536854833685 453644867934493915070329)
                  ·
                    rfl

theorem cell22_3975616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_3975616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975616 prefixEnd_3975616 := by exact prefixLift 3975616
  have htrace : WordTrace (prefixWord ++ tailWord_3975616) baseStart_3975616 baseEnd_3975616 := by
    simpa [prefixWord, tailWord_3975616, baseEnd_3975616] using wordTrace_append hprefix tailTrace_3975616
  have hstable : (prefixWord ++ tailWord_3975616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975616).length < 2 ^ (prefixWord ++ tailWord_3975616).sum := by decide
  have hdescent : baseEnd_3975616 < baseStart_3975616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975620 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3975620 : Nat := 118140960795 + 3975620 * 2 ^ 59
def prefixEnd_3975620 : Nat := 4983230072969 + 3 ^ 40 * 3975620 * 2
def baseEnd_3975620 : Nat := 1360935973085227068110975

theorem tailTrace_3975620 : CollatzResearch.WordTrace tailWord_3975620 prefixEnd_3975620 1360935973085227068110975 := by
  unfold tailWord_3975620
  simp only [CollatzResearch.WordTrace]
  refine ⟨72501386928507598342302157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96668515904676797789736209 72501386928507598342302157)
  ·
    refine ⟨27188020098190349378363309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72501386928507598342302157 27188020098190349378363309)
    ·
      refine ⟨10195507536821381016886241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27188020098190349378363309 10195507536821381016886241)
      ·
        refine ⟨7646630652616035762664681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10195507536821381016886241 7646630652616035762664681)
        ·
          refine ⟨5734972989462026821998511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7646630652616035762664681 5734972989462026821998511)
          ·
            refine ⟨8602459484193040232997767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734972989462026821998511 8602459484193040232997767)
            ·
              refine ⟨12903689226289560349496651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8602459484193040232997767 12903689226289560349496651)
              ·
                refine ⟨19355533839434340524244977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12903689226289560349496651 19355533839434340524244977)
                ·
                  refine ⟨14516650379575755393183733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19355533839434340524244977 14516650379575755393183733)
                  ·
                    refine ⟨1360935973085227068110975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14516650379575755393183733 1360935973085227068110975)
                    ·
                      rfl

theorem cell22_3975620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3975620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975620 prefixEnd_3975620 := by exact prefixLift 3975620
  have htrace : WordTrace (prefixWord ++ tailWord_3975620) baseStart_3975620 baseEnd_3975620 := by
    simpa [prefixWord, tailWord_3975620, baseEnd_3975620] using wordTrace_append hprefix tailTrace_3975620
  have hstable : (prefixWord ++ tailWord_3975620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975620).length < 2 ^ (prefixWord ++ tailWord_3975620).sum := by decide
  have hdescent : baseEnd_3975620 < baseStart_3975620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975648 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_3975648 : Nat := 118140960795 + 3975648 * 2 ^ 59
def prefixEnd_3975648 : Nat := 4983230072969 + 3 ^ 40 * 3975648 * 2
def baseEnd_3975648 : Nat := 1360945558057444328410889

theorem tailTrace_3975648 : CollatzResearch.WordTrace tailWord_3975648 prefixEnd_3975648 1360945558057444328410889 := by
  unfold tailWord_3975648
  simp only [CollatzResearch.WordTrace]
  refine ⟨72501897550456878733311799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96669196733942504977749065 72501897550456878733311799)
  ·
    refine ⟨108752846325685318099967699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72501897550456878733311799 108752846325685318099967699)
    ·
      refine ⟨163129269488527977149951549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108752846325685318099967699 163129269488527977149951549)
      ·
        refine ⟨61173476058197991431231831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163129269488527977149951549 61173476058197991431231831)
        ·
          refine ⟨91760214087296987146847747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61173476058197991431231831 91760214087296987146847747)
          ·
            refine ⟨137640321130945480720271621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91760214087296987146847747 137640321130945480720271621)
            ·
              refine ⟨25807560212052277635050929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137640321130945480720271621 25807560212052277635050929)
              ·
                refine ⟨19355670159039208226288197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25807560212052277635050929 19355670159039208226288197)
                ·
                  refine ⟨3629188154819851542429037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19355670159039208226288197 3629188154819851542429037)
                  ·
                    refine ⟨1360945558057444328410889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629188154819851542429037 1360945558057444328410889)
                    ·
                      rfl

theorem cell22_3975648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_3975648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975648 prefixEnd_3975648 := by exact prefixLift 3975648
  have htrace : WordTrace (prefixWord ++ tailWord_3975648) baseStart_3975648 baseEnd_3975648 := by
    simpa [prefixWord, tailWord_3975648, baseEnd_3975648] using wordTrace_append hprefix tailTrace_3975648
  have hstable : (prefixWord ++ tailWord_3975648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975648).length < 2 ^ (prefixWord ++ tailWord_3975648).sum := by decide
  have hdescent : baseEnd_3975648 < baseStart_3975648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975686 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_3975686 : Nat := 118140960795 + 3975686 * 2 ^ 59
def prefixEnd_3975686 : Nat := 4983230072969 + 3 ^ 40 * 3975686 * 2
def baseEnd_3975686 : Nat := 1360958566234024895960773

theorem tailTrace_3975686 : CollatzResearch.WordTrace tailWord_3975686 prefixEnd_3975686 1360958566234024895960773 := by
  unfold tailWord_3975686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531411908586752811140841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 96670120716517393304337941 4531411908586752811140841)
  ·
    refine ⟨3398558931440064608355631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4531411908586752811140841 3398558931440064608355631)
    ·
      refine ⟨5097838397160096912533447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398558931440064608355631 5097838397160096912533447)
      ·
        refine ⟨7646757595740145368800171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097838397160096912533447 7646757595740145368800171)
        ·
          refine ⟨11470136393610218053200257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646757595740145368800171 11470136393610218053200257)
          ·
            refine ⟨8602602295207663539900193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11470136393610218053200257 8602602295207663539900193)
            ·
              refine ⟨6451951721405747654925145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602602295207663539900193 6451951721405747654925145)
              ·
                refine ⟨4838963791054310741193859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451951721405747654925145 4838963791054310741193859)
                ·
                  refine ⟨7258445686581466111790789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838963791054310741193859 7258445686581466111790789)
                  ·
                    refine ⟨1360958566234024895960773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7258445686581466111790789 1360958566234024895960773)
                    ·
                      rfl

theorem cell22_3975686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_3975686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975686 prefixEnd_3975686 := by exact prefixLift 3975686
  have htrace : WordTrace (prefixWord ++ tailWord_3975686) baseStart_3975686 baseEnd_3975686 := by
    simpa [prefixWord, tailWord_3975686, baseEnd_3975686] using wordTrace_append hprefix tailTrace_3975686
  have hstable : (prefixWord ++ tailWord_3975686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975686).length < 2 ^ (prefixWord ++ tailWord_3975686).sum := by decide
  have hdescent : baseEnd_3975686 < baseStart_3975686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975740 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_3975740 : Nat := 118140960795 + 3975740 * 2 ^ 59
def prefixEnd_3975740 : Nat := 4983230072969 + 3 ^ 40 * 3975740 * 2
def baseEnd_3975740 : Nat := 453659017179195585036869

theorem tailTrace_3975740 : CollatzResearch.WordTrace tailWord_3975740 prefixEnd_3975740 453659017179195585036869 := by
  unfold tailWord_3975740
  simp only [CollatzResearch.WordTrace]
  refine ⟨72503575308290228589486337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 96671433744386971452648449 72503575308290228589486337)
  ·
    refine ⟨54377681481217671442114753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72503575308290228589486337 54377681481217671442114753)
    ·
      refine ⟨40783261110913253581586065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54377681481217671442114753 40783261110913253581586065)
      ·
        refine ⟨30587445833184940186189549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40783261110913253581586065 30587445833184940186189549)
        ·
          refine ⟨11470292187444352569821081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30587445833184940186189549 11470292187444352569821081)
          ·
            refine ⟨8602719140583264427365811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11470292187444352569821081 8602719140583264427365811)
            ·
              refine ⟨12904078710874896641048717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8602719140583264427365811 12904078710874896641048717)
              ·
                refine ⟨4839029516578086240393269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12904078710874896641048717 4839029516578086240393269)
                ·
                  refine ⟨453659017179195585036869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4839029516578086240393269 453659017179195585036869)
                  ·
                    rfl

theorem cell22_3975740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_3975740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975740 prefixEnd_3975740 := by exact prefixLift 3975740
  have htrace : WordTrace (prefixWord ++ tailWord_3975740) baseStart_3975740 baseEnd_3975740 := by
    simpa [prefixWord, tailWord_3975740, baseEnd_3975740] using wordTrace_append hprefix tailTrace_3975740
  have hstable : (prefixWord ++ tailWord_3975740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975740).length < 2 ^ (prefixWord ++ tailWord_3975740).sum := by decide
  have hdescent : baseEnd_3975740 < baseStart_3975740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975783 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3975783 : Nat := 118140960795 + 3975783 * 2 ^ 59
def prefixEnd_3975783 : Nat := 4983230072969 + 3 ^ 40 * 3975783 * 2
def baseEnd_3975783 : Nat := 1360991771316348976285475

theorem tailTrace_3975783 : CollatzResearch.WordTrace tailWord_3975783 prefixEnd_3975783 1360991771316348976285475 := by
  unfold tailWord_3975783
  simp only [CollatzResearch.WordTrace]
  refine ⟨145008718955424675522788003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 96672479303616450348525335 145008718955424675522788003)
  ·
    refine ⟨217513078433137013284182005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145008718955424675522788003 217513078433137013284182005)
    ·
      refine ⟨20391851103106594995392063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217513078433137013284182005 20391851103106594995392063)
      ·
        refine ⟨30587776654659892493088095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391851103106594995392063 30587776654659892493088095)
        ·
          refine ⟨45881664981989838739632143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30587776654659892493088095 45881664981989838739632143)
          ·
            refine ⟨68822497472984758109448215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45881664981989838739632143 68822497472984758109448215)
            ·
              refine ⟨103233746209477137164172323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68822497472984758109448215 103233746209477137164172323)
              ·
                refine ⟨154850619314215705746258485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103233746209477137164172323 154850619314215705746258485)
                ·
                  refine ⟨14517245560707722413711733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154850619314215705746258485 14517245560707722413711733)
                  ·
                    refine ⟨1360991771316348976285475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14517245560707722413711733 1360991771316348976285475)
                    ·
                      rfl

theorem cell22_3975783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3975783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975783 prefixEnd_3975783 := by exact prefixLift 3975783
  have htrace : WordTrace (prefixWord ++ tailWord_3975783) baseStart_3975783 baseEnd_3975783 := by
    simpa [prefixWord, tailWord_3975783, baseEnd_3975783] using wordTrace_append hprefix tailTrace_3975783
  have hstable : (prefixWord ++ tailWord_3975783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975783).length < 2 ^ (prefixWord ++ tailWord_3975783).sum := by decide
  have hdescent : baseEnd_3975783 < baseStart_3975783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3975834 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_3975834 : Nat := 118140960795 + 3975834 * 2 ^ 59
def prefixEnd_3975834 : Nat := 4983230072969 + 3 ^ 40 * 3975834 * 2
def baseEnd_3975834 : Nat := 1361009229658601843260319

theorem tailTrace_3975834 : CollatzResearch.WordTrace tailWord_3975834 prefixEnd_3975834 1361009229658601843260319 := by
  unfold tailWord_3975834
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252644769559977808223639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 96673719385493274155263037 36252644769559977808223639)
  ·
    refine ⟨54378967154339966712335459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36252644769559977808223639 54378967154339966712335459)
    ·
      refine ⟨81568450731509950068503189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54378967154339966712335459 81568450731509950068503189)
      ·
        refine ⟨3823521128039528909461087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81568450731509950068503189 3823521128039528909461087)
        ·
          refine ⟨5735281692059293364191631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823521128039528909461087 5735281692059293364191631)
          ·
            refine ⟨8602922538088940046287447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735281692059293364191631 8602922538088940046287447)
            ·
              refine ⟨12904383807133410069431171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8602922538088940046287447 12904383807133410069431171)
              ·
                refine ⟨19356575710700115104146757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12904383807133410069431171 19356575710700115104146757)
                ·
                  refine ⟨3629357945756271582027517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19356575710700115104146757 3629357945756271582027517)
                  ·
                    refine ⟨1361009229658601843260319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3629357945756271582027517 1361009229658601843260319)
                    ·
                      rfl

theorem cell22_3975834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_3975834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3975834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3975834 prefixEnd_3975834 := by exact prefixLift 3975834
  have htrace : WordTrace (prefixWord ++ tailWord_3975834) baseStart_3975834 baseEnd_3975834 := by
    simpa [prefixWord, tailWord_3975834, baseEnd_3975834] using wordTrace_append hprefix tailTrace_3975834
  have hstable : (prefixWord ++ tailWord_3975834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3975834).length < 2 ^ (prefixWord ++ tailWord_3975834).sum := by decide
  have hdescent : baseEnd_3975834 < baseStart_3975834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3975834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
