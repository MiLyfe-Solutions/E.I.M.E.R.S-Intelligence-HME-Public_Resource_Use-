import V185TrunkScan23Chunk0997

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5909943 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_5909943 : Nat := 118140960795 + 5909943 * 2 ^ 59
def prefixEnd_5909943 : Nat := 4983230072969 + 3 ^ 40 * 5909943 * 2
def baseEnd_5909943 : Nat := 3034641399674676054533173

theorem tailTrace_5909943 : CollatzResearch.WordTrace tailWord_5909943 prefixEnd_5909943 3034641399674676054533173 := by
  unfold tailWord_5909943
  simp only [CollatzResearch.WordTrace]
  refine ⟨215553329628293323752014483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143702219752195549168009655 215553329628293323752014483)
  ·
    refine ⟨323329994442439985628021725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215553329628293323752014483 323329994442439985628021725)
    ·
      refine ⟨121248747915914994610508147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323329994442439985628021725 121248747915914994610508147)
      ·
        refine ⟨181873121873872491915762221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121248747915914994610508147 181873121873872491915762221)
        ·
          refine ⟨68202420702702184468410833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181873121873872491915762221 68202420702702184468410833)
          ·
            refine ⟨51151815527026638351308125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68202420702702184468410833 51151815527026638351308125)
            ·
              refine ⟨19181930822634989381740547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51151815527026638351308125 19181930822634989381740547)
              ·
                refine ⟨28772896233952484072610821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19181930822634989381740547 28772896233952484072610821)
                ·
                  refine ⟨5394918043866090763614529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28772896233952484072610821 5394918043866090763614529)
                  ·
                    refine ⟨4046188532899568072710897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5394918043866090763614529 4046188532899568072710897)
                    ·
                      refine ⟨3034641399674676054533173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046188532899568072710897 3034641399674676054533173)
                      ·
                        rfl

theorem cell23_5909943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_5909943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5909943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5909943 prefixEnd_5909943 := by exact prefixLift 5909943
  have htrace : WordTrace (prefixWord ++ tailWord_5909943) baseStart_5909943 baseEnd_5909943 := by
    simpa [prefixWord, tailWord_5909943, baseEnd_5909943] using wordTrace_append hprefix tailTrace_5909943
  have hstable : (prefixWord ++ tailWord_5909943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5909943).length < 2 ^ (prefixWord ++ tailWord_5909943).sum := by decide
  have hdescent : baseEnd_5909943 < baseStart_5909943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5909943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910006 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5910006 : Nat := 118140960795 + 5910006 * 2 ^ 59
def prefixEnd_5910006 : Nat := 4983230072969 + 3 ^ 40 * 5910006 * 2
def baseEnd_5910006 : Nat := 3034673748955909308045383

theorem tailTrace_5910006 : CollatzResearch.WordTrace tailWord_5910006 prefixEnd_5910006 3034673748955909308045383 := by
  unfold tailWord_5910006
  simp only [CollatzResearch.WordTrace]
  refine ⟨13472226714191567844472367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143703751618043390341038581 13472226714191567844472367)
  ·
    refine ⟨20208340071287351766708551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13472226714191567844472367 20208340071287351766708551)
    ·
      refine ⟨30312510106931027650062827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20208340071287351766708551 30312510106931027650062827)
      ·
        refine ⟨45468765160396541475094241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30312510106931027650062827 45468765160396541475094241)
        ·
          refine ⟨34101573870297406106320681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45468765160396541475094241 34101573870297406106320681)
          ·
            refine ⟨25576180402723054579740511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34101573870297406106320681 25576180402723054579740511)
            ·
              refine ⟨38364270604084581869610767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25576180402723054579740511 38364270604084581869610767)
              ·
                refine ⟨57546405906126872804416151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38364270604084581869610767 57546405906126872804416151)
                ·
                  refine ⟨86319608859190309206624227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57546405906126872804416151 86319608859190309206624227)
                  ·
                    refine ⟨129479413288785463809936341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86319608859190309206624227 129479413288785463809936341)
                    ·
                      refine ⟨3034673748955909308045383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129479413288785463809936341 3034673748955909308045383)
                      ·
                        rfl

theorem cell23_5910006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5910006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910006 prefixEnd_5910006 := by exact prefixLift 5910006
  have htrace : WordTrace (prefixWord ++ tailWord_5910006) baseStart_5910006 baseEnd_5910006 := by
    simpa [prefixWord, tailWord_5910006, baseEnd_5910006] using wordTrace_append hprefix tailTrace_5910006
  have hstable : (prefixWord ++ tailWord_5910006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910006).length < 2 ^ (prefixWord ++ tailWord_5910006).sum := by decide
  have hdescent : baseEnd_5910006 < baseStart_5910006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910066 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_5910066 : Nat := 118140960795 + 5910066 * 2 ^ 59
def prefixEnd_5910066 : Nat := 4983230072969 + 3 ^ 40 * 5910066 * 2
def baseEnd_5910066 : Nat := 3034704557795179073295107

theorem tailTrace_5910066 : CollatzResearch.WordTrace tailWord_5910066 prefixEnd_5910066 3034704557795179073295107 := by
  unfold tailWord_5910066
  simp only [CollatzResearch.WordTrace]
  refine ⟨53889453951711928939685513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143705210537898477172494701 53889453951711928939685513)
  ·
    refine ⟨40417090463783946704764135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53889453951711928939685513 40417090463783946704764135)
    ·
      refine ⟨60625635695675920057146203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40417090463783946704764135 60625635695675920057146203)
      ·
        refine ⟨90938453543513880085719305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60625635695675920057146203 90938453543513880085719305)
        ·
          refine ⟨68203840157635410064289479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90938453543513880085719305 68203840157635410064289479)
          ·
            refine ⟨102305760236453115096434219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68203840157635410064289479 102305760236453115096434219)
            ·
              refine ⟨153458640354679672644651329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102305760236453115096434219 153458640354679672644651329)
              ·
                refine ⟨115093980266009754483488497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153458640354679672644651329 115093980266009754483488497)
                ·
                  refine ⟨86320485199507315862616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115093980266009754483488497 86320485199507315862616373)
                  ·
                    refine ⟨8092545487453810862120285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86320485199507315862616373 8092545487453810862120285)
                    ·
                      refine ⟨3034704557795179073295107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8092545487453810862120285 3034704557795179073295107)
                      ·
                        rfl

theorem cell23_5910066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_5910066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910066 prefixEnd_5910066 := by exact prefixLift 5910066
  have htrace : WordTrace (prefixWord ++ tailWord_5910066) baseStart_5910066 baseEnd_5910066 := by
    simpa [prefixWord, tailWord_5910066, baseEnd_5910066] using wordTrace_append hprefix tailTrace_5910066
  have hstable : (prefixWord ++ tailWord_5910066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910066).length < 2 ^ (prefixWord ++ tailWord_5910066).sum := by decide
  have hdescent : baseEnd_5910066 < baseStart_5910066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910087 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_5910087 : Nat := 118140960795 + 5910087 * 2 ^ 59
def prefixEnd_5910087 : Nat := 4983230072969 + 3 ^ 40 * 5910087 * 2
def baseEnd_5910087 : Nat := 3034715340888923491132511

theorem tailTrace_5910087 : CollatzResearch.WordTrace tailWord_5910087 prefixEnd_5910087 3034715340888923491132511 := by
  unfold tailWord_5910087
  simp only [CollatzResearch.WordTrace]
  refine ⟨215558581739771636345256515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143705721159847757563504343 215558581739771636345256515)
  ·
    refine ⟨323337872609657454517884773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215558581739771636345256515 323337872609657454517884773)
    ·
      refine ⟨60625851114310772722103395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323337872609657454517884773 60625851114310772722103395)
      ·
        refine ⟨90938776671466159083155093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60625851114310772722103395 90938776671466159083155093)
        ·
          refine ⟨4262755156474976207022895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90938776671466159083155093 4262755156474976207022895)
          ·
            refine ⟨6394132734712464310534343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4262755156474976207022895 6394132734712464310534343)
            ·
              refine ⟨9591199102068696465801515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6394132734712464310534343 9591199102068696465801515)
              ·
                refine ⟨14386798653103044698702273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9591199102068696465801515 14386798653103044698702273)
                ·
                  refine ⟨10790098989827283524026705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14386798653103044698702273 10790098989827283524026705)
                  ·
                    refine ⟨8092574242370462643020029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10790098989827283524026705 8092574242370462643020029)
                    ·
                      refine ⟨3034715340888923491132511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8092574242370462643020029 3034715340888923491132511)
                      ·
                        rfl

theorem cell23_5910087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_5910087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910087 prefixEnd_5910087 := by exact prefixLift 5910087
  have htrace : WordTrace (prefixWord ++ tailWord_5910087) baseStart_5910087 baseEnd_5910087 := by
    simpa [prefixWord, tailWord_5910087, baseEnd_5910087] using wordTrace_append hprefix tailTrace_5910087
  have hstable : (prefixWord ++ tailWord_5910087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910087).length < 2 ^ (prefixWord ++ tailWord_5910087).sum := by decide
  have hdescent : baseEnd_5910087 < baseStart_5910087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910103 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 1, 5]
def baseStart_5910103 : Nat := 118140960795 + 5910103 * 2 ^ 59
def prefixEnd_5910103 : Nat := 4983230072969 + 3 ^ 40 * 5910103 * 2
def baseEnd_5910103 : Nat := 1011574518859798476177479

theorem tailTrace_5910103 : CollatzResearch.WordTrace tailWord_5910103 prefixEnd_5910103 1011574518859798476177479 := by
  unfold tailWord_5910103
  simp only [CollatzResearch.WordTrace]
  refine ⟨215559165307713671077838963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143706110205142447385225975 215559165307713671077838963)
  ·
    refine ⟨323338747961570506616758445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215559165307713671077838963 323338747961570506616758445)
    ·
      refine ⟨121252030485588939981284417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323338747961570506616758445 121252030485588939981284417)
      ·
        refine ⟨90939022864191704985963313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121252030485588939981284417 90939022864191704985963313)
        ·
          refine ⟨68204267148143778739472485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90939022864191704985963313 68204267148143778739472485)
          ·
            refine ⟨12788300090276958513651091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68204267148143778739472485 12788300090276958513651091)
            ·
              refine ⟨19182450135415437770476637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12788300090276958513651091 19182450135415437770476637)
              ·
                refine ⟨7193418800780789163928739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19182450135415437770476637 7193418800780789163928739)
                ·
                  refine ⟨10790128201171183745893109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7193418800780789163928739 10790128201171183745893109)
                  ·
                    refine ⟨1011574518859798476177479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10790128201171183745893109 1011574518859798476177479)
                    ·
                      rfl

theorem cell23_5910103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_5910103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910103 prefixEnd_5910103 := by exact prefixLift 5910103
  have htrace : WordTrace (prefixWord ++ tailWord_5910103) baseStart_5910103 baseEnd_5910103 := by
    simpa [prefixWord, tailWord_5910103, baseEnd_5910103] using wordTrace_append hprefix tailTrace_5910103
  have hstable : (prefixWord ++ tailWord_5910103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910103).length < 2 ^ (prefixWord ++ tailWord_5910103).sum := by decide
  have hdescent : baseEnd_5910103 < baseStart_5910103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910117 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 1, 1, 3]
def baseStart_5910117 : Nat := 118140960795 + 5910117 * 2 ^ 59
def prefixEnd_5910117 : Nat := 4983230072969 + 3 ^ 40 * 5910117 * 2
def baseEnd_5910117 : Nat := 3034730745308558373757373

theorem tailTrace_5910117 : CollatzResearch.WordTrace tailWord_5910117 prefixEnd_5910117 3034730745308558373757373 := by
  unfold tailWord_5910117
  simp only [CollatzResearch.WordTrace]
  refine ⟨215559675929662951468848605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143706450619775300979232403 215559675929662951468848605)
  ·
    refine ⟨80834878473623606800818227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215559675929662951468848605 80834878473623606800818227)
    ·
      refine ⟨121252317710435410201227341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80834878473623606800818227 121252317710435410201227341)
      ·
        refine ⟨45469619141413278825460253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121252317710435410201227341 45469619141413278825460253)
        ·
          refine ⟨17051107178029979559547595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45469619141413278825460253 17051107178029979559547595)
          ·
            refine ⟨25576660767044969339321393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17051107178029979559547595 25576660767044969339321393)
            ·
              refine ⟨19182495575283727004491045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25576660767044969339321393 19182495575283727004491045)
              ·
                refine ⟨3596717920365698813342071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19182495575283727004491045 3596717920365698813342071)
                ·
                  refine ⟨5395076880548548220013107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596717920365698813342071 5395076880548548220013107)
                  ·
                    refine ⟨8092615320822822330019661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395076880548548220013107 8092615320822822330019661)
                    ·
                      refine ⟨3034730745308558373757373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8092615320822822330019661 3034730745308558373757373)
                      ·
                        rfl

theorem cell23_5910117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_5910117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910117 prefixEnd_5910117 := by exact prefixLift 5910117
  have htrace : WordTrace (prefixWord ++ tailWord_5910117) baseStart_5910117 baseEnd_5910117 := by
    simpa [prefixWord, tailWord_5910117, baseEnd_5910117] using wordTrace_append hprefix tailTrace_5910117
  have hstable : (prefixWord ++ tailWord_5910117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910117).length < 2 ^ (prefixWord ++ tailWord_5910117).sum := by decide
  have hdescent : baseEnd_5910117 < baseStart_5910117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910174 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5910174 : Nat := 118140960795 + 5910174 * 2 ^ 59
def prefixEnd_5910174 : Nat := 4983230072969 + 3 ^ 40 * 5910174 * 2
def baseEnd_5910174 : Nat := 3034760013705864650744611

theorem tailTrace_5910174 : CollatzResearch.WordTrace tailWord_5910174 prefixEnd_5910174 3034760013705864650744611 := by
  unfold tailWord_5910174
  simp only [CollatzResearch.WordTrace]
  refine ⟨26945219361307056275459197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143707836593637633469115717 26945219361307056275459197)
  ·
    refine ⟨10104457260490146103297199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26945219361307056275459197 10104457260490146103297199)
    ·
      refine ⟨15156685890735219154945799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10104457260490146103297199 15156685890735219154945799)
      ·
        refine ⟨22735028836102828732418699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15156685890735219154945799 22735028836102828732418699)
        ·
          refine ⟨34102543254154243098628049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22735028836102828732418699 34102543254154243098628049)
          ·
            refine ⟨25576907440615682323971037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34102543254154243098628049 25576907440615682323971037)
            ·
              refine ⟨9591340290230880871489139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25576907440615682323971037 9591340290230880871489139)
              ·
                refine ⟨14387010435346321307233709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9591340290230880871489139 14387010435346321307233709)
                ·
                  refine ⟨5395128913254870490212641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14387010435346321307233709 5395128913254870490212641)
                  ·
                    refine ⟨4046346684941152867659481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395128913254870490212641 4046346684941152867659481)
                    ·
                      refine ⟨3034760013705864650744611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046346684941152867659481 3034760013705864650744611)
                      ·
                        rfl

theorem cell23_5910174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5910174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910174 prefixEnd_5910174 := by exact prefixLift 5910174
  have htrace : WordTrace (prefixWord ++ tailWord_5910174) baseStart_5910174 baseEnd_5910174 := by
    simpa [prefixWord, tailWord_5910174, baseEnd_5910174] using wordTrace_append hprefix tailTrace_5910174
  have hstable : (prefixWord ++ tailWord_5910174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910174).length < 2 ^ (prefixWord ++ tailWord_5910174).sum := by decide
  have hdescent : baseEnd_5910174 < baseStart_5910174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910233 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 3]
def baseStart_5910233 : Nat := 118140960795 + 5910233 * 2 ^ 59
def prefixEnd_5910233 : Nat := 4983230072969 + 3 ^ 40 * 5910233 * 2
def baseEnd_5910233 : Nat := 3034790309064479919906839

theorem tailTrace_5910233 : CollatzResearch.WordTrace tailWord_5910233 prefixEnd_5910233 3034790309064479919906839 := by
  unfold tailWord_5910233
  simp only [CollatzResearch.WordTrace]
  refine ⟨215563906797242703280071353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143709271198161802186714235 215563906797242703280071353)
  ·
    refine ⟨161672930097932027460053515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215563906797242703280071353 161672930097932027460053515)
    ·
      refine ⟨242509395146898041190080273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161672930097932027460053515 242509395146898041190080273)
      ·
        refine ⟨181882046360173530892560205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242509395146898041190080273 181882046360173530892560205)
        ·
          refine ⟨68205767385065074084710077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181882046360173530892560205 68205767385065074084710077)
          ·
            refine ⟨25577162769399402781766279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68205767385065074084710077 25577162769399402781766279)
            ·
              refine ⟨38365744154099104172649419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25577162769399402781766279 38365744154099104172649419)
              ·
                refine ⟨57548616231148656258974129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38365744154099104172649419 57548616231148656258974129)
                ·
                  refine ⟨43161462173361492194230597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57548616231148656258974129 43161462173361492194230597)
                  ·
                    refine ⟨8092774157505279786418237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43161462173361492194230597 8092774157505279786418237)
                    ·
                      refine ⟨3034790309064479919906839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8092774157505279786418237 3034790309064479919906839)
                      ·
                        rfl

theorem cell23_5910233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_5910233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910233 prefixEnd_5910233 := by exact prefixLift 5910233
  have htrace : WordTrace (prefixWord ++ tailWord_5910233) baseStart_5910233 baseEnd_5910233 := by
    simpa [prefixWord, tailWord_5910233, baseEnd_5910233] using wordTrace_append hprefix tailTrace_5910233
  have hstable : (prefixWord ++ tailWord_5910233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910233).length < 2 ^ (prefixWord ++ tailWord_5910233).sum := by decide
  have hdescent : baseEnd_5910233 < baseStart_5910233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910253 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 9]
def baseStart_5910253 : Nat := 118140960795 + 5910253 * 2 ^ 59
def prefixEnd_5910253 : Nat := 4983230072969 + 3 ^ 40 * 5910253 * 2
def baseEnd_5910253 : Nat := 337200064297507760184083

theorem tailTrace_5910253 : CollatzResearch.WordTrace tailWord_5910253 prefixEnd_5910253 337200064297507760184083 := by
  unfold tailWord_5910253
  simp only [CollatzResearch.WordTrace]
  refine ⟨215564636257170246695799413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143709757504780164463866275 215564636257170246695799413)
  ·
    refine ⟨20209184649109710627731195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215564636257170246695799413 20209184649109710627731195)
    ·
      refine ⟨30313776973664565941596793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20209184649109710627731195 30313776973664565941596793)
      ·
        refine ⟨22735332730248424456197595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30313776973664565941596793 22735332730248424456197595)
        ·
          refine ⟨34102999095372636684296393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22735332730248424456197595 34102999095372636684296393)
          ·
            refine ⟨25577249321529477513222295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34102999095372636684296393 25577249321529477513222295)
            ·
              refine ⟨38365873982294216269833443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25577249321529477513222295 38365873982294216269833443)
              ·
                refine ⟨57548810973441324404750165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38365873982294216269833443 57548810973441324404750165)
                ·
                  refine ⟨337200064297507760184083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57548810973441324404750165 337200064297507760184083)
                  ·
                    rfl

theorem cell23_5910253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_5910253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910253 prefixEnd_5910253 := by exact prefixLift 5910253
  have htrace : WordTrace (prefixWord ++ tailWord_5910253) baseStart_5910253 baseEnd_5910253 := by
    simpa [prefixWord, tailWord_5910253, baseEnd_5910253] using wordTrace_append hprefix tailTrace_5910253
  have hstable : (prefixWord ++ tailWord_5910253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910253).length < 2 ^ (prefixWord ++ tailWord_5910253).sum := by decide
  have hdescent : baseEnd_5910253 < baseStart_5910253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910283 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 2, 5]
def baseStart_5910283 : Nat := 118140960795 + 5910283 * 2 ^ 59
def prefixEnd_5910283 : Nat := 4983230072969 + 3 ^ 40 * 5910283 * 2
def baseEnd_5910283 : Nat := 1011605327699068241427203

theorem tailTrace_5910283 : CollatzResearch.WordTrace tailWord_5910283 prefixEnd_5910283 1011605327699068241427203 := by
  unfold tailWord_5910283
  simp only [CollatzResearch.WordTrace]
  refine ⟨215565730447061561819391503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143710486964707707879594335 215565730447061561819391503)
  ·
    refine ⟨323348595670592342729087255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215565730447061561819391503 323348595670592342729087255)
    ·
      refine ⟨485022893505888514093630883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323348595670592342729087255 485022893505888514093630883)
      ·
        refine ⟨727534340258832771140446325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485022893505888514093630883 727534340258832771140446325)
        ·
          refine ⟨68206344399265572294416843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 727534340258832771140446325 68206344399265572294416843)
          ·
            refine ⟨102309516598898358441625265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68206344399265572294416843 102309516598898358441625265)
            ·
              refine ⟨76732137449173768831218949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102309516598898358441625265 76732137449173768831218949)
              ·
                refine ⟨14387275771720081655853553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76732137449173768831218949 14387275771720081655853553)
                ·
                  refine ⟨10790456828790061241890165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14387275771720081655853553 10790456828790061241890165)
                  ·
                    refine ⟨1011605327699068241427203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10790456828790061241890165 1011605327699068241427203)
                    ·
                      rfl

theorem cell23_5910283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 2, 5].length) (baseStart_5910283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910283 prefixEnd_5910283 := by exact prefixLift 5910283
  have htrace : WordTrace (prefixWord ++ tailWord_5910283) baseStart_5910283 baseEnd_5910283 := by
    simpa [prefixWord, tailWord_5910283, baseEnd_5910283] using wordTrace_append hprefix tailTrace_5910283
  have hstable : (prefixWord ++ tailWord_5910283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910283).length < 2 ^ (prefixWord ++ tailWord_5910283).sum := by decide
  have hdescent : baseEnd_5910283 < baseStart_5910283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910303 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_5910303 : Nat := 118140960795 + 5910303 * 2 ^ 59
def prefixEnd_5910303 : Nat := 4983230072969 + 3 ^ 40 * 5910303 * 2
def baseEnd_5910303 : Nat := 3034826252710294646031517

theorem tailTrace_5910303 : CollatzResearch.WordTrace tailWord_5910303 prefixEnd_5910303 3034826252710294646031517 := by
  unfold tailWord_5910303
  simp only [CollatzResearch.WordTrace]
  refine ⟨215566459906989105235119563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143710973271326070156746375 215566459906989105235119563)
  ·
    refine ⟨323349689860483657852679345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215566459906989105235119563 323349689860483657852679345)
    ·
      refine ⟨242512267395362743389509509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323349689860483657852679345 242512267395362743389509509)
      ·
        refine ⟨45471050136630514385533033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242512267395362743389509509 45471050136630514385533033)
        ·
          refine ⟨34103287602472885789149775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45471050136630514385533033 34103287602472885789149775)
          ·
            refine ⟨51154931403709328683724663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34103287602472885789149775 51154931403709328683724663)
            ·
              refine ⟨76732397105563993025586995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51154931403709328683724663 76732397105563993025586995)
              ·
                refine ⟨115098595658345989538380493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76732397105563993025586995 115098595658345989538380493)
                ·
                  refine ⟨43161973371879746076892685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115098595658345989538380493 43161973371879746076892685)
                  ·
                    refine ⟨16185740014454904778834757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43161973371879746076892685 16185740014454904778834757)
                    ·
                      refine ⟨3034826252710294646031517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16185740014454904778834757 3034826252710294646031517)
                      ·
                        rfl

theorem cell23_5910303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_5910303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910303 prefixEnd_5910303 := by exact prefixLift 5910303
  have htrace : WordTrace (prefixWord ++ tailWord_5910303) baseStart_5910303 baseEnd_5910303 := by
    simpa [prefixWord, tailWord_5910303, baseEnd_5910303] using wordTrace_append hprefix tailTrace_5910303
  have hstable : (prefixWord ++ tailWord_5910303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910303).length < 2 ^ (prefixWord ++ tailWord_5910303).sum := by decide
  have hdescent : baseEnd_5910303 < baseStart_5910303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910343 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 8]
def baseStart_5910343 : Nat := 118140960795 + 5910343 * 2 ^ 59
def prefixEnd_5910343 : Nat := 4983230072969 + 3 ^ 40 * 5910343 * 2
def baseEnd_5910343 : Nat := 337205199104052721059037

theorem tailTrace_5910343 : CollatzResearch.WordTrace tailWord_5910343 prefixEnd_5910343 337205199104052721059037 := by
  unfold tailWord_5910343
  simp only [CollatzResearch.WordTrace]
  refine ⟨215567918826844192066575683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143711945884562794711050455 215567918826844192066575683)
  ·
    refine ⟨323351878240266288099863525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215567918826844192066575683 323351878240266288099863525)
    ·
      refine ⟨60628477170049929018724411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323351878240266288099863525 60628477170049929018724411)
      ·
        refine ⟨90942715755074893528086617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60628477170049929018724411 90942715755074893528086617)
        ·
          refine ⟨68207036816306170146064963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90942715755074893528086617 68207036816306170146064963)
          ·
            refine ⟨102310555224459255219097445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68207036816306170146064963 102310555224459255219097445)
            ·
              refine ⟨19183229104586110353580771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102310555224459255219097445 19183229104586110353580771)
              ·
                refine ⟨28774843656879165530371157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19183229104586110353580771 28774843656879165530371157)
                ·
                  refine ⟨337205199104052721059037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28774843656879165530371157 337205199104052721059037)
                  ·
                    rfl

theorem cell23_5910343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 8].length) (baseStart_5910343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910343 prefixEnd_5910343 := by exact prefixLift 5910343
  have htrace : WordTrace (prefixWord ++ tailWord_5910343) baseStart_5910343 baseEnd_5910343 := by
    simpa [prefixWord, tailWord_5910343, baseEnd_5910343] using wordTrace_append hprefix tailTrace_5910343
  have hstable : (prefixWord ++ tailWord_5910343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910343).length < 2 ^ (prefixWord ++ tailWord_5910343).sum := by decide
  have hdescent : baseEnd_5910343 < baseStart_5910343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910398 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5910398 : Nat := 118140960795 + 5910398 * 2 ^ 59
def prefixEnd_5910398 : Nat := 4983230072969 + 3 ^ 40 * 5910398 * 2
def baseEnd_5910398 : Nat := 1011625011124157258114527

theorem tailTrace_5910398 : CollatzResearch.WordTrace tailWord_5910398 prefixEnd_5910398 1011625011124157258114527 := by
  unfold tailWord_5910398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26946240605205617057478481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143713283227763290973218565 26946240605205617057478481)
  ·
    refine ⟨20209680453904212793108861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26946240605205617057478481 20209680453904212793108861)
    ·
      refine ⟨7578630170214079797415823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20209680453904212793108861 7578630170214079797415823)
      ·
        refine ⟨11367945255321119696123735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578630170214079797415823 11367945255321119696123735)
        ·
          refine ⟨17051917882981679544185603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11367945255321119696123735 17051917882981679544185603)
          ·
            refine ⟨25577876824472519316278405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17051917882981679544185603 25577876824472519316278405)
            ·
              refine ⟨4795851904588597371802201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25577876824472519316278405 4795851904588597371802201)
              ·
                refine ⟨3596888928441448028851651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4795851904588597371802201 3596888928441448028851651)
                ·
                  refine ⟨5395333392662172043277477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3596888928441448028851651 5395333392662172043277477)
                  ·
                    refine ⟨1011625011124157258114527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395333392662172043277477 1011625011124157258114527)
                    ·
                      rfl

theorem cell23_5910398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5910398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910398 prefixEnd_5910398 := by exact prefixLift 5910398
  have htrace : WordTrace (prefixWord ++ tailWord_5910398) baseStart_5910398 baseEnd_5910398 := by
    simpa [prefixWord, tailWord_5910398, baseEnd_5910398] using wordTrace_append hprefix tailTrace_5910398
  have hstable : (prefixWord ++ tailWord_5910398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910398).length < 2 ^ (prefixWord ++ tailWord_5910398).sum := by decide
  have hdescent : baseEnd_5910398 < baseStart_5910398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910431 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 2, 3, 2]
def baseStart_5910431 : Nat := 118140960795 + 5910431 * 2 ^ 59
def prefixEnd_5910431 : Nat := 4983230072969 + 3 ^ 40 * 5910431 * 2
def baseEnd_5910431 : Nat := 3034891978234070145230929

theorem tailTrace_5910431 : CollatzResearch.WordTrace tailWord_5910431 prefixEnd_5910431 3034891978234070145230929 := by
  unfold tailWord_5910431
  simp only [CollatzResearch.WordTrace]
  refine ⟨215571128450525383095779147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143714085633683588730519431 215571128450525383095779147)
  ·
    refine ⟨323356692675788074643668721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215571128450525383095779147 323356692675788074643668721)
    ·
      refine ⟨242517519506841055982751541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323356692675788074643668721 242517519506841055982751541)
      ·
        refine ⟨22736017453766348998382957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242517519506841055982751541 22736017453766348998382957)
        ·
          refine ⟨8526006545162380874393609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22736017453766348998382957 8526006545162380874393609)
          ·
            refine ⟨6394504908871785655795207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8526006545162380874393609 6394504908871785655795207)
            ·
              refine ⟨9591757363307678483692811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6394504908871785655795207 9591757363307678483692811)
              ·
                refine ⟨14387636044961517725539217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9591757363307678483692811 14387636044961517725539217)
                ·
                  refine ⟨10790727033721138294154413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14387636044961517725539217 10790727033721138294154413)
                  ·
                    refine ⟨4046522637645426860307905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10790727033721138294154413 4046522637645426860307905)
                    ·
                      refine ⟨3034891978234070145230929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046522637645426860307905 3034891978234070145230929)
                      ·
                        rfl

theorem cell23_5910431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_5910431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910431 prefixEnd_5910431 := by exact prefixLift 5910431
  have htrace : WordTrace (prefixWord ++ tailWord_5910431) baseStart_5910431 baseEnd_5910431 := by
    simpa [prefixWord, tailWord_5910431, baseEnd_5910431] using wordTrace_append hprefix tailTrace_5910431
  have hstable : (prefixWord ++ tailWord_5910431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910431).length < 2 ^ (prefixWord ++ tailWord_5910431).sum := by decide
  have hdescent : baseEnd_5910431 < baseStart_5910431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910447 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_5910447 : Nat := 118140960795 + 5910447 * 2 ^ 59
def prefixEnd_5910447 : Nat := 4983230072969 + 3 ^ 40 * 5910447 * 2
def baseEnd_5910447 : Nat := 3034900193924542082630855

theorem tailTrace_5910447 : CollatzResearch.WordTrace tailWord_5910447 prefixEnd_5910447 3034900193924542082630855 := by
  unfold tailWord_5910447
  simp only [CollatzResearch.WordTrace]
  refine ⟨215571712018467417828361595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143714474678978278552241063 215571712018467417828361595)
  ·
    refine ⟨323357568027701126742542393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215571712018467417828361595 323357568027701126742542393)
    ·
      refine ⟨242518176020775845056906795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323357568027701126742542393 242518176020775845056906795)
      ·
        refine ⟨363777264031163767585360193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242518176020775845056906795 363777264031163767585360193)
        ·
          refine ⟨272832948023372825689020145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363777264031163767585360193 272832948023372825689020145)
          ·
            refine ⟨204624711017529619266765109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272832948023372825689020145 204624711017529619266765109)
            ·
              refine ⟨19183566657893401806259229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204624711017529619266765109 19183566657893401806259229)
              ·
                refine ⟨7193837496710025677347211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19183566657893401806259229 7193837496710025677347211)
                ·
                  refine ⟨10790756245065038516020817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7193837496710025677347211 10790756245065038516020817)
                  ·
                    refine ⟨8093067183798778887015613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10790756245065038516020817 8093067183798778887015613)
                    ·
                      refine ⟨3034900193924542082630855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093067183798778887015613 3034900193924542082630855)
                      ·
                        rfl

theorem cell23_5910447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_5910447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910447 prefixEnd_5910447 := by exact prefixLift 5910447
  have htrace : WordTrace (prefixWord ++ tailWord_5910447) baseStart_5910447 baseEnd_5910447 := by
    simpa [prefixWord, tailWord_5910447, baseEnd_5910447] using wordTrace_append hprefix tailTrace_5910447
  have hstable : (prefixWord ++ tailWord_5910447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910447).length < 2 ^ (prefixWord ++ tailWord_5910447).sum := by decide
  have hdescent : baseEnd_5910447 < baseStart_5910447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910461 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_5910461 : Nat := 118140960795 + 5910461 * 2 ^ 59
def prefixEnd_5910461 : Nat := 4983230072969 + 3 ^ 40 * 5910461 * 2
def baseEnd_5910461 : Nat := 3034907382653705027855791

theorem tailTrace_5910461 : CollatzResearch.WordTrace tailWord_5910461 prefixEnd_5910461 3034907382653705027855791 := by
  unfold tailWord_5910461
  simp only [CollatzResearch.WordTrace]
  refine ⟨215572222640416698219371237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143714815093611132146247491 215572222640416698219371237)
  ·
    refine ⟨40419791745078130916132107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215572222640416698219371237 40419791745078130916132107)
    ·
      refine ⟨60629687617617196374198161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40419791745078130916132107 60629687617617196374198161)
      ·
        refine ⟨45472265713212897280648621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60629687617617196374198161 45472265713212897280648621)
        ·
          refine ⟨17052099642454836480243233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45472265713212897280648621 17052099642454836480243233)
          ·
            refine ⟨12789074731841127360182425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17052099642454836480243233 12789074731841127360182425)
            ·
              refine ⟨9591806048880845520136819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12789074731841127360182425 9591806048880845520136819)
              ·
                refine ⟨14387709073321268280205229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9591806048880845520136819 14387709073321268280205229)
                ·
                  refine ⟨5395390902495475605076961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14387709073321268280205229 5395390902495475605076961)
                  ·
                    refine ⟨4046543176871606703807721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395390902495475605076961 4046543176871606703807721)
                    ·
                      refine ⟨3034907382653705027855791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046543176871606703807721 3034907382653705027855791)
                      ·
                        rfl

theorem cell23_5910461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_5910461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910461 prefixEnd_5910461 := by exact prefixLift 5910461
  have htrace : WordTrace (prefixWord ++ tailWord_5910461) baseStart_5910461 baseEnd_5910461 := by
    simpa [prefixWord, tailWord_5910461, baseEnd_5910461] using wordTrace_append hprefix tailTrace_5910461
  have hstable : (prefixWord ++ tailWord_5910461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910461).length < 2 ^ (prefixWord ++ tailWord_5910461).sum := by decide
  have hdescent : baseEnd_5910461 < baseStart_5910461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910538 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_5910538 : Nat := 118140960795 + 5910538 * 2 ^ 59
def prefixEnd_5910538 : Nat := 4983230072969 + 3 ^ 40 * 5910538 * 2
def baseEnd_5910538 : Nat := 3034946920664101226592937

theorem tailTrace_5910538 : CollatzResearch.WordTrace tailWord_5910538 prefixEnd_5910538 3034946920664101226592937 := by
  unfold tailWord_5910538
  simp only [CollatzResearch.WordTrace]
  refine ⟨53893757765284435092481067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143716687374091826913282845 53893757765284435092481067)
  ·
    refine ⟨80840636647926652638721601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53893757765284435092481067 80840636647926652638721601)
    ·
      refine ⟨60630477485944989479041201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80840636647926652638721601 60630477485944989479041201)
      ·
        refine ⟨45472858114458742109280901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60630477485944989479041201 45472858114458742109280901)
        ·
          refine ⟨8526160896461014145490169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45472858114458742109280901 8526160896461014145490169)
          ·
            refine ⟨6394620672345760609117627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8526160896461014145490169 6394620672345760609117627)
            ·
              refine ⟨9591931008518640913676441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6394620672345760609117627 9591931008518640913676441)
              ·
                refine ⟨7193948256388980685257331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9591931008518640913676441 7193948256388980685257331)
                ·
                  refine ⟨10790922384583471027885997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7193948256388980685257331 10790922384583471027885997)
                  ·
                    refine ⟨4046595894218801635457249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10790922384583471027885997 4046595894218801635457249)
                    ·
                      refine ⟨3034946920664101226592937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046595894218801635457249 3034946920664101226592937)
                      ·
                        rfl

theorem cell23_5910538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_5910538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910538 prefixEnd_5910538 := by exact prefixLift 5910538
  have htrace : WordTrace (prefixWord ++ tailWord_5910538) baseStart_5910538 baseEnd_5910538 := by
    simpa [prefixWord, tailWord_5910538, baseEnd_5910538] using wordTrace_append hprefix tailTrace_5910538
  have hstable : (prefixWord ++ tailWord_5910538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910538).length < 2 ^ (prefixWord ++ tailWord_5910538).sum := by decide
  have hdescent : baseEnd_5910538 < baseStart_5910538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910540 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 9]
def baseStart_5910540 : Nat := 118140960795 + 5910540 * 2 ^ 59
def prefixEnd_5910540 : Nat := 4983230072969 + 3 ^ 40 * 5910540 * 2
def baseEnd_5910540 : Nat := 337216438625045579863103

theorem tailTrace_5910540 : CollatzResearch.WordTrace tailWord_5910540 prefixEnd_5910540 337216438625045579863103 := by
  unfold tailWord_5910540
  simp only [CollatzResearch.WordTrace]
  refine ⟨107787552003565247355748537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143716736004753663140998049 107787552003565247355748537)
  ·
    refine ⟨80840664002673935516811403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107787552003565247355748537 80840664002673935516811403)
    ·
      refine ⟨121260996004010903275217105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80840664002673935516811403 121260996004010903275217105)
      ·
        refine ⟨90945747003008177456412829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121260996004010903275217105 90945747003008177456412829)
        ·
          refine ⟨34104655126128066546154811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90945747003008177456412829 34104655126128066546154811)
          ·
            refine ⟨51156982689192099819232217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34104655126128066546154811 51156982689192099819232217)
            ·
              refine ⟨38367737016894074864424163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51156982689192099819232217 38367737016894074864424163)
              ·
                refine ⟨57551605525341112296636245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38367737016894074864424163 57551605525341112296636245)
                ·
                  refine ⟨337216438625045579863103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57551605525341112296636245 337216438625045579863103)
                  ·
                    rfl

theorem cell23_5910540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_5910540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910540 prefixEnd_5910540 := by exact prefixLift 5910540
  have htrace : WordTrace (prefixWord ++ tailWord_5910540) baseStart_5910540 baseEnd_5910540 := by
    simpa [prefixWord, tailWord_5910540, baseEnd_5910540] using wordTrace_append hprefix tailTrace_5910540
  have hstable : (prefixWord ++ tailWord_5910540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910540).length < 2 ^ (prefixWord ++ tailWord_5910540).sum := by decide
  have hdescent : baseEnd_5910540 < baseStart_5910540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910551 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5910551 : Nat := 118140960795 + 5910551 * 2 ^ 59
def prefixEnd_5910551 : Nat := 4983230072969 + 3 ^ 40 * 5910551 * 2
def baseEnd_5910551 : Nat := 3034953595912609675730377

theorem tailTrace_5910551 : CollatzResearch.WordTrace tailWord_5910551 prefixEnd_5910551 3034953595912609675730377 := by
  unfold tailWord_5910551
  simp only [CollatzResearch.WordTrace]
  refine ⟨215575505210090643590147507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143717003473393762393431671 215575505210090643590147507)
  ·
    refine ⟨323363257815135965385221261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215575505210090643590147507 323363257815135965385221261)
    ·
      refine ⟨121261221680675987019457973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323363257815135965385221261 121261221680675987019457973)
      ·
        refine ⟨11368239532563373783074185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121261221680675987019457973 11368239532563373783074185)
        ·
          refine ⟨8526179649422530337305639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11368239532563373783074185 8526179649422530337305639)
          ·
            refine ⟨12789269474133795505958459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526179649422530337305639 12789269474133795505958459)
            ·
              refine ⟨19183904211200693258937689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12789269474133795505958459 19183904211200693258937689)
              ·
                refine ⟨14387928158400519944203267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19183904211200693258937689 14387928158400519944203267)
                ·
                  refine ⟨21581892237600779916304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14387928158400519944203267 21581892237600779916304901)
                  ·
                    refine ⟨4046604794550146234307169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21581892237600779916304901 4046604794550146234307169)
                    ·
                      refine ⟨3034953595912609675730377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046604794550146234307169 3034953595912609675730377)
                      ·
                        rfl

theorem cell23_5910551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5910551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910551 prefixEnd_5910551 := by exact prefixLift 5910551
  have htrace : WordTrace (prefixWord ++ tailWord_5910551) baseStart_5910551 baseEnd_5910551 := by
    simpa [prefixWord, tailWord_5910551, baseEnd_5910551] using wordTrace_append hprefix tailTrace_5910551
  have hstable : (prefixWord ++ tailWord_5910551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910551).length < 2 ^ (prefixWord ++ tailWord_5910551).sum := by decide
  have hdescent : baseEnd_5910551 < baseStart_5910551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910584 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_5910584 : Nat := 118140960795 + 5910584 * 2 ^ 59
def prefixEnd_5910584 : Nat := 4983230072969 + 3 ^ 40 * 5910584 * 2
def baseEnd_5910584 : Nat := 3034970540774208046617725

theorem tailTrace_5910584 : CollatzResearch.WordTrace tailWord_5910584 prefixEnd_5910584 3034970540774208046617725 := by
  unfold tailWord_5910584
  simp only [CollatzResearch.WordTrace]
  refine ⟨107788354409485545113049403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143717805879314060150732537 107788354409485545113049403)
  ·
    refine ⟨161682531614228317669574105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107788354409485545113049403 161682531614228317669574105)
    ·
      refine ⟨121261898710671238252180579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161682531614228317669574105 121261898710671238252180579)
      ·
        refine ⟨181892848066006857378270869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121261898710671238252180579 181892848066006857378270869)
        ·
          refine ⟨8526227253094071439606447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 181892848066006857378270869 8526227253094071439606447)
          ·
            refine ⟨12789340879641107159409671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526227253094071439606447 12789340879641107159409671)
            ·
              refine ⟨19184011319461660739114507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12789340879641107159409671 19184011319461660739114507)
              ·
                refine ⟨28776016979192491108671761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19184011319461660739114507 28776016979192491108671761)
                ·
                  refine ⟨21582012734394368331503821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28776016979192491108671761 21582012734394368331503821)
                  ·
                    refine ⟨8093254775397888124313933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21582012734394368331503821 8093254775397888124313933)
                    ·
                      refine ⟨3034970540774208046617725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093254775397888124313933 3034970540774208046617725)
                      ·
                        rfl

theorem cell23_5910584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_5910584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910584 prefixEnd_5910584 := by exact prefixLift 5910584
  have htrace : WordTrace (prefixWord ++ tailWord_5910584) baseStart_5910584 baseEnd_5910584 := by
    simpa [prefixWord, tailWord_5910584, baseEnd_5910584] using wordTrace_append hprefix tailTrace_5910584
  have hstable : (prefixWord ++ tailWord_5910584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910584).length < 2 ^ (prefixWord ++ tailWord_5910584).sum := by decide
  have hdescent : baseEnd_5910584 < baseStart_5910584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910600 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_5910600 : Nat := 118140960795 + 5910600 * 2 ^ 59
def prefixEnd_5910600 : Nat := 4983230072969 + 3 ^ 40 * 5910600 * 2
def baseEnd_5910600 : Nat := 1011659585488226661339217

theorem tailTrace_5910600 : CollatzResearch.WordTrace tailWord_5910600 prefixEnd_5910600 1011659585488226661339217 := by
  unfold tailWord_5910600
  simp only [CollatzResearch.WordTrace]
  refine ⟨107788646193456562479340627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143718194924608749972454169 107788646193456562479340627)
  ·
    refine ⟨161682969290184843719010941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107788646193456562479340627 161682969290184843719010941)
    ·
      refine ⟨60631113483819316394629103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161682969290184843719010941 60631113483819316394629103)
      ·
        refine ⟨90946670225728974591943655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60631113483819316394629103 90946670225728974591943655)
        ·
          refine ⟨136420005338593461887915483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90946670225728974591943655 136420005338593461887915483)
          ·
            refine ⟨204630008007890192831873225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136420005338593461887915483 204630008007890192831873225)
            ·
              refine ⟨153472506005917644623904919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204630008007890192831873225 153472506005917644623904919)
              ·
                refine ⟨230208759008876466935857379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153472506005917644623904919 230208759008876466935857379)
                ·
                  refine ⟨345313138513314700403786069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230208759008876466935857379 345313138513314700403786069)
                  ·
                    refine ⟨1011659585488226661339217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 345313138513314700403786069 1011659585488226661339217)
                    ·
                      rfl

theorem cell23_5910600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_5910600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910600 prefixEnd_5910600 := by exact prefixLift 5910600
  have htrace : WordTrace (prefixWord ++ tailWord_5910600) baseStart_5910600 baseEnd_5910600 := by
    simpa [prefixWord, tailWord_5910600, baseEnd_5910600] using wordTrace_append hprefix tailTrace_5910600
  have hstable : (prefixWord ++ tailWord_5910600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910600).length < 2 ^ (prefixWord ++ tailWord_5910600).sum := by decide
  have hdescent : baseEnd_5910600 < baseStart_5910600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910617 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 5, 4]
def baseStart_5910617 : Nat := 118140960795 + 5910617 * 2 ^ 59
def prefixEnd_5910617 : Nat := 4983230072969 + 3 ^ 40 * 5910617 * 2
def baseEnd_5910617 : Nat := 1011662495211935472501691

theorem tailTrace_5910617 : CollatzResearch.WordTrace tailWord_5910617 prefixEnd_5910617 1011662495211935472501691 := by
  unfold tailWord_5910617
  simp only [CollatzResearch.WordTrace]
  refine ⟨215577912427851536862050105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143718608285234357908033403 215577912427851536862050105)
  ·
    refine ⟨161683434320888652646537579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215577912427851536862050105 161683434320888652646537579)
    ·
      refine ⟨242525151481332978969806369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161683434320888652646537579 242525151481332978969806369)
      ·
        refine ⟨181893863610999734227354777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242525151481332978969806369 181893863610999734227354777)
        ·
          refine ⟨136420397708249800670516083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181893863610999734227354777 136420397708249800670516083)
          ·
            refine ⟨204630596562374701005774125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136420397708249800670516083 204630596562374701005774125)
            ·
              refine ⟨76736473710890512877165297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204630596562374701005774125 76736473710890512877165297)
              ·
                refine ⟨57552355283167884657873973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76736473710890512877165297 57552355283167884657873973)
                ·
                  refine ⟨5395533307796989186675685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57552355283167884657873973 5395533307796989186675685)
                  ·
                    refine ⟨1011662495211935472501691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395533307796989186675685 1011662495211935472501691)
                    ·
                      rfl

theorem cell23_5910617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 5, 4].length) (baseStart_5910617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910617 prefixEnd_5910617 := by exact prefixLift 5910617
  have htrace : WordTrace (prefixWord ++ tailWord_5910617) baseStart_5910617 baseEnd_5910617 := by
    simpa [prefixWord, tailWord_5910617, baseEnd_5910617] using wordTrace_append hprefix tailTrace_5910617
  have hstable : (prefixWord ++ tailWord_5910617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910617).length < 2 ^ (prefixWord ++ tailWord_5910617).sum := by decide
  have hdescent : baseEnd_5910617 < baseStart_5910617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910624 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2]
def baseStart_5910624 : Nat := 118140960795 + 5910624 * 2 ^ 59
def prefixEnd_5910624 : Nat := 4983230072969 + 3 ^ 40 * 5910624 * 2
def baseEnd_5910624 : Nat := 3034991080000387890117541

theorem tailTrace_5910624 : CollatzResearch.WordTrace tailWord_5910624 prefixEnd_5910624 3034991080000387890117541 := by
  unfold tailWord_5910624
  simp only [CollatzResearch.WordTrace]
  refine ⟨107789083869413088528777463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143718778492550784705036617 107789083869413088528777463)
  ·
    refine ⟨161683625804119632793166195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107789083869413088528777463 161683625804119632793166195)
    ·
      refine ⟨242525438706179449189749293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161683625804119632793166195 242525438706179449189749293)
      ·
        refine ⟨90947039514817293446155985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242525438706179449189749293 90947039514817293446155985)
        ·
          refine ⟨68210279636112970084616989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90947039514817293446155985 68210279636112970084616989)
          ·
            refine ⟨25578854863542363781731371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68210279636112970084616989 25578854863542363781731371)
            ·
              refine ⟨38368282295313545672597057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25578854863542363781731371 38368282295313545672597057)
              ·
                refine ⟨28776211721485159254447793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38368282295313545672597057 28776211721485159254447793)
                ·
                  refine ⟨21582158791113869440835845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28776211721485159254447793 21582158791113869440835845)
                  ·
                    refine ⟨4046654773333850520156721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21582158791113869440835845 4046654773333850520156721)
                    ·
                      refine ⟨3034991080000387890117541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046654773333850520156721 3034991080000387890117541)
                      ·
                        rfl

theorem cell23_5910624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_5910624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910624 prefixEnd_5910624 := by exact prefixLift 5910624
  have htrace : WordTrace (prefixWord ++ tailWord_5910624) baseStart_5910624 baseEnd_5910624 := by
    simpa [prefixWord, tailWord_5910624, baseEnd_5910624] using wordTrace_append hprefix tailTrace_5910624
  have hstable : (prefixWord ++ tailWord_5910624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910624).length < 2 ^ (prefixWord ++ tailWord_5910624).sum := by decide
  have hdescent : baseEnd_5910624 < baseStart_5910624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910637 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5910637 : Nat := 118140960795 + 5910637 * 2 ^ 59
def prefixEnd_5910637 : Nat := 4983230072969 + 3 ^ 40 * 5910637 * 2
def baseEnd_5910637 : Nat := 3034997755248896339254981

theorem tailTrace_5910637 : CollatzResearch.WordTrace tailWord_5910637 prefixEnd_5910637 3034997755248896339254981 := by
  unfold tailWord_5910637
  simp only [CollatzResearch.WordTrace]
  refine ⟨215578641887779080277778165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143719094591852720185185443 215578641887779080277778165)
  ·
    refine ⟨20210497676979288776041703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215578641887779080277778165 20210497676979288776041703)
    ·
      refine ⟨30315746515468933164062555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20210497676979288776041703 30315746515468933164062555)
      ·
        refine ⟨45473619773203399746093833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30315746515468933164062555 45473619773203399746093833)
        ·
          refine ⟨34105214829902549809570375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45473619773203399746093833 34105214829902549809570375)
          ·
            refine ⟨51157822244853824714355563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34105214829902549809570375 51157822244853824714355563)
            ·
              refine ⟨76736733367280737071533345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51157822244853824714355563 76736733367280737071533345)
              ·
                refine ⟨57552550025460552803650009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76736733367280737071533345 57552550025460552803650009)
                ·
                  refine ⟨43164412519095414602737507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57552550025460552803650009 43164412519095414602737507)
                  ·
                    refine ⟨64746618778643121904106261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43164412519095414602737507 64746618778643121904106261)
                    ·
                      refine ⟨3034997755248896339254981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64746618778643121904106261 3034997755248896339254981)
                      ·
                        rfl

theorem cell23_5910637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5910637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910637 prefixEnd_5910637 := by exact prefixLift 5910637
  have htrace : WordTrace (prefixWord ++ tailWord_5910637) baseStart_5910637 baseEnd_5910637 := by
    simpa [prefixWord, tailWord_5910637, baseEnd_5910637] using wordTrace_append hprefix tailTrace_5910637
  have hstable : (prefixWord ++ tailWord_5910637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910637).length < 2 ^ (prefixWord ++ tailWord_5910637).sum := by decide
  have hdescent : baseEnd_5910637 < baseStart_5910637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910707 : List Nat := [1, 1, 1, 2, 3, 2, 1, 5, 1, 6]
def baseStart_5910707 : Nat := 118140960795 + 5910707 * 2 ^ 59
def prefixEnd_5910707 : Nat := 4983230072969 + 3 ^ 40 * 5910707 * 2
def baseEnd_5910707 : Nat := 1011677899631570355126553

theorem tailTrace_5910707 : CollatzResearch.WordTrace tailWord_5910707 prefixEnd_5910707 1011677899631570355126553 := by
  unfold tailWord_5910707
  simp only [CollatzResearch.WordTrace]
  refine ⟨215581194997525482232826375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143720796665016988155217583 215581194997525482232826375)
  ·
    refine ⟨323371792496288223349239563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215581194997525482232826375 323371792496288223349239563)
    ·
      refine ⟨485057688744432335023859345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323371792496288223349239563 485057688744432335023859345)
      ·
        refine ⟨363793266558324251267894509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485057688744432335023859345 363793266558324251267894509)
        ·
          refine ⟨136422474959371594225460441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363793266558324251267894509 136422474959371594225460441)
          ·
            refine ⟨102316856219528695669095331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136422474959371594225460441 102316856219528695669095331)
            ·
              refine ⟨153475284329293043503642997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102316856219528695669095331 153475284329293043503642997)
              ·
                refine ⟨14388307905871222828466531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153475284329293043503642997 14388307905871222828466531)
                ·
                  refine ⟨21582461858806834242699797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14388307905871222828466531 21582461858806834242699797)
                  ·
                    refine ⟨1011677899631570355126553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21582461858806834242699797 1011677899631570355126553)
                    ·
                      rfl

theorem cell23_5910707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 6].length) (baseStart_5910707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910707 prefixEnd_5910707 := by exact prefixLift 5910707
  have htrace : WordTrace (prefixWord ++ tailWord_5910707) baseStart_5910707 baseEnd_5910707 := by
    simpa [prefixWord, tailWord_5910707, baseEnd_5910707] using wordTrace_append hprefix tailTrace_5910707
  have hstable : (prefixWord ++ tailWord_5910707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910707).length < 2 ^ (prefixWord ++ tailWord_5910707).sum := by decide
  have hdescent : baseEnd_5910707 < baseStart_5910707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910711 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 1, 5]
def baseStart_5910711 : Nat := 118140960795 + 5910711 * 2 ^ 59
def prefixEnd_5910711 : Nat := 4983230072969 + 3 ^ 40 * 5910711 * 2
def baseEnd_5910711 : Nat := 1011678584272443016576547

theorem tailTrace_5910711 : CollatzResearch.WordTrace tailWord_5910711 prefixEnd_5910711 1011678584272443016576547 := by
  unfold tailWord_5910711
  simp only [CollatzResearch.WordTrace]
  refine ⟨215581340889510990915971987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143720893926340660610647991 215581340889510990915971987)
  ·
    refine ⟨323372011334266486373957981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215581340889510990915971987 323372011334266486373957981)
    ·
      refine ⟨121264504250349932390234243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323372011334266486373957981 121264504250349932390234243)
      ·
        refine ⟨181896756375524898585351365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121264504250349932390234243 181896756375524898585351365)
        ·
          refine ⟨34105641820410918484753381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181896756375524898585351365 34105641820410918484753381)
          ·
            refine ⟨6394807841327047215891259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34105641820410918484753381 6394807841327047215891259)
            ·
              refine ⟨9592211761990570823836889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6394807841327047215891259 9592211761990570823836889)
              ·
                refine ⟨7194158821492928117877667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9592211761990570823836889 7194158821492928117877667)
                ·
                  refine ⟨10791238232239392176816501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7194158821492928117877667 10791238232239392176816501)
                  ·
                    refine ⟨1011678584272443016576547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10791238232239392176816501 1011678584272443016576547)
                    ·
                      rfl

theorem cell23_5910711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_5910711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910711 prefixEnd_5910711 := by exact prefixLift 5910711
  have htrace : WordTrace (prefixWord ++ tailWord_5910711) baseStart_5910711 baseEnd_5910711 := by
    simpa [prefixWord, tailWord_5910711, baseEnd_5910711] using wordTrace_append hprefix tailTrace_5910711
  have hstable : (prefixWord ++ tailWord_5910711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910711).length < 2 ^ (prefixWord ++ tailWord_5910711).sum := by decide
  have hdescent : baseEnd_5910711 < baseStart_5910711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910714 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2]
def baseStart_5910714 : Nat := 118140960795 + 5910714 * 2 ^ 59
def prefixEnd_5910714 : Nat := 4983230072969 + 3 ^ 40 * 5910714 * 2
def baseEnd_5910714 : Nat := 3035037293259292537992127

theorem tailTrace_5910714 : CollatzResearch.WordTrace tailWord_5910714 prefixEnd_5910714 3035037293259292537992127 := by
  unfold tailWord_5910714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53895362577125030607082799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143720966872333414952220797 53895362577125030607082799)
  ·
    refine ⟨80843043865687545910624199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53895362577125030607082799 80843043865687545910624199)
    ·
      refine ⟨121264565798531318865936299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80843043865687545910624199 121264565798531318865936299)
      ·
        refine ⟨181896848697796978298904449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121264565798531318865936299 181896848697796978298904449)
        ·
          refine ⟨136422636523347733724178337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181896848697796978298904449 136422636523347733724178337)
          ·
            refine ⟨102316977392510800293133753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136422636523347733724178337 102316977392510800293133753)
            ·
              refine ⟨76737733044383100219850315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102316977392510800293133753 76737733044383100219850315)
              ·
                refine ⟨115106599566574650329775473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76737733044383100219850315 115106599566574650329775473)
                ·
                  refine ⟨86329949674930987747331605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115106599566574650329775473 86329949674930987747331605)
                  ·
                    refine ⟨4046716391012390050656169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86329949674930987747331605 4046716391012390050656169)
                    ·
                      refine ⟨3035037293259292537992127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046716391012390050656169 3035037293259292537992127)
                      ·
                        rfl

theorem cell23_5910714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2].length) (baseStart_5910714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910714 prefixEnd_5910714 := by exact prefixLift 5910714
  have htrace : WordTrace (prefixWord ++ tailWord_5910714) baseStart_5910714 baseEnd_5910714 := by
    simpa [prefixWord, tailWord_5910714, baseEnd_5910714] using wordTrace_append hprefix tailTrace_5910714
  have hstable : (prefixWord ++ tailWord_5910714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910714).length < 2 ^ (prefixWord ++ tailWord_5910714).sum := by decide
  have hdescent : baseEnd_5910714 < baseStart_5910714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910724 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5910724 : Nat := 118140960795 + 5910724 * 2 ^ 59
def prefixEnd_5910724 : Nat := 4983230072969 + 3 ^ 40 * 5910724 * 2
def baseEnd_5910724 : Nat := 1011680809355279166289027

theorem tailTrace_5910724 : CollatzResearch.WordTrace tailWord_5910724 prefixEnd_5910724 1011680809355279166289027 := by
  unfold tailWord_5910724
  simp only [CollatzResearch.WordTrace]
  refine ⟨107790907519231947068097613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143721210025642596090796817 107790907519231947068097613)
  ·
    refine ⟨40421590319711980150536605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107790907519231947068097613 40421590319711980150536605)
    ·
      refine ⟨15158096369891992556451227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40421590319711980150536605 15158096369891992556451227)
      ·
        refine ⟨22737144554837988834676841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15158096369891992556451227 22737144554837988834676841)
        ·
          refine ⟨17052858416128491626007631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22737144554837988834676841 17052858416128491626007631)
          ·
            refine ⟨25579287624192737439011447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17052858416128491626007631 25579287624192737439011447)
            ·
              refine ⟨38368931436289106158517171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25579287624192737439011447 38368931436289106158517171)
              ·
                refine ⟨57553397154433659237775757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38368931436289106158517171 57553397154433659237775757)
                ·
                  refine ⟨21582523932912622214165909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57553397154433659237775757 21582523932912622214165909)
                  ·
                    refine ⟨1011680809355279166289027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21582523932912622214165909 1011680809355279166289027)
                    ·
                      rfl

theorem cell23_5910724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5910724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910724 prefixEnd_5910724 := by exact prefixLift 5910724
  have htrace : WordTrace (prefixWord ++ tailWord_5910724) baseStart_5910724 baseEnd_5910724 := by
    simpa [prefixWord, tailWord_5910724, baseEnd_5910724] using wordTrace_append hprefix tailTrace_5910724
  have hstable : (prefixWord ++ tailWord_5910724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910724).length < 2 ^ (prefixWord ++ tailWord_5910724).sum := by decide
  have hdescent : baseEnd_5910724 < baseStart_5910724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910731 : List Nat := [1, 1, 1, 1, 3, 2, 7, 1, 1, 1, 4]
def baseStart_5910731 : Nat := 118140960795 + 5910731 * 2 ^ 59
def prefixEnd_5910731 : Nat := 4983230072969 + 3 ^ 40 * 5910731 * 2
def baseEnd_5910731 : Nat := 3035046022430418971479549

theorem tailTrace_5910731 : CollatzResearch.WordTrace tailWord_5910731 prefixEnd_5910731 3035046022430418971479549 := by
  unfold tailWord_5910731
  simp only [CollatzResearch.WordTrace]
  refine ⟨215582070349438534331700047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143721380232959022887800031 215582070349438534331700047)
  ·
    refine ⟨323373105524157801497550071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215582070349438534331700047 323373105524157801497550071)
    ·
      refine ⟨485059658286236702246325107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323373105524157801497550071 485059658286236702246325107)
      ·
        refine ⟨727589487429355053369487661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485059658286236702246325107 727589487429355053369487661)
        ·
          refine ⟨272846057786008145013557873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727589487429355053369487661 272846057786008145013557873)
          ·
            refine ⟨204634543339506108760168405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272846057786008145013557873 204634543339506108760168405)
            ·
              refine ⟨4796122109519674424066447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 204634543339506108760168405 4796122109519674424066447)
              ·
                refine ⟨7194183164279511636099671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796122109519674424066447 7194183164279511636099671)
                ·
                  refine ⟨10791274746419267454149507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7194183164279511636099671 10791274746419267454149507)
                  ·
                    refine ⟨16186912119628901181224261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10791274746419267454149507 16186912119628901181224261)
                    ·
                      refine ⟨3035046022430418971479549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16186912119628901181224261 3035046022430418971479549)
                      ·
                        rfl

theorem cell23_5910731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 1, 1, 4].length) (baseStart_5910731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910731 prefixEnd_5910731 := by exact prefixLift 5910731
  have htrace : WordTrace (prefixWord ++ tailWord_5910731) baseStart_5910731 baseEnd_5910731 := by
    simpa [prefixWord, tailWord_5910731, baseEnd_5910731] using wordTrace_append hprefix tailTrace_5910731
  have hstable : (prefixWord ++ tailWord_5910731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910731).length < 2 ^ (prefixWord ++ tailWord_5910731).sum := by decide
  have hdescent : baseEnd_5910731 < baseStart_5910731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910742 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5910742 : Nat := 118140960795 + 5910742 * 2 ^ 59
def prefixEnd_5910742 : Nat := 4983230072969 + 3 ^ 40 * 5910742 * 2
def baseEnd_5910742 : Nat := 3035051670717618428441999

theorem tailTrace_5910742 : CollatzResearch.WordTrace tailWord_5910742 prefixEnd_5910742 3035051670717618428441999 := by
  unfold tailWord_5910742
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473904472024917700646905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143721647701599122140233653 13473904472024917700646905)
  ·
    refine ⟨10105428354018688275485179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13473904472024917700646905 10105428354018688275485179)
    ·
      refine ⟨15158142531028032413227769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10105428354018688275485179 15158142531028032413227769)
      ·
        refine ⟨11368606898271024309920827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15158142531028032413227769 11368606898271024309920827)
        ·
          refine ⟨17052910347406536464881241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368606898271024309920827 17052910347406536464881241)
          ·
            refine ⟨12789682760554902348660931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17052910347406536464881241 12789682760554902348660931)
            ·
              refine ⟨19184524140832353522991397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12789682760554902348660931 19184524140832353522991397)
              ·
                refine ⟨3597098276406066285560887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19184524140832353522991397 3597098276406066285560887)
                ·
                  refine ⟨5395647414609099428341331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597098276406066285560887 5395647414609099428341331)
                  ·
                    refine ⟨8093471121913649142511997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395647414609099428341331 8093471121913649142511997)
                    ·
                      refine ⟨3035051670717618428441999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093471121913649142511997 3035051670717618428441999)
                      ·
                        rfl

theorem cell23_5910742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5910742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910742 prefixEnd_5910742 := by exact prefixLift 5910742
  have htrace : WordTrace (prefixWord ++ tailWord_5910742) baseStart_5910742 baseEnd_5910742 := by
    simpa [prefixWord, tailWord_5910742, baseEnd_5910742] using wordTrace_append hprefix tailTrace_5910742
  have hstable : (prefixWord ++ tailWord_5910742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910742).length < 2 ^ (prefixWord ++ tailWord_5910742).sum := by decide
  have hdescent : baseEnd_5910742 < baseStart_5910742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910765 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5910765 : Nat := 118140960795 + 5910765 * 2 ^ 59
def prefixEnd_5910765 : Nat := 4983230072969 + 3 ^ 40 * 5910765 * 2
def baseEnd_5910765 : Nat := 3035063480772671838454393

theorem tailTrace_5910765 : CollatzResearch.WordTrace tailWord_5910765 prefixEnd_5910765 3035063480772671838454393 := by
  unfold tailWord_5910765
  simp only [CollatzResearch.WordTrace]
  refine ⟨215583310431315358138437749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143722206954210238758958499 215583310431315358138437749)
  ·
    refine ⟨20210935352935814825478539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215583310431315358138437749 20210935352935814825478539)
    ·
      refine ⟨30316403029403722238217809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20210935352935814825478539 30316403029403722238217809)
      ·
        refine ⟨22737302272052791678663357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30316403029403722238217809 22737302272052791678663357)
        ·
          refine ⟨8526488352019796879498759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22737302272052791678663357 8526488352019796879498759)
          ·
            refine ⟨12789732528029695319248139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526488352019796879498759 12789732528029695319248139)
            ·
              refine ⟨19184598792044542978872209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12789732528029695319248139 19184598792044542978872209)
              ·
                refine ⟨14388449094033407234154157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19184598792044542978872209 14388449094033407234154157)
                ·
                  refine ⟨5395668410262527712807809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14388449094033407234154157 5395668410262527712807809)
                  ·
                    refine ⟨4046751307696895784605857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395668410262527712807809 4046751307696895784605857)
                    ·
                      refine ⟨3035063480772671838454393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046751307696895784605857 3035063480772671838454393)
                      ·
                        rfl

theorem cell23_5910765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5910765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910765 prefixEnd_5910765 := by exact prefixLift 5910765
  have htrace : WordTrace (prefixWord ++ tailWord_5910765) baseStart_5910765 baseEnd_5910765 := by
    simpa [prefixWord, tailWord_5910765, baseEnd_5910765] using wordTrace_append hprefix tailTrace_5910765
  have hstable : (prefixWord ++ tailWord_5910765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910765).length < 2 ^ (prefixWord ++ tailWord_5910765).sum := by decide
  have hdescent : baseEnd_5910765 < baseStart_5910765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910782 : List Nat := [4, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5910782 : Nat := 118140960795 + 5910782 * 2 ^ 59
def prefixEnd_5910782 : Nat := 4983230072969 + 3 ^ 40 * 5910782 * 2
def baseEnd_5910782 : Nat := 3035072209943798271941815

theorem tailTrace_5910782 : CollatzResearch.WordTrace tailWord_5910782 prefixEnd_5910782 3035072209943798271941815 := by
  unfold tailWord_5910782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26947991309031721255225825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143722620314835846694537733 26947991309031721255225825)
  ·
    refine ⟨20210993481773790941419369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26947991309031721255225825 20210993481773790941419369)
    ·
      refine ⟨15158245111330343206064527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20210993481773790941419369 15158245111330343206064527)
      ·
        refine ⟨22737367666995514809096791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15158245111330343206064527 22737367666995514809096791)
        ·
          refine ⟨34106051500493272213645187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22737367666995514809096791 34106051500493272213645187)
          ·
            refine ⟨51159077250739908320467781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34106051500493272213645187 51159077250739908320467781)
            ·
              refine ⟨9592326984513732810087709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51159077250739908320467781 9592326984513732810087709)
              ·
                refine ⟨3597122619192649803782891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9592326984513732810087709 3597122619192649803782891)
                ·
                  refine ⟨5395683928788974705674337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597122619192649803782891 5395683928788974705674337)
                  ·
                    refine ⟨4046762946591731029255753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395683928788974705674337 4046762946591731029255753)
                    ·
                      refine ⟨3035072209943798271941815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046762946591731029255753 3035072209943798271941815)
                      ·
                        rfl

theorem cell23_5910782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5910782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910782 prefixEnd_5910782 := by exact prefixLift 5910782
  have htrace : WordTrace (prefixWord ++ tailWord_5910782) baseStart_5910782 baseEnd_5910782 := by
    simpa [prefixWord, tailWord_5910782, baseEnd_5910782] using wordTrace_append hprefix tailTrace_5910782
  have hstable : (prefixWord ++ tailWord_5910782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910782).length < 2 ^ (prefixWord ++ tailWord_5910782).sum := by decide
  have hdescent : baseEnd_5910782 < baseStart_5910782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910815 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 2, 1, 3]
def baseStart_5910815 : Nat := 118140960795 + 5910815 * 2 ^ 59
def prefixEnd_5910815 : Nat := 4983230072969 + 3 ^ 40 * 5910815 * 2
def baseEnd_5910815 : Nat := 3035089154805396642829163

theorem tailTrace_5910815 : CollatzResearch.WordTrace tailWord_5910815 prefixEnd_5910815 3035089154805396642829163 := by
  unfold tailWord_5910815
  simp only [CollatzResearch.WordTrace]
  refine ⟨215585134081134216677757899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143723422720756144451838599 215585134081134216677757899)
  ·
    refine ⟨323377701121701325016636849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215585134081134216677757899 323377701121701325016636849)
    ·
      refine ⟨242533275841275993762477637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323377701121701325016636849 242533275841275993762477637)
      ·
        refine ⟨45474989220239248830464557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242533275841275993762477637 45474989220239248830464557)
        ·
          refine ⟨17053120957589718311424209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45474989220239248830464557 17053120957589718311424209)
          ·
            refine ⟨12789840718192288733568157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17053120957589718311424209 12789840718192288733568157)
            ·
              refine ⟨4796190269322108275088059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12789840718192288733568157 4796190269322108275088059)
              ·
                refine ⟨7194285403983162412632089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796190269322108275088059 7194285403983162412632089)
                ·
                  refine ⟨5395714052987371809474067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7194285403983162412632089 5395714052987371809474067)
                  ·
                    refine ⟨8093571079481057714211101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395714052987371809474067 8093571079481057714211101)
                    ·
                      refine ⟨3035089154805396642829163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093571079481057714211101 3035089154805396642829163)
                      ·
                        rfl

theorem cell23_5910815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_5910815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910815 prefixEnd_5910815 := by exact prefixLift 5910815
  have htrace : WordTrace (prefixWord ++ tailWord_5910815) baseStart_5910815 baseEnd_5910815 := by
    simpa [prefixWord, tailWord_5910815, baseEnd_5910815] using wordTrace_append hprefix tailTrace_5910815
  have hstable : (prefixWord ++ tailWord_5910815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910815).length < 2 ^ (prefixWord ++ tailWord_5910815).sum := by decide
  have hdescent : baseEnd_5910815 < baseStart_5910815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910841 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5910841 : Nat := 118140960795 + 5910841 * 2 ^ 59
def prefixEnd_5910841 : Nat := 4983230072969 + 3 ^ 40 * 5910841 * 2
def baseEnd_5910841 : Nat := 3035102505302413541104043

theorem tailTrace_5910841 : CollatzResearch.WordTrace tailWord_5910841 prefixEnd_5910841 3035102505302413541104043 := by
  unfold tailWord_5910841
  simp only [CollatzResearch.WordTrace]
  refine ⟨215586082379040023118204377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143724054919360015412136251 215586082379040023118204377)
  ·
    refine ⟨161689561784280017338653283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215586082379040023118204377 161689561784280017338653283)
    ·
      refine ⟨242534342676420026007979925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161689561784280017338653283 242534342676420026007979925)
      ·
        refine ⟨11368797312957188719124059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242534342676420026007979925 11368797312957188719124059)
        ·
          refine ⟨17053195969435783078686089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11368797312957188719124059 17053195969435783078686089)
          ·
            refine ⟨12789896977076837309014567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17053195969435783078686089 12789896977076837309014567)
            ·
              refine ⟨19184845465615255963521851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12789896977076837309014567 19184845465615255963521851)
              ·
                refine ⟨28777268198422883945282777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19184845465615255963521851 28777268198422883945282777)
                ·
                  refine ⟨21582951148817162958962083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28777268198422883945282777 21582951148817162958962083)
                  ·
                    refine ⟨32374426723225744438443125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21582951148817162958962083 32374426723225744438443125)
                    ·
                      refine ⟨3035102505302413541104043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32374426723225744438443125 3035102505302413541104043)
                      ·
                        rfl

theorem cell23_5910841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5910841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910841 prefixEnd_5910841 := by exact prefixLift 5910841
  have htrace : WordTrace (prefixWord ++ tailWord_5910841) baseStart_5910841 baseEnd_5910841 := by
    simpa [prefixWord, tailWord_5910841, baseEnd_5910841] using wordTrace_append hprefix tailTrace_5910841
  have hstable : (prefixWord ++ tailWord_5910841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910841).length < 2 ^ (prefixWord ++ tailWord_5910841).sum := by decide
  have hdescent : baseEnd_5910841 < baseStart_5910841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910874 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_5910874 : Nat := 118140960795 + 5910874 * 2 ^ 59
def prefixEnd_5910874 : Nat := 4983230072969 + 3 ^ 40 * 5910874 * 2
def baseEnd_5910874 : Nat := 1011706483388003970663797

theorem tailTrace_5910874 : CollatzResearch.WordTrace tailWord_5910874 prefixEnd_5910874 1011706483388003970663797 := by
  unfold tailWord_5910874
  simp only [CollatzResearch.WordTrace]
  refine ⟨53896821496980117438538919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143724857325280313169437117 53896821496980117438538919)
  ·
    refine ⟨80845232245470176157808379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53896821496980117438538919 80845232245470176157808379)
    ·
      refine ⟨121267848368205264236712569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80845232245470176157808379 121267848368205264236712569)
      ·
        refine ⟨90950886276153948177534427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121267848368205264236712569 90950886276153948177534427)
        ·
          refine ⟨136426329414230922266301641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90950886276153948177534427 136426329414230922266301641)
          ·
            refine ⟨102319747060673191699726231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136426329414230922266301641 102319747060673191699726231)
            ·
              refine ⟨153479620591009787549589347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102319747060673191699726231 153479620591009787549589347)
              ·
                refine ⟨230219430886514681324384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153479620591009787549589347 230219430886514681324384021)
                ·
                  refine ⟨10791535822805375687080501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230219430886514681324384021 10791535822805375687080501)
                  ·
                    refine ⟨1011706483388003970663797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10791535822805375687080501 1011706483388003970663797)
                    ·
                      rfl

theorem cell23_5910874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_5910874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910874 prefixEnd_5910874 := by exact prefixLift 5910874
  have htrace : WordTrace (prefixWord ++ tailWord_5910874) baseStart_5910874 baseEnd_5910874 := by
    simpa [prefixWord, tailWord_5910874, baseEnd_5910874] using wordTrace_append hprefix tailTrace_5910874
  have hstable : (prefixWord ++ tailWord_5910874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910874).length < 2 ^ (prefixWord ++ tailWord_5910874).sum := by decide
  have hdescent : baseEnd_5910874 < baseStart_5910874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910884 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_5910884 : Nat := 118140960795 + 5910884 * 2 ^ 59
def prefixEnd_5910884 : Nat := 4983230072969 + 3 ^ 40 * 5910884 * 2
def baseEnd_5910884 : Nat := 3035124584970556872866345

theorem tailTrace_5910884 : CollatzResearch.WordTrace tailWord_5910884 prefixEnd_5910884 3035124584970556872866345 := by
  unfold tailWord_5910884
  simp only [CollatzResearch.WordTrace]
  refine ⟨107793825358942120731009853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143725100478589494308013137 107793825358942120731009853)
  ·
    refine ⟨40422684509603295274128695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107793825358942120731009853 40422684509603295274128695)
    ·
      refine ⟨60634026764404942911193043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40422684509603295274128695 60634026764404942911193043)
      ·
        refine ⟨90951040146607414366789565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60634026764404942911193043 90951040146607414366789565)
        ·
          refine ⟨34106640054977780387546087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90951040146607414366789565 34106640054977780387546087)
          ·
            refine ⟨51159960082466670581319131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34106640054977780387546087 51159960082466670581319131)
            ·
              refine ⟨76739940123700005871978697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51159960082466670581319131 76739940123700005871978697)
              ·
                refine ⟨57554955092775004403984023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76739940123700005871978697 57554955092775004403984023)
                ·
                  refine ⟨86332432639162506605976035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57554955092775004403984023 86332432639162506605976035)
                  ·
                    refine ⟨129498648958743759908964053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86332432639162506605976035 129498648958743759908964053)
                    ·
                      refine ⟨3035124584970556872866345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129498648958743759908964053 3035124584970556872866345)
                      ·
                        rfl

theorem cell23_5910884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_5910884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910884 prefixEnd_5910884 := by exact prefixLift 5910884
  have htrace : WordTrace (prefixWord ++ tailWord_5910884) baseStart_5910884 baseEnd_5910884 := by
    simpa [prefixWord, tailWord_5910884, baseEnd_5910884] using wordTrace_append hprefix tailTrace_5910884
  have hstable : (prefixWord ++ tailWord_5910884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910884).length < 2 ^ (prefixWord ++ tailWord_5910884).sum := by decide
  have hdescent : baseEnd_5910884 < baseStart_5910884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910901 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5910901 : Nat := 118140960795 + 5910901 * 2 ^ 59
def prefixEnd_5910901 : Nat := 4983230072969 + 3 ^ 40 * 5910901 * 2
def baseEnd_5910901 : Nat := 3035133314141683306353767

theorem tailTrace_5910901 : CollatzResearch.WordTrace tailWord_5910901 prefixEnd_5910901 3035133314141683306353767 := by
  unfold tailWord_5910901
  simp only [CollatzResearch.WordTrace]
  refine ⟨215588270758822653365388557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143725513839215102243592371 215588270758822653365388557)
  ·
    refine ⟨80845601534558495012020709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215588270758822653365388557 80845601534558495012020709)
    ·
      refine ⟨15158550287729717814753883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80845601534558495012020709 15158550287729717814753883)
      ·
        refine ⟨22737825431594576722130825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15158550287729717814753883 22737825431594576722130825)
        ·
          refine ⟨17053369073695932541598119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22737825431594576722130825 17053369073695932541598119)
          ·
            refine ⟨25580053610543898812397179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17053369073695932541598119 25580053610543898812397179)
            ·
              refine ⟨38370080415815848218595769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25580053610543898812397179 38370080415815848218595769)
              ·
                refine ⟨28777560311861886163946827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38370080415815848218595769 28777560311861886163946827)
                ·
                  refine ⟨43166340467792829245920241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28777560311861886163946827 43166340467792829245920241)
                  ·
                    refine ⟨32374755350844621934440181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43166340467792829245920241 32374755350844621934440181)
                    ·
                      refine ⟨3035133314141683306353767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32374755350844621934440181 3035133314141683306353767)
                      ·
                        rfl

theorem cell23_5910901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5910901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910901 prefixEnd_5910901 := by exact prefixLift 5910901
  have htrace : WordTrace (prefixWord ++ tailWord_5910901) baseStart_5910901 baseEnd_5910901 := by
    simpa [prefixWord, tailWord_5910901, baseEnd_5910901] using wordTrace_append hprefix tailTrace_5910901
  have hstable : (prefixWord ++ tailWord_5910901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910901).length < 2 ^ (prefixWord ++ tailWord_5910901).sum := by decide
  have hdescent : baseEnd_5910901 < baseStart_5910901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910911 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 4, 4, 2]
def baseStart_5910911 : Nat := 118140960795 + 5910911 * 2 ^ 59
def prefixEnd_5910911 : Nat := 4983230072969 + 3 ^ 40 * 5910911 * 2
def baseEnd_5910911 : Nat := 3035138448948228267228721

theorem tailTrace_5910911 : CollatzResearch.WordTrace tailWord_5910911 prefixEnd_5910911 3035138448948228267228721 := by
  unfold tailWord_5910911
  simp only [CollatzResearch.WordTrace]
  refine ⟨215588635488786425073252587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143725756992524283382168391 215588635488786425073252587)
  ·
    refine ⟨323382953233179637609878881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215588635488786425073252587 323382953233179637609878881)
    ·
      refine ⟨242537214924884728207409161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323382953233179637609878881 242537214924884728207409161)
      ·
        refine ⟨181902911193663546155556871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242537214924884728207409161 181902911193663546155556871)
        ·
          refine ⟨272854366790495319233335307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181902911193663546155556871 272854366790495319233335307)
          ·
            refine ⟨409281550185742978850002961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272854366790495319233335307 409281550185742978850002961)
            ·
              refine ⟨306961162639307234137502221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409281550185742978850002961 306961162639307234137502221)
              ·
                refine ⟨115110435989740212801563333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306961162639307234137502221 115110435989740212801563333)
                ·
                  refine ⟨21583206748076289900293125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115110435989740212801563333 21583206748076289900293125)
                  ·
                    refine ⟨4046851265264304356304961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21583206748076289900293125 4046851265264304356304961)
                    ·
                      refine ⟨3035138448948228267228721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046851265264304356304961 3035138448948228267228721)
                      ·
                        rfl

theorem cell23_5910911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_5910911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910911 prefixEnd_5910911 := by exact prefixLift 5910911
  have htrace : WordTrace (prefixWord ++ tailWord_5910911) baseStart_5910911 baseEnd_5910911 := by
    simpa [prefixWord, tailWord_5910911, baseEnd_5910911] using wordTrace_append hprefix tailTrace_5910911
  have hstable : (prefixWord ++ tailWord_5910911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910911).length < 2 ^ (prefixWord ++ tailWord_5910911).sum := by decide
  have hdescent : baseEnd_5910911 < baseStart_5910911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910938 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 3, 4]
def baseStart_5910938 : Nat := 118140960795 + 5910938 * 2 ^ 59
def prefixEnd_5910938 : Nat := 4983230072969 + 3 ^ 40 * 5910938 * 2
def baseEnd_5910938 : Nat := 1011717437641966553863699

theorem tailTrace_5910938 : CollatzResearch.WordTrace tailWord_5910938 prefixEnd_5910938 1011717437641966553863699 := by
  unfold tailWord_5910938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53897405064922152171121367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143726413506459072456323645 53897405064922152171121367)
  ·
    refine ⟨80846107597383228256682051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53897405064922152171121367 80846107597383228256682051)
    ·
      refine ⟨121269161396074842385023077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80846107597383228256682051 121269161396074842385023077)
      ·
        refine ⟨22737967761764032947191827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121269161396074842385023077 22737967761764032947191827)
        ·
          refine ⟨34106951642646049420787741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22737967761764032947191827 34106951642646049420787741)
          ·
            refine ⟨12790106865992268532795403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34106951642646049420787741 12790106865992268532795403)
            ·
              refine ⟨19185160298988402799193105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12790106865992268532795403 19185160298988402799193105)
              ·
                refine ⟨14388870224241302099394829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19185160298988402799193105 14388870224241302099394829)
                ·
                  refine ⟨5395826334090488287273061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14388870224241302099394829 5395826334090488287273061)
                  ·
                    refine ⟨1011717437641966553863699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395826334090488287273061 1011717437641966553863699)
                    ·
                      rfl

theorem cell23_5910938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_5910938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910938 prefixEnd_5910938 := by exact prefixLift 5910938
  have htrace : WordTrace (prefixWord ++ tailWord_5910938) baseStart_5910938 baseEnd_5910938 := by
    simpa [prefixWord, tailWord_5910938, baseEnd_5910938] using wordTrace_append hprefix tailTrace_5910938
  have hstable : (prefixWord ++ tailWord_5910938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910938).length < 2 ^ (prefixWord ++ tailWord_5910938).sum := by decide
  have hdescent : baseEnd_5910938 < baseStart_5910938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910948 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_5910948 : Nat := 118140960795 + 5910948 * 2 ^ 59
def prefixEnd_5910948 : Nat := 4983230072969 + 3 ^ 40 * 5910948 * 2
def baseEnd_5910948 : Nat := 3035157447732444622466051

theorem tailTrace_5910948 : CollatzResearch.WordTrace tailWord_5910948 prefixEnd_5910948 3035157447732444622466051 := by
  unfold tailWord_5910948
  simp only [CollatzResearch.WordTrace]
  refine ⟨107794992494826190196174749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143726656659768253594899665 107794992494826190196174749)
  ·
    refine ⟨40423122185559821323565531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107794992494826190196174749 40423122185559821323565531)
    ·
      refine ⟨60634683278339731985348297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40423122185559821323565531 60634683278339731985348297)
      ·
        refine ⟨45476012458754798989011223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60634683278339731985348297 45476012458754798989011223)
        ·
          refine ⟨68214018688132198483516835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45476012458754798989011223 68214018688132198483516835)
          ·
            refine ⟨102321028032198297725275253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68214018688132198483516835 102321028032198297725275253)
            ·
              refine ⟨9592596378018590411744555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102321028032198297725275253 9592596378018590411744555)
              ·
                refine ⟨14388894567027885617616833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9592596378018590411744555 14388894567027885617616833)
                ·
                  refine ⟨10791670925270914213212625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14388894567027885617616833 10791670925270914213212625)
                  ·
                    refine ⟨8093753193953185659909469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10791670925270914213212625 8093753193953185659909469)
                    ·
                      refine ⟨3035157447732444622466051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093753193953185659909469 3035157447732444622466051)
                      ·
                        rfl

theorem cell23_5910948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_5910948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910948 prefixEnd_5910948 := by exact prefixLift 5910948
  have htrace : WordTrace (prefixWord ++ tailWord_5910948) baseStart_5910948 baseEnd_5910948 := by
    simpa [prefixWord, tailWord_5910948, baseEnd_5910948] using wordTrace_append hprefix tailTrace_5910948
  have hstable : (prefixWord ++ tailWord_5910948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910948).length < 2 ^ (prefixWord ++ tailWord_5910948).sum := by decide
  have hdescent : baseEnd_5910948 < baseStart_5910948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5910971 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 9, 2]
def baseStart_5910971 : Nat := 118140960795 + 5910971 * 2 ^ 59
def prefixEnd_5910971 : Nat := 4983230072969 + 3 ^ 40 * 5910971 * 2
def baseEnd_5910971 : Nat := 3035169257787498032478445

theorem tailTrace_5910971 : CollatzResearch.WordTrace tailWord_5910971 prefixEnd_5910971 3035169257787498032478445 := by
  unfold tailWord_5910971
  simp only [CollatzResearch.WordTrace]
  refine ⟨215590823868569055320436767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143727215912379370213624511 215590823868569055320436767)
  ·
    refine ⟨323386235802853582980655151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215590823868569055320436767 323386235802853582980655151)
    ·
      refine ⟨485079353704280374470982727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323386235802853582980655151 485079353704280374470982727)
      ·
        refine ⟨727619030556420561706474091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485079353704280374470982727 727619030556420561706474091)
        ·
          refine ⟨1091428545834630842559711137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727619030556420561706474091 1091428545834630842559711137)
          ·
            refine ⟨818571409375973131919783353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091428545834630842559711137 818571409375973131919783353)
            ·
              refine ⟨613928557031979848939837515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818571409375973131919783353 613928557031979848939837515)
              ·
                refine ⟨920892835547969773409756273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613928557031979848939837515 920892835547969773409756273)
                ·
                  refine ⟨690669626660977330057317205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920892835547969773409756273 690669626660977330057317205)
                  ·
                    refine ⟨4046892343716664043304593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 690669626660977330057317205 4046892343716664043304593)
                    ·
                      refine ⟨3035169257787498032478445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046892343716664043304593 3035169257787498032478445)
                      ·
                        rfl

theorem cell23_5910971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 9, 2].length) (baseStart_5910971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5910971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5910971 prefixEnd_5910971 := by exact prefixLift 5910971
  have htrace : WordTrace (prefixWord ++ tailWord_5910971) baseStart_5910971 baseEnd_5910971 := by
    simpa [prefixWord, tailWord_5910971, baseEnd_5910971] using wordTrace_append hprefix tailTrace_5910971
  have hstable : (prefixWord ++ tailWord_5910971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5910971).length < 2 ^ (prefixWord ++ tailWord_5910971).sum := by decide
  have hdescent : baseEnd_5910971 < baseStart_5910971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5910971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911005 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5911005 : Nat := 118140960795 + 5911005 * 2 ^ 59
def prefixEnd_5911005 : Nat := 4983230072969 + 3 ^ 40 * 5911005 * 2
def baseEnd_5911005 : Nat := 3035186716129750899453289

theorem tailTrace_5911005 : CollatzResearch.WordTrace tailWord_5911005 prefixEnd_5911005 3035186716129750899453289 := by
  unfold tailWord_5911005
  simp only [CollatzResearch.WordTrace]
  refine ⟨215592063950445879127174469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143728042633630586084782979 215592063950445879127174469)
  ·
    refine ⟨40423511990708602336345213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215592063950445879127174469 40423511990708602336345213)
    ·
      refine ⟨15158816996515725876129455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40423511990708602336345213 15158816996515725876129455)
      ·
        refine ⟨22738225494773588814194183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15158816996515725876129455 22738225494773588814194183)
        ·
          refine ⟨34107338242160383221291275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22738225494773588814194183 34107338242160383221291275)
          ·
            refine ⟨51161007363240574831936913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34107338242160383221291275 51161007363240574831936913)
            ·
              refine ⟨38370755522430431123952685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51161007363240574831936913 38370755522430431123952685)
              ·
                refine ⟨14389033320911411671482257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38370755522430431123952685 14389033320911411671482257)
                ·
                  refine ⟨10791774990683558753611693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14389033320911411671482257 10791774990683558753611693)
                  ·
                    refine ⟨4046915621506334532604385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10791774990683558753611693 4046915621506334532604385)
                    ·
                      refine ⟨3035186716129750899453289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046915621506334532604385 3035186716129750899453289)
                      ·
                        rfl

theorem cell23_5911005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5911005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911005 prefixEnd_5911005 := by exact prefixLift 5911005
  have htrace : WordTrace (prefixWord ++ tailWord_5911005) baseStart_5911005 baseEnd_5911005 := by
    simpa [prefixWord, tailWord_5911005, baseEnd_5911005] using wordTrace_append hprefix tailTrace_5911005
  have hstable : (prefixWord ++ tailWord_5911005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911005).length < 2 ^ (prefixWord ++ tailWord_5911005).sum := by decide
  have hdescent : baseEnd_5911005 < baseStart_5911005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911029 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5911029 : Nat := 118140960795 + 5911029 * 2 ^ 59
def prefixEnd_5911029 : Nat := 4983230072969 + 3 ^ 40 * 5911029 * 2
def baseEnd_5911029 : Nat := 3035199039665458805553179

theorem tailTrace_5911029 : CollatzResearch.WordTrace tailWord_5911029 prefixEnd_5911029 3035199039665458805553179 := by
  unfold tailWord_5911029
  simp only [CollatzResearch.WordTrace]
  refine ⟨215592939302358931226048141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143728626201572620817365427 215592939302358931226048141)
  ·
    refine ⟨80847352238384599209768053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215592939302358931226048141 80847352238384599209768053)
    ·
      refine ⟨7579439272348556175915755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80847352238384599209768053 7579439272348556175915755)
      ·
        refine ⟨11369158908522834263873633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579439272348556175915755 11369158908522834263873633)
        ·
          refine ⟨8526869181392125697905225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11369158908522834263873633 8526869181392125697905225)
          ·
            refine ⟨6395151886044094273428919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8526869181392125697905225 6395151886044094273428919)
            ·
              refine ⟨9592727829066141410143379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395151886044094273428919 9592727829066141410143379)
              ·
                refine ⟨14389091743599212115215069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9592727829066141410143379 14389091743599212115215069)
                ·
                  refine ⟨5395909403849704543205651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14389091743599212115215069 5395909403849704543205651)
                  ·
                    refine ⟨8093864105774556814808477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5395909403849704543205651 8093864105774556814808477)
                    ·
                      refine ⟨3035199039665458805553179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093864105774556814808477 3035199039665458805553179)
                      ·
                        rfl

theorem cell23_5911029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5911029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911029 prefixEnd_5911029 := by exact prefixLift 5911029
  have htrace : WordTrace (prefixWord ++ tailWord_5911029) baseStart_5911029 baseEnd_5911029 := by
    simpa [prefixWord, tailWord_5911029, baseEnd_5911029] using wordTrace_append hprefix tailTrace_5911029
  have hstable : (prefixWord ++ tailWord_5911029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911029).length < 2 ^ (prefixWord ++ tailWord_5911029).sum := by decide
  have hdescent : baseEnd_5911029 < baseStart_5911029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911041 : List Nat := [1, 2, 4, 1, 3, 1, 1, 10]
def baseStart_5911041 : Nat := 118140960795 + 5911041 * 2 ^ 59
def prefixEnd_5911041 : Nat := 4983230072969 + 3 ^ 40 * 5911041 * 2
def baseEnd_5911041 : Nat := 112415007460493065133449

theorem tailTrace_5911041 : CollatzResearch.WordTrace tailWord_5911041 prefixEnd_5911041 112415007460493065133449 := by
  unfold tailWord_5911041
  simp only [CollatzResearch.WordTrace]
  refine ⟨215593376978315457275484977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143728917985543638183656651 215593376978315457275484977)
  ·
    refine ⟨161695032733736592956613733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215593376978315457275484977 161695032733736592956613733)
    ·
      refine ⟨30317818637575611179365075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161695032733736592956613733 30317818637575611179365075)
      ·
        refine ⟨45476727956363416769047613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30317818637575611179365075 45476727956363416769047613)
        ·
          refine ⟨17053772983636281288392855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45476727956363416769047613 17053772983636281288392855)
          ·
            refine ⟨25580659475454421932589283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17053772983636281288392855 25580659475454421932589283)
            ·
              refine ⟨38370989213181632898883925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25580659475454421932589283 38370989213181632898883925)
              ·
                refine ⟨112415007460493065133449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38370989213181632898883925 112415007460493065133449)
                ·
                  rfl

theorem cell23_5911041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 10].length) (baseStart_5911041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911041 prefixEnd_5911041 := by exact prefixLift 5911041
  have htrace : WordTrace (prefixWord ++ tailWord_5911041) baseStart_5911041 baseEnd_5911041 := by
    simpa [prefixWord, tailWord_5911041, baseEnd_5911041] using wordTrace_append hprefix tailTrace_5911041
  have hstable : (prefixWord ++ tailWord_5911041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911041).length < 2 ^ (prefixWord ++ tailWord_5911041).sum := by decide
  have hdescent : baseEnd_5911041 < baseStart_5911041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911045 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_5911045 : Nat := 118140960795 + 5911045 * 2 ^ 59
def prefixEnd_5911045 : Nat := 4983230072969 + 3 ^ 40 * 5911045 * 2
def baseEnd_5911045 : Nat := 1011735751785310247651035

theorem tailTrace_5911045 : CollatzResearch.WordTrace tailWord_5911045 prefixEnd_5911045 1011735751785310247651035 := by
  unfold tailWord_5911045
  simp only [CollatzResearch.WordTrace]
  refine ⟨215593522870300965958630589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143729015246867310639087059 215593522870300965958630589)
  ·
    refine ⟨80847571076362862234486471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215593522870300965958630589 80847571076362862234486471)
    ·
      refine ⟨121271356614544293351729707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80847571076362862234486471 121271356614544293351729707)
      ·
        refine ⟨181907034921816440027594561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121271356614544293351729707 181907034921816440027594561)
        ·
          refine ⟨136430276191362330020695921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181907034921816440027594561 136430276191362330020695921)
          ·
            refine ⟨102322707143521747515521941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136430276191362330020695921 102322707143521747515521941)
            ·
              refine ⟨4796376897352581914790091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102322707143521747515521941 4796376897352581914790091)
              ·
                refine ⟨7194565346028872872185137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796376897352581914790091 7194565346028872872185137)
                ·
                  refine ⟨5395924009521654654138853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7194565346028872872185137 5395924009521654654138853)
                  ·
                    refine ⟨1011735751785310247651035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395924009521654654138853 1011735751785310247651035)
                    ·
                      rfl

theorem cell23_5911045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_5911045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911045 prefixEnd_5911045 := by exact prefixLift 5911045
  have htrace : WordTrace (prefixWord ++ tailWord_5911045) baseStart_5911045 baseEnd_5911045 := by
    simpa [prefixWord, tailWord_5911045, baseEnd_5911045] using wordTrace_append hprefix tailTrace_5911045
  have hstable : (prefixWord ++ tailWord_5911045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911045).length < 2 ^ (prefixWord ++ tailWord_5911045).sum := by decide
  have hdescent : baseEnd_5911045 < baseStart_5911045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911068 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5911068 : Nat := 118140960795 + 5911068 * 2 ^ 59
def prefixEnd_5911068 : Nat := 4983230072969 + 3 ^ 40 * 5911068 * 2
def baseEnd_5911068 : Nat := 3035219065410984152965499

theorem tailTrace_5911068 : CollatzResearch.WordTrace tailWord_5911068 prefixEnd_5911068 3035219065410984152965499 := by
  unfold tailWord_5911068
  simp only [CollatzResearch.WordTrace]
  refine ⟨107797180874608820443358929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143729574499478427257811905 107797180874608820443358929)
  ·
    refine ⟨80847885655956615332519197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107797180874608820443358929 80847885655956615332519197)
    ·
      refine ⟨30317957120983730749694699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80847885655956615332519197 30317957120983730749694699)
      ·
        refine ⟨45476935681475596124542049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30317957120983730749694699 45476935681475596124542049)
        ·
          refine ⟨34107701761106697093406537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45476935681475596124542049 34107701761106697093406537)
          ·
            refine ⟨25580776320830022820054903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34107701761106697093406537 25580776320830022820054903)
            ·
              refine ⟨38371164481245034230082355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25580776320830022820054903 38371164481245034230082355)
              ·
                refine ⟨57556746721867551345123533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38371164481245034230082355 57556746721867551345123533)
                ·
                  refine ⟨21583780020700331754421325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57556746721867551345123533 21583780020700331754421325)
                  ·
                    refine ⟨8093917507762624407907997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21583780020700331754421325 8093917507762624407907997)
                    ·
                      refine ⟨3035219065410984152965499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8093917507762624407907997 3035219065410984152965499)
                      ·
                        rfl

theorem cell23_5911068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5911068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911068 prefixEnd_5911068 := by exact prefixLift 5911068
  have htrace : WordTrace (prefixWord ++ tailWord_5911068) baseStart_5911068 baseEnd_5911068 := by
    simpa [prefixWord, tailWord_5911068, baseEnd_5911068] using wordTrace_append hprefix tailTrace_5911068
  have hstable : (prefixWord ++ tailWord_5911068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911068).length < 2 ^ (prefixWord ++ tailWord_5911068).sum := by decide
  have hdescent : baseEnd_5911068 < baseStart_5911068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911072 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5911072 : Nat := 118140960795 + 5911072 * 2 ^ 59
def prefixEnd_5911072 : Nat := 4983230072969 + 3 ^ 40 * 5911072 * 2
def baseEnd_5911072 : Nat := 3035221119333602137315481

theorem tailTrace_5911072 : CollatzResearch.WordTrace tailWord_5911072 prefixEnd_5911072 3035221119333602137315481 := by
  unfold tailWord_5911072
  simp only [CollatzResearch.WordTrace]
  refine ⟨107797253820601574784931735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143729671760802099713242313 107797253820601574784931735)
  ·
    refine ⟨161695880730902362177397603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107797253820601574784931735 161695880730902362177397603)
    ·
      refine ⟨242543821096353543266096405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161695880730902362177397603 242543821096353543266096405)
      ·
        refine ⟨11369241613891572340598269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 242543821096353543266096405 11369241613891572340598269)
        ·
          refine ⟨4263465605209339627724351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11369241613891572340598269 4263465605209339627724351)
          ·
            refine ⟨6395198407814009441586527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263465605209339627724351 6395198407814009441586527)
            ·
              refine ⟨9592797611721014162379791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395198407814009441586527 9592797611721014162379791)
              ·
                refine ⟨14389196417581521243569687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9592797611721014162379791 14389196417581521243569687)
                ·
                  refine ⟨21583794626372281865354531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14389196417581521243569687 21583794626372281865354531)
                  ·
                    refine ⟨32375691939558422798031797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21583794626372281865354531 32375691939558422798031797)
                    ·
                      refine ⟨3035221119333602137315481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32375691939558422798031797 3035221119333602137315481)
                      ·
                        rfl

theorem cell23_5911072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5911072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911072 prefixEnd_5911072 := by exact prefixLift 5911072
  have htrace : WordTrace (prefixWord ++ tailWord_5911072) baseStart_5911072 baseEnd_5911072 := by
    simpa [prefixWord, tailWord_5911072, baseEnd_5911072] using wordTrace_append hprefix tailTrace_5911072
  have hstable : (prefixWord ++ tailWord_5911072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911072).length < 2 ^ (prefixWord ++ tailWord_5911072).sum := by decide
  have hdescent : baseEnd_5911072 < baseStart_5911072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911079 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5911079 : Nat := 118140960795 + 5911079 * 2 ^ 59
def prefixEnd_5911079 : Nat := 4983230072969 + 3 ^ 40 * 5911079 * 2
def baseEnd_5911079 : Nat := 1011741571232727869975983

theorem tailTrace_5911079 : CollatzResearch.WordTrace tailWord_5911079 prefixEnd_5911079 1011741571232727869975983 := by
  unfold tailWord_5911079
  simp only [CollatzResearch.WordTrace]
  refine ⟨215594762952177789765368291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143729841968118526510245527 215594762952177789765368291)
  ·
    refine ⟨323392144428266684648052437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215594762952177789765368291 323392144428266684648052437)
    ·
      refine ⟨7579503385037500421438729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 323392144428266684648052437 7579503385037500421438729)
      ·
        refine ⟨5684627538778125316079047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579503385037500421438729 5684627538778125316079047)
        ·
          refine ⟨8526941308167187974118571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684627538778125316079047 8526941308167187974118571)
          ·
            refine ⟨12790411962250781961177857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526941308167187974118571 12790411962250781961177857)
            ·
              refine ⟨9592808971688086470883393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12790411962250781961177857 9592808971688086470883393)
              ·
                refine ⟨7194606728766064853162545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9592808971688086470883393 7194606728766064853162545)
                ·
                  refine ⟨5395955046574548639871909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7194606728766064853162545 5395955046574548639871909)
                  ·
                    refine ⟨1011741571232727869975983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5395955046574548639871909 1011741571232727869975983)
                    ·
                      rfl

theorem cell23_5911079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5911079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911079 prefixEnd_5911079 := by exact prefixLift 5911079
  have htrace : WordTrace (prefixWord ++ tailWord_5911079) baseStart_5911079 baseEnd_5911079 := by
    simpa [prefixWord, tailWord_5911079, baseEnd_5911079] using wordTrace_append hprefix tailTrace_5911079
  have hstable : (prefixWord ++ tailWord_5911079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911079).length < 2 ^ (prefixWord ++ tailWord_5911079).sum := by decide
  have hdescent : baseEnd_5911079 < baseStart_5911079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911086 : List Nat := [4, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_5911086 : Nat := 118140960795 + 5911086 * 2 ^ 59
def prefixEnd_5911086 : Nat := 4983230072969 + 3 ^ 40 * 5911086 * 2
def baseEnd_5911086 : Nat := 3035228308062765082540417

theorem tailTrace_5911086 : CollatzResearch.WordTrace tailWord_5911086 prefixEnd_5911086 3035228308062765082540417 := by
  unfold tailWord_5911086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26949377282894053745109139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143730012175434953307248741 26949377282894053745109139)
  ·
    refine ⟨40424065924341080617663709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26949377282894053745109139 40424065924341080617663709)
    ·
      refine ⟨15159024721627905231623891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40424065924341080617663709 15159024721627905231623891)
      ·
        refine ⟨22738537082441857847435837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15159024721627905231623891 22738537082441857847435837)
        ·
          refine ⟨8526951405915696692788439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22738537082441857847435837 8526951405915696692788439)
          ·
            refine ⟨12790427108873545039182659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8526951405915696692788439 12790427108873545039182659)
            ·
              refine ⟨19185640663310317558773989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12790427108873545039182659 19185640663310317558773989)
              ·
                refine ⟨3597307624370684542270123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19185640663310317558773989 3597307624370684542270123)
                ·
                  refine ⟨5395961436556026813405185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597307624370684542270123 5395961436556026813405185)
                  ·
                    refine ⟨4046971077417020110053889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5395961436556026813405185 4046971077417020110053889)
                    ·
                      refine ⟨3035228308062765082540417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046971077417020110053889 3035228308062765082540417)
                      ·
                        rfl

theorem cell23_5911086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_5911086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911086 prefixEnd_5911086 := by exact prefixLift 5911086
  have htrace : WordTrace (prefixWord ++ tailWord_5911086) baseStart_5911086 baseEnd_5911086 := by
    simpa [prefixWord, tailWord_5911086, baseEnd_5911086] using wordTrace_append hprefix tailTrace_5911086
  have hstable : (prefixWord ++ tailWord_5911086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911086).length < 2 ^ (prefixWord ++ tailWord_5911086).sum := by decide
  have hdescent : baseEnd_5911086 < baseStart_5911086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911091 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_5911091 : Nat := 118140960795 + 5911091 * 2 ^ 59
def prefixEnd_5911091 : Nat := 4983230072969 + 3 ^ 40 * 5911091 * 2
def baseEnd_5911091 : Nat := 3035230875466037562977893

theorem tailTrace_5911091 : CollatzResearch.WordTrace tailWord_5911091 prefixEnd_5911091 3035230875466037562977893 := by
  unfold tailWord_5911091
  simp only [CollatzResearch.WordTrace]
  refine ⟨215595200628134315814805127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143730133752089543876536751 215595200628134315814805127)
  ·
    refine ⟨323392800942201473722207691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215595200628134315814805127 323392800942201473722207691)
    ·
      refine ⟨485089201413302210583311537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323392800942201473722207691 485089201413302210583311537)
      ·
        refine ⟨363816901059976657937483653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485089201413302210583311537 363816901059976657937483653)
        ·
          refine ⟨68215668948745623363278185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363816901059976657937483653 68215668948745623363278185)
          ·
            refine ⟨51161751711559217522458639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68215668948745623363278185 51161751711559217522458639)
            ·
              refine ⟨76742627567338826283687959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51161751711559217522458639 76742627567338826283687959)
              ·
                refine ⟨115113941351008239425531939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76742627567338826283687959 115113941351008239425531939)
                ·
                  refine ⟨172670912026512359138297909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115113941351008239425531939 172670912026512359138297909)
                  ·
                    refine ⟨16187898002485533669215429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172670912026512359138297909 16187898002485533669215429)
                    ·
                      refine ⟨3035230875466037562977893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16187898002485533669215429 3035230875466037562977893)
                      ·
                        rfl

theorem cell23_5911091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_5911091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911091 prefixEnd_5911091 := by exact prefixLift 5911091
  have htrace : WordTrace (prefixWord ++ tailWord_5911091) baseStart_5911091 baseEnd_5911091 := by
    simpa [prefixWord, tailWord_5911091, baseEnd_5911091] using wordTrace_append hprefix tailTrace_5911091
  have hstable : (prefixWord ++ tailWord_5911091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911091).length < 2 ^ (prefixWord ++ tailWord_5911091).sum := by decide
  have hdescent : baseEnd_5911091 < baseStart_5911091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911092 : List Nat := [2, 5, 1, 3, 1, 2, 1, 8]
def baseStart_5911092 : Nat := 118140960795 + 5911092 * 2 ^ 59
def prefixEnd_5911092 : Nat := 4983230072969 + 3 ^ 40 * 5911092 * 2
def baseEnd_5911092 : Nat := 112415977368396002187607

theorem tailTrace_5911092 : CollatzResearch.WordTrace tailWord_5911092 prefixEnd_5911092 112415977368396002187607 := by
  unfold tailWord_5911092
  simp only [CollatzResearch.WordTrace]
  refine ⟨107797618550565346492795765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143730158067420461990394353 107797618550565346492795765)
  ·
    refine ⟨10106026739115501233699603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107797618550565346492795765 10106026739115501233699603)
    ·
      refine ⟨15159040108673251850549405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10106026739115501233699603 15159040108673251850549405)
      ·
        refine ⟨5684640040752469443956027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15159040108673251850549405 5684640040752469443956027)
        ·
          refine ⟨8526960061128704165934041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684640040752469443956027 8526960061128704165934041)
          ·
            refine ⟨6395220045846528124450531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8526960061128704165934041 6395220045846528124450531)
            ·
              refine ⟨9592830068769792186675797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395220045846528124450531 9592830068769792186675797)
              ·
                refine ⟨112415977368396002187607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9592830068769792186675797 112415977368396002187607)
                ·
                  rfl

theorem cell23_5911092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 8].length) (baseStart_5911092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911092 prefixEnd_5911092 := by exact prefixLift 5911092
  have htrace : WordTrace (prefixWord ++ tailWord_5911092) baseStart_5911092 baseEnd_5911092 := by
    simpa [prefixWord, tailWord_5911092, baseEnd_5911092] using wordTrace_append hprefix tailTrace_5911092
  have hstable : (prefixWord ++ tailWord_5911092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911092).length < 2 ^ (prefixWord ++ tailWord_5911092).sum := by decide
  have hdescent : baseEnd_5911092 < baseStart_5911092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911125 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5911125 : Nat := 118140960795 + 5911125 * 2 ^ 59
def prefixEnd_5911125 : Nat := 4983230072969 + 3 ^ 40 * 5911125 * 2
def baseEnd_5911125 : Nat := 3035248333808290429952737

theorem tailTrace_5911125 : CollatzResearch.WordTrace tailWord_5911125 prefixEnd_5911125 3035248333808290429952737 := by
  unfold tailWord_5911125
  simp only [CollatzResearch.WordTrace]
  refine ⟨215596440710011139621542829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143730960473340759747695219 215596440710011139621542829)
  ·
    refine ⟨80848665266254177358078561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215596440710011139621542829 80848665266254177358078561)
    ·
      refine ⟨60636498949690633018558921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80848665266254177358078561 60636498949690633018558921)
      ·
        refine ⟨45477374212267974763919191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60636498949690633018558921 45477374212267974763919191)
        ·
          refine ⟨68216061318401962145878787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45477374212267974763919191 68216061318401962145878787)
          ·
            refine ⟨102324091977602943218818181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68216061318401962145878787 102324091977602943218818181)
            ·
              refine ⟨19185767245800551853528409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102324091977602943218818181 19185767245800551853528409)
              ·
                refine ⟨14389325434350413890146307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19185767245800551853528409 14389325434350413890146307)
                ·
                  refine ⟨21583988151525620835219461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14389325434350413890146307 21583988151525620835219461)
                  ·
                    refine ⟨4046997778411053906603649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21583988151525620835219461 4046997778411053906603649)
                    ·
                      refine ⟨3035248333808290429952737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4046997778411053906603649 3035248333808290429952737)
                      ·
                        rfl

theorem cell23_5911125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5911125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911125 prefixEnd_5911125 := by exact prefixLift 5911125
  have htrace : WordTrace (prefixWord ++ tailWord_5911125) baseStart_5911125 baseEnd_5911125 := by
    simpa [prefixWord, tailWord_5911125, baseEnd_5911125] using wordTrace_append hprefix tailTrace_5911125
  have hstable : (prefixWord ++ tailWord_5911125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911125).length < 2 ^ (prefixWord ++ tailWord_5911125).sum := by decide
  have hdescent : baseEnd_5911125 < baseStart_5911125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911210 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5911210 : Nat := 118140960795 + 5911210 * 2 ^ 59
def prefixEnd_5911210 : Nat := 4983230072969 + 3 ^ 40 * 5911210 * 2
def baseEnd_5911210 : Nat := 3035291979663922597389847

theorem tailTrace_5911210 : CollatzResearch.WordTrace tailWord_5911210 prefixEnd_5911210 3035291979663922597389847 := by
  unfold tailWord_5911210
  simp only [CollatzResearch.WordTrace]
  refine ⟨53899885228675799784596771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143733027276468799425591389 53899885228675799784596771)
  ·
    refine ⟨80849827843013699676895157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53899885228675799784596771 80849827843013699676895157)
    ·
      refine ⟨7579671360282534344708921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80849827843013699676895157 7579671360282534344708921)
      ·
        refine ⟨5684753520211900758531691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579671360282534344708921 5684753520211900758531691)
        ·
          refine ⟨8527130280317851137797537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5684753520211900758531691 8527130280317851137797537)
          ·
            refine ⟨6395347710238388353348153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8527130280317851137797537 6395347710238388353348153)
            ·
              refine ⟨4796510782678791265011115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6395347710238388353348153 4796510782678791265011115)
              ·
                refine ⟨7194766174018186897516673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796510782678791265011115 7194766174018186897516673)
                ·
                  refine ⟨5396074630513640173137505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7194766174018186897516673 5396074630513640173137505)
                  ·
                    refine ⟨4047055972885230129853129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396074630513640173137505 4047055972885230129853129)
                    ·
                      refine ⟨3035291979663922597389847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047055972885230129853129 3035291979663922597389847)
                      ·
                        rfl

theorem cell23_5911210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5911210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911210 prefixEnd_5911210 := by exact prefixLift 5911210
  have htrace : WordTrace (prefixWord ++ tailWord_5911210) baseStart_5911210 baseEnd_5911210 := by
    simpa [prefixWord, tailWord_5911210, baseEnd_5911210] using wordTrace_append hprefix tailTrace_5911210
  have hstable : (prefixWord ++ tailWord_5911210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911210).length < 2 ^ (prefixWord ++ tailWord_5911210).sum := by decide
  have hdescent : baseEnd_5911210 < baseStart_5911210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911248 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_5911248 : Nat := 118140960795 + 5911248 * 2 ^ 59
def prefixEnd_5911248 : Nat := 4983230072969 + 3 ^ 40 * 5911248 * 2
def baseEnd_5911248 : Nat := 3035311491928793448714671

theorem tailTrace_5911248 : CollatzResearch.WordTrace tailWord_5911248 prefixEnd_5911248 3035311491928793448714671 := by
  unfold tailWord_5911248
  simp only [CollatzResearch.WordTrace]
  refine ⟨107800463444282765814135199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143733951259043687752180265 107800463444282765814135199)
  ·
    refine ⟨161700695166424148721202799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107800463444282765814135199 161700695166424148721202799)
    ·
      refine ⟨242551042749636223081804199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161700695166424148721202799 242551042749636223081804199)
      ·
        refine ⟨363826564124454334622706299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242551042749636223081804199 363826564124454334622706299)
        ·
          refine ⟨545739846186681501934059449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363826564124454334622706299 545739846186681501934059449)
          ·
            refine ⟨409304884640011126450544587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545739846186681501934059449 409304884640011126450544587)
            ·
              refine ⟨613957326960016689675816881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409304884640011126450544587 613957326960016689675816881)
              ·
                refine ⟨460467995220012517256862661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613957326960016689675816881 460467995220012517256862661)
                ·
                  refine ⟨86337749103752346985661749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 460467995220012517256862661 86337749103752346985661749)
                  ·
                    refine ⟨8094163978476782529905789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86337749103752346985661749 8094163978476782529905789)
                    ·
                      refine ⟨3035311491928793448714671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094163978476782529905789 3035311491928793448714671)
                      ·
                        rfl

theorem cell23_5911248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_5911248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911248 prefixEnd_5911248 := by exact prefixLift 5911248
  have htrace : WordTrace (prefixWord ++ tailWord_5911248) baseStart_5911248 baseEnd_5911248 := by
    simpa [prefixWord, tailWord_5911248, baseEnd_5911248] using wordTrace_append hprefix tailTrace_5911248
  have hstable : (prefixWord ++ tailWord_5911248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911248).length < 2 ^ (prefixWord ++ tailWord_5911248).sum := by decide
  have hdescent : baseEnd_5911248 < baseStart_5911248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911255 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 6]
def baseStart_5911255 : Nat := 118140960795 + 5911255 * 2 ^ 59
def prefixEnd_5911255 : Nat := 4983230072969 + 3 ^ 40 * 5911255 * 2
def baseEnd_5911255 : Nat := 337257231810374991258571

theorem tailTrace_5911255 : CollatzResearch.WordTrace tailWord_5911255 prefixEnd_5911255 337257231810374991258571 := by
  unfold tailWord_5911255
  simp only [CollatzResearch.WordTrace]
  refine ⟨215601182199540171823775219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143734121466360114549183479 215601182199540171823775219)
  ·
    refine ⟨323401773299310257735662829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215601182199540171823775219 323401773299310257735662829)
    ·
      refine ⟨121275664987241346650873561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323401773299310257735662829 121275664987241346650873561)
      ·
        refine ⟨90956748740431009988155171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121275664987241346650873561 90956748740431009988155171)
        ·
          refine ⟨136435123110646514982232757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90956748740431009988155171 136435123110646514982232757)
          ·
            refine ⟨12790792791623110779584321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136435123110646514982232757 12790792791623110779584321)
            ·
              refine ⟨9593094593717333084688241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12790792791623110779584321 9593094593717333084688241)
              ·
                refine ⟨7194820945287999813516181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9593094593717333084688241 7194820945287999813516181)
                ·
                  refine ⟨337257231810374991258571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7194820945287999813516181 337257231810374991258571)
                  ·
                    rfl

theorem cell23_5911255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 6].length) (baseStart_5911255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911255 prefixEnd_5911255 := by exact prefixLift 5911255
  have htrace : WordTrace (prefixWord ++ tailWord_5911255) baseStart_5911255 baseEnd_5911255 := by
    simpa [prefixWord, tailWord_5911255, baseEnd_5911255] using wordTrace_append hprefix tailTrace_5911255
  have hstable : (prefixWord ++ tailWord_5911255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911255).length < 2 ^ (prefixWord ++ tailWord_5911255).sum := by decide
  have hdescent : baseEnd_5911255 < baseStart_5911255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911258 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_5911258 : Nat := 118140960795 + 5911258 * 2 ^ 59
def prefixEnd_5911258 : Nat := 4983230072969 + 3 ^ 40 * 5911258 * 2
def baseEnd_5911258 : Nat := 3035316626735338409589625

theorem tailTrace_5911258 : CollatzResearch.WordTrace tailWord_5911258 prefixEnd_5911258 3035316626735338409589625 := by
  unfold tailWord_5911258
  simp only [CollatzResearch.WordTrace]
  refine ⟨53900322904632325834033607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143734194412352868890756285 53900322904632325834033607)
  ·
    refine ⟨80850484356948488751050411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53900322904632325834033607 80850484356948488751050411)
    ·
      refine ⟨121275726535422733126575617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80850484356948488751050411 121275726535422733126575617)
      ·
        refine ⟨90956794901567049844931713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121275726535422733126575617 90956794901567049844931713)
        ·
          refine ⟨68217596176175287383698785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90956794901567049844931713 68217596176175287383698785)
          ·
            refine ⟨51163197132131465537774089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68217596176175287383698785 51163197132131465537774089)
            ·
              refine ⟨38372397849098599153330567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51163197132131465537774089 38372397849098599153330567)
              ·
                refine ⟨57558596773647898729995851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38372397849098599153330567 57558596773647898729995851)
                ·
                  refine ⟨86337895160471848094993777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57558596773647898729995851 86337895160471848094993777)
                  ·
                    refine ⟨64753421370353886071245333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86337895160471848094993777 64753421370353886071245333)
                    ·
                      refine ⟨3035316626735338409589625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64753421370353886071245333 3035316626735338409589625)
                      ·
                        rfl

theorem cell23_5911258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_5911258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911258 prefixEnd_5911258 := by exact prefixLift 5911258
  have htrace : WordTrace (prefixWord ++ tailWord_5911258) baseStart_5911258 baseEnd_5911258 := by
    simpa [prefixWord, tailWord_5911258, baseEnd_5911258] using wordTrace_append hprefix tailTrace_5911258
  have hstable : (prefixWord ++ tailWord_5911258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911258).length < 2 ^ (prefixWord ++ tailWord_5911258).sum := by decide
  have hdescent : baseEnd_5911258 < baseStart_5911258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911275 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 5, 2]
def baseStart_5911275 : Nat := 118140960795 + 5911275 * 2 ^ 59
def prefixEnd_5911275 : Nat := 4983230072969 + 3 ^ 40 * 5911275 * 2
def baseEnd_5911275 : Nat := 3035325355906464843077047

theorem tailTrace_5911275 : CollatzResearch.WordTrace tailWord_5911275 prefixEnd_5911275 3035325355906464843077047 := by
  unfold tailWord_5911275
  simp only [CollatzResearch.WordTrace]
  refine ⟨215601911659467715239503279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143734607772978476826335519 215601911659467715239503279)
  ·
    refine ⟨323402867489201572859254919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215601911659467715239503279 323402867489201572859254919)
    ·
      refine ⟨485104301233802359288882379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323402867489201572859254919 485104301233802359288882379)
      ·
        refine ⟨727656451850703538933323569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485104301233802359288882379 727656451850703538933323569)
        ·
          refine ⟨545742338888027654199992677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727656451850703538933323569 545742338888027654199992677)
          ·
            refine ⟨102326688541505185162498627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 545742338888027654199992677 102326688541505185162498627)
            ·
              refine ⟨153490032812257777743747941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102326688541505185162498627 153490032812257777743747941)
              ·
                refine ⟨28779381152298333326952739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153490032812257777743747941 28779381152298333326952739)
                ·
                  refine ⟨43169071728447499990429109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28779381152298333326952739 43169071728447499990429109)
                  ·
                    refine ⟨4047100474541953124102729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43169071728447499990429109 4047100474541953124102729)
                    ·
                      refine ⟨3035325355906464843077047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047100474541953124102729 3035325355906464843077047)
                      ·
                        rfl

theorem cell23_5911275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 5, 2].length) (baseStart_5911275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911275 prefixEnd_5911275 := by exact prefixLift 5911275
  have htrace : WordTrace (prefixWord ++ tailWord_5911275) baseStart_5911275 baseEnd_5911275 := by
    simpa [prefixWord, tailWord_5911275, baseEnd_5911275] using wordTrace_append hprefix tailTrace_5911275
  have hstable : (prefixWord ++ tailWord_5911275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911275).length < 2 ^ (prefixWord ++ tailWord_5911275).sum := by decide
  have hdescent : baseEnd_5911275 < baseStart_5911275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911282 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_5911282 : Nat := 118140960795 + 5911282 * 2 ^ 59
def prefixEnd_5911282 : Nat := 4983230072969 + 3 ^ 40 * 5911282 * 2
def baseEnd_5911282 : Nat := 3035328950271046315689515

theorem tailTrace_5911282 : CollatzResearch.WordTrace tailWord_5911282 prefixEnd_5911282 3035328950271046315689515 := by
  unfold tailWord_5911282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53900541742610588858752025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143734777980294903623338733 53900541742610588858752025)
  ·
    refine ⟨40425406306957941644064019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53900541742610588858752025 40425406306957941644064019)
    ·
      refine ⟨60638109460436912466096029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40425406306957941644064019 60638109460436912466096029)
      ·
        refine ⟨22739291047663842174786011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60638109460436912466096029 22739291047663842174786011)
        ·
          refine ⟨34108936571495763262179017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22739291047663842174786011 34108936571495763262179017)
          ·
            refine ⟨25581702428621822446634263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34108936571495763262179017 25581702428621822446634263)
            ·
              refine ⟨38372553642932733669951395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25581702428621822446634263 38372553642932733669951395)
              ·
                refine ⟨57558830464399100504927093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38372553642932733669951395 57558830464399100504927093)
                ·
                  refine ⟨5396140356037415672336915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57558830464399100504927093 5396140356037415672336915)
                  ·
                    refine ⟨8094210534056123508505373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5396140356037415672336915 8094210534056123508505373)
                    ·
                      refine ⟨3035328950271046315689515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094210534056123508505373 3035328950271046315689515)
                      ·
                        rfl

theorem cell23_5911282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_5911282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911282 prefixEnd_5911282 := by exact prefixLift 5911282
  have htrace : WordTrace (prefixWord ++ tailWord_5911282) baseStart_5911282 baseEnd_5911282 := by
    simpa [prefixWord, tailWord_5911282, baseEnd_5911282] using wordTrace_append hprefix tailTrace_5911282
  have hstable : (prefixWord ++ tailWord_5911282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911282).length < 2 ^ (prefixWord ++ tailWord_5911282).sum := by decide
  have hdescent : baseEnd_5911282 < baseStart_5911282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911292 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_5911292 : Nat := 118140960795 + 5911292 * 2 ^ 59
def prefixEnd_5911292 : Nat := 4983230072969 + 3 ^ 40 * 5911292 * 2
def baseEnd_5911292 : Nat := 3035334085077591276564469

theorem tailTrace_5911292 : CollatzResearch.WordTrace tailWord_5911292 prefixEnd_5911292 3035334085077591276564469 := by
  unfold tailWord_5911292
  simp only [CollatzResearch.WordTrace]
  refine ⟨107801265850203063571436065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143735021133604084761914753 107801265850203063571436065)
  ·
    refine ⟨80850949387652297678577049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107801265850203063571436065 80850949387652297678577049)
    ·
      refine ⟨60638212040739223258932787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80850949387652297678577049 60638212040739223258932787)
      ·
        refine ⟨90957318061108834888399181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60638212040739223258932787 90957318061108834888399181)
        ·
          refine ⟨34108994272915813083149693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90957318061108834888399181 34108994272915813083149693)
          ·
            refine ⟨12790872852343429906181135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34108994272915813083149693 12790872852343429906181135)
            ·
              refine ⟨19186309278515144859271703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12790872852343429906181135 19186309278515144859271703)
              ·
                refine ⟨28779463917772717288907555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19186309278515144859271703 28779463917772717288907555)
                ·
                  refine ⟨43169195876659075933361333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28779463917772717288907555 43169195876659075933361333)
                  ·
                    refine ⟨4047112113436788368752625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43169195876659075933361333 4047112113436788368752625)
                    ·
                      refine ⟨3035334085077591276564469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047112113436788368752625 3035334085077591276564469)
                      ·
                        rfl

theorem cell23_5911292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_5911292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911292 prefixEnd_5911292 := by exact prefixLift 5911292
  have htrace : WordTrace (prefixWord ++ tailWord_5911292) baseStart_5911292 baseEnd_5911292 := by
    simpa [prefixWord, tailWord_5911292, baseEnd_5911292] using wordTrace_append hprefix tailTrace_5911292
  have hstable : (prefixWord ++ tailWord_5911292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911292).length < 2 ^ (prefixWord ++ tailWord_5911292).sum := by decide
  have hdescent : baseEnd_5911292 < baseStart_5911292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911315 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 4, 4]
def baseStart_5911315 : Nat := 118140960795 + 5911315 * 2 ^ 59
def prefixEnd_5911315 : Nat := 4983230072969 + 3 ^ 40 * 5911315 * 2
def baseEnd_5911315 : Nat := 1011781965044214895525621

theorem tailTrace_5911315 : CollatzResearch.WordTrace tailWord_5911315 prefixEnd_5911315 1011781965044214895525621 := by
  unfold tailWord_5911315
  simp only [CollatzResearch.WordTrace]
  refine ⟨215603370579322802070959399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143735580386215201380639599 215603370579322802070959399)
  ·
    refine ⟨323405055868984203106439099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215603370579322802070959399 323405055868984203106439099)
    ·
      refine ⟨485107583803476304659658649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323405055868984203106439099 485107583803476304659658649)
      ·
        refine ⟨363830687852607228494743987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485107583803476304659658649 363830687852607228494743987)
        ·
          refine ⟨545746031778910842742115981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363830687852607228494743987 545746031778910842742115981)
          ·
            refine ⟨204654761917091566028293493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 545746031778910842742115981 204654761917091566028293493)
            ·
              refine ⟨19186383929727334315152515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204654761917091566028293493 19186383929727334315152515)
              ·
                refine ⟨28779575894591001472728773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19186383929727334315152515 28779575894591001472728773)
                ·
                  refine ⟨5396170480235812776136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28779575894591001472728773 5396170480235812776136645)
                  ·
                    refine ⟨1011781965044214895525621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5396170480235812776136645 1011781965044214895525621)
                    ·
                      rfl

theorem cell23_5911315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 4].length) (baseStart_5911315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911315 prefixEnd_5911315 := by exact prefixLift 5911315
  have htrace : WordTrace (prefixWord ++ tailWord_5911315) baseStart_5911315 baseEnd_5911315 := by
    simpa [prefixWord, tailWord_5911315, baseEnd_5911315] using wordTrace_append hprefix tailTrace_5911315
  have hstable : (prefixWord ++ tailWord_5911315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911315).length < 2 ^ (prefixWord ++ tailWord_5911315).sum := by decide
  have hdescent : baseEnd_5911315 < baseStart_5911315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911350 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5911350 : Nat := 118140960795 + 5911350 * 2 ^ 59
def prefixEnd_5911350 : Nat := 4983230072969 + 3 ^ 40 * 5911350 * 2
def baseEnd_5911350 : Nat := 3035363866955552049639203

theorem tailTrace_5911350 : CollatzResearch.WordTrace tailWord_5911350 prefixEnd_5911350 3035363866955552049639203 := by
  unfold tailWord_5911350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13475290445887250190530219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143736431422797335365655669 13475290445887250190530219)
  ·
    refine ⟨20212935668830875285795329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13475290445887250190530219 20212935668830875285795329)
    ·
      refine ⟨15159701751623156464346497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20212935668830875285795329 15159701751623156464346497)
      ·
        refine ⟨11369776313717367348259873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15159701751623156464346497 11369776313717367348259873)
        ·
          refine ⟨8527332235288025511194905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11369776313717367348259873 8527332235288025511194905)
          ·
            refine ⟨6395499176466019133396179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8527332235288025511194905 6395499176466019133396179)
            ·
              refine ⟨9593248764699028700094269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395499176466019133396179 9593248764699028700094269)
              ·
                refine ⟨3597468286762135762535351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9593248764699028700094269 3597468286762135762535351)
                ·
                  refine ⟨5396202430143203643803027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597468286762135762535351 5396202430143203643803027)
                  ·
                    refine ⟨8094303645214805465704541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5396202430143203643803027 8094303645214805465704541)
                    ·
                      refine ⟨3035363866955552049639203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094303645214805465704541 3035363866955552049639203)
                      ·
                        rfl

theorem cell23_5911350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5911350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911350 prefixEnd_5911350 := by exact prefixLift 5911350
  have htrace : WordTrace (prefixWord ++ tailWord_5911350) baseStart_5911350 baseEnd_5911350 := by
    simpa [prefixWord, tailWord_5911350, baseEnd_5911350] using wordTrace_append hprefix tailTrace_5911350
  have hstable : (prefixWord ++ tailWord_5911350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911350).length < 2 ^ (prefixWord ++ tailWord_5911350).sum := by decide
  have hdescent : baseEnd_5911350 < baseStart_5911350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911399 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_5911399 : Nat := 118140960795 + 5911399 * 2 ^ 59
def prefixEnd_5911399 : Nat := 4983230072969 + 3 ^ 40 * 5911399 * 2
def baseEnd_5911399 : Nat := 3035389027507622357926477

theorem tailTrace_5911399 : CollatzResearch.WordTrace tailWord_5911399 prefixEnd_5911399 3035389027507622357926477 := by
  unfold tailWord_5911399
  simp only [CollatzResearch.WordTrace]
  refine ⟨215606434311018484417017251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143737622874012322944678167 215606434311018484417017251)
  ·
    refine ⟨323409651466527726625525877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215606434311018484417017251 323409651466527726625525877)
    ·
      refine ⟨30319654824986974371143051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323409651466527726625525877 30319654824986974371143051)
      ·
        refine ⟨45479482237480461556714577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30319654824986974371143051 45479482237480461556714577)
        ·
          refine ⟨34109611678110346167535933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45479482237480461556714577 34109611678110346167535933)
          ·
            refine ⟨12791104379291379812825975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34109611678110346167535933 12791104379291379812825975)
            ·
              refine ⟨19186656568937069719238963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12791104379291379812825975 19186656568937069719238963)
              ·
                refine ⟨28779984853405604578858445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19186656568937069719238963 28779984853405604578858445)
                ·
                  refine ⟨10792494320027101717071917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28779984853405604578858445 10792494320027101717071917)
                  ·
                    refine ⟨4047185370010163143901969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10792494320027101717071917 4047185370010163143901969)
                    ·
                      refine ⟨3035389027507622357926477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047185370010163143901969 3035389027507622357926477)
                      ·
                        rfl

theorem cell23_5911399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_5911399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911399 prefixEnd_5911399 := by exact prefixLift 5911399
  have htrace : WordTrace (prefixWord ++ tailWord_5911399) baseStart_5911399 baseEnd_5911399 := by
    simpa [prefixWord, tailWord_5911399, baseEnd_5911399] using wordTrace_append hprefix tailTrace_5911399
  have hstable : (prefixWord ++ tailWord_5911399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911399).length < 2 ^ (prefixWord ++ tailWord_5911399).sum := by decide
  have hdescent : baseEnd_5911399 < baseStart_5911399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911405 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_5911405 : Nat := 118140960795 + 5911405 * 2 ^ 59
def prefixEnd_5911405 : Nat := 4983230072969 + 3 ^ 40 * 5911405 * 2
def baseEnd_5911405 : Nat := 1011797369463849778150483

theorem tailTrace_5911405 : CollatzResearch.WordTrace tailWord_5911405 prefixEnd_5911405 1011797369463849778150483 := by
  unfold tailWord_5911405
  simp only [CollatzResearch.WordTrace]
  refine ⟨215606653148996747441735669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143737768765997831627823779 215606653148996747441735669)
  ·
    refine ⟨20213123732718445072662719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215606653148996747441735669 20213123732718445072662719)
    ·
      refine ⟨30319685599077667608994079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20213123732718445072662719 30319685599077667608994079)
      ·
        refine ⟨45479528398616501413491119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30319685599077667608994079 45479528398616501413491119)
        ·
          refine ⟨68219292597924752120236679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45479528398616501413491119 68219292597924752120236679)
          ·
            refine ⟨102328938896887128180355019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68219292597924752120236679 102328938896887128180355019)
            ·
              refine ⟨153493408345330692270532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102328938896887128180355019 153493408345330692270532529)
              ·
                refine ⟨115120056258998019202899397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153493408345330692270532529 115120056258998019202899397)
                ·
                  refine ⟨21585010548562128600543637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115120056258998019202899397 21585010548562128600543637)
                  ·
                    refine ⟨1011797369463849778150483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21585010548562128600543637 1011797369463849778150483)
                    ·
                      rfl

theorem cell23_5911405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_5911405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911405 prefixEnd_5911405 := by exact prefixLift 5911405
  have htrace : WordTrace (prefixWord ++ tailWord_5911405) baseStart_5911405 baseEnd_5911405 := by
    simpa [prefixWord, tailWord_5911405, baseEnd_5911405] using wordTrace_append hprefix tailTrace_5911405
  have hstable : (prefixWord ++ tailWord_5911405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911405).length < 2 ^ (prefixWord ++ tailWord_5911405).sum := by decide
  have hdescent : baseEnd_5911405 < baseStart_5911405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911415 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_5911415 : Nat := 118140960795 + 5911415 * 2 ^ 59
def prefixEnd_5911415 : Nat := 4983230072969 + 3 ^ 40 * 5911415 * 2
def baseEnd_5911415 : Nat := 3035397243198094295326403

theorem tailTrace_5911415 : CollatzResearch.WordTrace tailWord_5911415 prefixEnd_5911415 3035397243198094295326403 := by
  unfold tailWord_5911415
  simp only [CollatzResearch.WordTrace]
  refine ⟨215607017878960519149599699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143738011919307012766399799 215607017878960519149599699)
  ·
    refine ⟨323410526818440778724399549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215607017878960519149599699 323410526818440778724399549)
    ·
      refine ⟨121278947556915292021649831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323410526818440778724399549 121278947556915292021649831)
      ·
        refine ⟨181918421335372938032474747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121278947556915292021649831 181918421335372938032474747)
        ·
          refine ⟨272877632003059407048712121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181918421335372938032474747 272877632003059407048712121)
          ·
            refine ⟨204658224002294555286534091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272877632003059407048712121 204658224002294555286534091)
            ·
              refine ⟨306987336003441832929801137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204658224002294555286534091 306987336003441832929801137)
              ·
                refine ⟨230240502002581374697350853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306987336003441832929801137 230240502002581374697350853)
                ·
                  refine ⟨43170094125484007755753285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230240502002581374697350853 43170094125484007755753285)
                  ·
                    refine ⟨8094392648528251454203741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43170094125484007755753285 8094392648528251454203741)
                    ·
                      refine ⟨3035397243198094295326403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094392648528251454203741 3035397243198094295326403)
                      ·
                        rfl

theorem cell23_5911415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_5911415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911415 prefixEnd_5911415 := by exact prefixLift 5911415
  have htrace : WordTrace (prefixWord ++ tailWord_5911415) baseStart_5911415 baseEnd_5911415 := by
    simpa [prefixWord, tailWord_5911415, baseEnd_5911415] using wordTrace_append hprefix tailTrace_5911415
  have hstable : (prefixWord ++ tailWord_5911415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911415).length < 2 ^ (prefixWord ++ tailWord_5911415).sum := by decide
  have hdescent : baseEnd_5911415 < baseStart_5911415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911432 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5911432 : Nat := 118140960795 + 5911432 * 2 ^ 59
def prefixEnd_5911432 : Nat := 4983230072969 + 3 ^ 40 * 5911432 * 2
def baseEnd_5911432 : Nat := 3035405972369220728813825

theorem tailTrace_5911432 : CollatzResearch.WordTrace tailWord_5911432 prefixEnd_5911432 3035405972369220728813825 := by
  unfold tailWord_5911432
  simp only [CollatzResearch.WordTrace]
  refine ⟨107803818959949465526484275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143738425279932620701979033 107803818959949465526484275)
  ·
    refine ⟨161705728439924198289726413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107803818959949465526484275 161705728439924198289726413)
    ·
      refine ⟨60639648164971574358647405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161705728439924198289726413 60639648164971574358647405)
      ·
        refine ⟨22739868061864340384492777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60639648164971574358647405 22739868061864340384492777)
        ·
          refine ⟨17054901046398255288369583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22739868061864340384492777 17054901046398255288369583)
          ·
            refine ⟨25582351569597382932554375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17054901046398255288369583 25582351569597382932554375)
            ·
              refine ⟨38373527354396074398831563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25582351569597382932554375 38373527354396074398831563)
              ·
                refine ⟨57560291031594111598247345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38373527354396074398831563 57560291031594111598247345)
                ·
                  refine ⟨43170218273695583698685509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57560291031594111598247345 43170218273695583698685509)
                  ·
                    refine ⟨8094415926317921943503533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43170218273695583698685509 8094415926317921943503533)
                    ·
                      refine ⟨3035405972369220728813825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094415926317921943503533 3035405972369220728813825)
                      ·
                        rfl

theorem cell23_5911432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5911432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911432 prefixEnd_5911432 := by exact prefixLift 5911432
  have htrace : WordTrace (prefixWord ++ tailWord_5911432) baseStart_5911432 baseEnd_5911432 := by
    simpa [prefixWord, tailWord_5911432, baseEnd_5911432] using wordTrace_append hprefix tailTrace_5911432
  have hstable : (prefixWord ++ tailWord_5911432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911432).length < 2 ^ (prefixWord ++ tailWord_5911432).sum := by decide
  have hdescent : baseEnd_5911432 < baseStart_5911432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911465 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_5911465 : Nat := 118140960795 + 5911465 * 2 ^ 59
def prefixEnd_5911465 : Nat := 4983230072969 + 3 ^ 40 * 5911465 * 2
def baseEnd_5911465 : Nat := 1011807639076939699900391

theorem tailTrace_5911465 : CollatzResearch.WordTrace tailWord_5911465 prefixEnd_5911465 1011807639076939699900391 := by
  unfold tailWord_5911465
  simp only [CollatzResearch.WordTrace]
  refine ⟨215608841528779377688919849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143739227685852918459279899 215608841528779377688919849)
  ·
    refine ⟨161706631146584533266689887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215608841528779377688919849 161706631146584533266689887)
    ·
      refine ⟨242559946719876799900034831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161706631146584533266689887 242559946719876799900034831)
      ·
        refine ⟨363839920079815199850052247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242559946719876799900034831 363839920079815199850052247)
        ·
          refine ⟨545759880119722799775078371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363839920079815199850052247 545759880119722799775078371)
          ·
            refine ⟨818639820179584199662617557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545759880119722799775078371 818639820179584199662617557)
            ·
              refine ⟨19186870785459004679592599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 818639820179584199662617557 19186870785459004679592599)
              ·
                refine ⟨28780306178188507019388899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19186870785459004679592599 28780306178188507019388899)
                ·
                  refine ⟨43170459267282760529083349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28780306178188507019388899 43170459267282760529083349)
                  ·
                    refine ⟨1011807639076939699900391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43170459267282760529083349 1011807639076939699900391)
                    ·
                      rfl

theorem cell23_5911465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_5911465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911465 prefixEnd_5911465 := by exact prefixLift 5911465
  have htrace : WordTrace (prefixWord ++ tailWord_5911465) baseStart_5911465 baseEnd_5911465 := by
    simpa [prefixWord, tailWord_5911465, baseEnd_5911465] using wordTrace_append hprefix tailTrace_5911465
  have hstable : (prefixWord ++ tailWord_5911465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911465).length < 2 ^ (prefixWord ++ tailWord_5911465).sum := by decide
  have hdescent : baseEnd_5911465 < baseStart_5911465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911475 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_5911475 : Nat := 118140960795 + 5911475 * 2 ^ 59
def prefixEnd_5911475 : Nat := 4983230072969 + 3 ^ 40 * 5911475 * 2
def baseEnd_5911475 : Nat := 3035428052037364060576127

theorem tailTrace_5911475 : CollatzResearch.WordTrace tailWord_5911475 prefixEnd_5911475 3035428052037364060576127 := by
  unfold tailWord_5911475
  simp only [CollatzResearch.WordTrace]
  refine ⟨215609206258743149396783879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143739470839162099597855919 215609206258743149396783879)
  ·
    refine ⟨323413809388114724095175819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215609206258743149396783879 323413809388114724095175819)
    ·
      refine ⟨485120714082172086142763729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323413809388114724095175819 485120714082172086142763729)
      ·
        refine ⟨363840535561629064607072797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485120714082172086142763729 363840535561629064607072797)
        ·
          refine ⟨136440200835610899227652299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363840535561629064607072797 136440200835610899227652299)
          ·
            refine ⟨204660301253416348841478449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136440200835610899227652299 204660301253416348841478449)
            ·
              refine ⟨153495225940062261631108837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204660301253416348841478449 153495225940062261631108837)
              ·
                refine ⟨28780354863761674055832907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153495225940062261631108837 28780354863761674055832907)
                ·
                  refine ⟨43170532295642511083749361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28780354863761674055832907 43170532295642511083749361)
                  ·
                    refine ⟨32377899221731883312812021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43170532295642511083749361 32377899221731883312812021)
                    ·
                      refine ⟨3035428052037364060576127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32377899221731883312812021 3035428052037364060576127)
                      ·
                        rfl

theorem cell23_5911475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_5911475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911475 prefixEnd_5911475 := by exact prefixLift 5911475
  have htrace : WordTrace (prefixWord ++ tailWord_5911475) baseStart_5911475 baseEnd_5911475 := by
    simpa [prefixWord, tailWord_5911475, baseEnd_5911475] using wordTrace_append hprefix tailTrace_5911475
  have hstable : (prefixWord ++ tailWord_5911475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911475).length < 2 ^ (prefixWord ++ tailWord_5911475).sum := by decide
  have hdescent : baseEnd_5911475 < baseStart_5911475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911502 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5911502 : Nat := 118140960795 + 5911502 * 2 ^ 59
def prefixEnd_5911502 : Nat := 4983230072969 + 3 ^ 40 * 5911502 * 2
def baseEnd_5911502 : Nat := 3035441916015035454938503

theorem tailTrace_5911502 : CollatzResearch.WordTrace tailWord_5911502 prefixEnd_5911502 3035441916015035454938503 := by
  unfold tailWord_5911502
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951273878705666626002095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143740127353096888672011173 26951273878705666626002095)
  ·
    refine ⟨40426910818058499939003143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26951273878705666626002095 40426910818058499939003143)
    ·
      refine ⟨60640366227087749908504715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40426910818058499939003143 60640366227087749908504715)
      ·
        refine ⟨90960549340631624862757073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60640366227087749908504715 90960549340631624862757073)
        ·
          refine ⟨68220412005473718647067805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90960549340631624862757073 68220412005473718647067805)
          ·
            refine ⟨25582654502052644492650427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68220412005473718647067805 25582654502052644492650427)
            ·
              refine ⟨38373981753078966738975641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25582654502052644492650427 38373981753078966738975641)
              ·
                refine ⟨28780486314809225054231731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38373981753078966738975641 28780486314809225054231731)
                ·
                  refine ⟨43170729472213837581347597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28780486314809225054231731 43170729472213837581347597)
                  ·
                    refine ⟨16189023552080189093005349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43170729472213837581347597 16189023552080189093005349)
                    ·
                      refine ⟨3035441916015035454938503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16189023552080189093005349 3035441916015035454938503)
                      ·
                        rfl

theorem cell23_5911502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5911502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911502 prefixEnd_5911502 := by exact prefixLift 5911502
  have htrace : WordTrace (prefixWord ++ tailWord_5911502) baseStart_5911502 baseEnd_5911502 := by
    simpa [prefixWord, tailWord_5911502, baseEnd_5911502] using wordTrace_append hprefix tailTrace_5911502
  have hstable : (prefixWord ++ tailWord_5911502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911502).length < 2 ^ (prefixWord ++ tailWord_5911502).sum := by decide
  have hdescent : baseEnd_5911502 < baseStart_5911502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911555 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 1, 11]
def baseStart_5911555 : Nat := 118140960795 + 5911555 * 2 ^ 59
def prefixEnd_5911555 : Nat := 4983230072969 + 3 ^ 40 * 5911555 * 2
def baseEnd_5911555 : Nat := 1011823043496574582525253

theorem tailTrace_5911555 : CollatzResearch.WordTrace tailWord_5911555 prefixEnd_5911555 1011823043496574582525253 := by
  unfold tailWord_5911555
  simp only [CollatzResearch.WordTrace]
  refine ⟨215612124098453323059696119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143741416065635548706464079 215612124098453323059696119)
  ·
    refine ⟨323418186147679984589544179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215612124098453323059696119 323418186147679984589544179)
    ·
      refine ⟨485127279221519976884316269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323418186147679984589544179 485127279221519976884316269)
      ·
        refine ⟨181922729708069991331618601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485127279221519976884316269 181922729708069991331618601)
        ·
          refine ⟨136442047281052493498713951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181922729708069991331618601 136442047281052493498713951)
          ·
            refine ⟨204663070921578740248070927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136442047281052493498713951 204663070921578740248070927)
            ·
              refine ⟨306994606382368110372106391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204663070921578740248070927 306994606382368110372106391)
              ·
                refine ⟨460491909573552165558159587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306994606382368110372106391 460491909573552165558159587)
                ·
                  refine ⟨690737864360328248337239381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460491909573552165558159587 690737864360328248337239381)
                  ·
                    refine ⟨1011823043496574582525253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 690737864360328248337239381 1011823043496574582525253)
                    ·
                      rfl

theorem cell23_5911555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_5911555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911555 prefixEnd_5911555 := by exact prefixLift 5911555
  have htrace : WordTrace (prefixWord ++ tailWord_5911555) baseStart_5911555 baseEnd_5911555 := by
    simpa [prefixWord, tailWord_5911555, baseEnd_5911555] using wordTrace_append hprefix tailTrace_5911555
  have hstable : (prefixWord ++ tailWord_5911555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911555).length < 2 ^ (prefixWord ++ tailWord_5911555).sum := by decide
  have hdescent : baseEnd_5911555 < baseStart_5911555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911569 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 3]
def baseStart_5911569 : Nat := 118140960795 + 5911569 * 2 ^ 59
def prefixEnd_5911569 : Nat := 4983230072969 + 3 ^ 40 * 5911569 * 2
def baseEnd_5911569 : Nat := 3035476319218886692800695

theorem tailTrace_5911569 : CollatzResearch.WordTrace tailWord_5911569 prefixEnd_5911569 3035476319218886692800695 := by
  unfold tailWord_5911569
  simp only [CollatzResearch.WordTrace]
  refine ⟨215612634720402603450705761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143741756480268402300470507 215612634720402603450705761)
  ·
    refine ⟨161709476040301952588029321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215612634720402603450705761 161709476040301952588029321)
    ·
      refine ⟨121282107030226464441021991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161709476040301952588029321 121282107030226464441021991)
      ·
        refine ⟨181923160545339696661532987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121282107030226464441021991 181923160545339696661532987)
        ·
          refine ⟨272884740818009544992299481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181923160545339696661532987 272884740818009544992299481)
          ·
            refine ⟨204663555613507158744224611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272884740818009544992299481 204663555613507158744224611)
            ·
              refine ⟨306995333420260738116336917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204663555613507158744224611 306995333420260738116336917)
              ·
                refine ⟨14390406254074722099203293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 306995333420260738116336917 14390406254074722099203293)
                ·
                  refine ⟨5396402345278020787201235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14390406254074722099203293 5396402345278020787201235)
                  ·
                    refine ⟨8094603517917031180801853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5396402345278020787201235 8094603517917031180801853)
                    ·
                      refine ⟨3035476319218886692800695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094603517917031180801853 3035476319218886692800695)
                      ·
                        rfl

theorem cell23_5911569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_5911569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911569 prefixEnd_5911569 := by exact prefixLift 5911569
  have htrace : WordTrace (prefixWord ++ tailWord_5911569) baseStart_5911569 baseEnd_5911569 := by
    simpa [prefixWord, tailWord_5911569, baseEnd_5911569] using wordTrace_append hprefix tailTrace_5911569
  have hstable : (prefixWord ++ tailWord_5911569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911569).length < 2 ^ (prefixWord ++ tailWord_5911569).sum := by decide
  have hdescent : baseEnd_5911569 < baseStart_5911569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911570 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5911570 : Nat := 118140960795 + 5911570 * 2 ^ 59
def prefixEnd_5911570 : Nat := 4983230072969 + 3 ^ 40 * 5911570 * 2
def baseEnd_5911570 : Nat := 3035476832699541188888191

theorem tailTrace_5911570 : CollatzResearch.WordTrace tailWord_5911570 prefixEnd_5911570 3035476832699541188888191 := by
  unfold tailWord_5911570
  simp only [CollatzResearch.WordTrace]
  refine ⟨53903167798349745155373041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143741780795599320414328109 53903167798349745155373041)
  ·
    refine ⟨40427375848762308866529781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53903167798349745155373041 40427375848762308866529781)
    ·
      refine ⟨3790066485821466456237167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40427375848762308866529781 3790066485821466456237167)
      ·
        refine ⟨5685099728732199684355751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3790066485821466456237167 5685099728732199684355751)
        ·
          refine ⟨8527649593098299526533627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685099728732199684355751 8527649593098299526533627)
          ·
            refine ⟨12791474389647449289800441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527649593098299526533627 12791474389647449289800441)
            ·
              refine ⟨9593605792235586967350331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12791474389647449289800441 9593605792235586967350331)
              ·
                refine ⟨14390408688353380451025497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9593605792235586967350331 14390408688353380451025497)
                ·
                  refine ⟨10792806516265035338269123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14390408688353380451025497 10792806516265035338269123)
                  ·
                    refine ⟨16189209774397553007403685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10792806516265035338269123 16189209774397553007403685)
                    ·
                      refine ⟨3035476832699541188888191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16189209774397553007403685 3035476832699541188888191)
                      ·
                        rfl

theorem cell23_5911570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5911570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911570 prefixEnd_5911570 := by exact prefixLift 5911570
  have htrace : WordTrace (prefixWord ++ tailWord_5911570) baseStart_5911570 baseEnd_5911570 := by
    simpa [prefixWord, tailWord_5911570, baseEnd_5911570] using wordTrace_append hprefix tailTrace_5911570
  have hstable : (prefixWord ++ tailWord_5911570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911570).length < 2 ^ (prefixWord ++ tailWord_5911570).sum := by decide
  have hdescent : baseEnd_5911570 < baseStart_5911570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911602 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_5911602 : Nat := 118140960795 + 5911602 * 2 ^ 59
def prefixEnd_5911602 : Nat := 4983230072969 + 3 ^ 40 * 5911602 * 2
def baseEnd_5911602 : Nat := 1011831088026828354562681

theorem tailTrace_5911602 : CollatzResearch.WordTrace tailWord_5911602 prefixEnd_5911602 1011831088026828354562681 := by
  unfold tailWord_5911602
  simp only [CollatzResearch.WordTrace]
  refine ⟨53903459582320762521664265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143742558886188700057771373 53903459582320762521664265)
  ·
    refine ⟨40427594686740571891248199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53903459582320762521664265 40427594686740571891248199)
    ·
      refine ⟨60641392030110857836872299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40427594686740571891248199 60641392030110857836872299)
      ·
        refine ⟨90962088045166286755308449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60641392030110857836872299 90962088045166286755308449)
        ·
          refine ⟨68221566033874715066481337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90962088045166286755308449 68221566033874715066481337)
          ·
            refine ⟨51166174525406036299861003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68221566033874715066481337 51166174525406036299861003)
            ·
              refine ⟨76749261788109054449791505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51166174525406036299861003 76749261788109054449791505)
              ·
                refine ⟨57561946341081790837343629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76749261788109054449791505 57561946341081790837343629)
                ·
                  refine ⟨21585729877905671564003861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57561946341081790837343629 21585729877905671564003861)
                  ·
                    refine ⟨1011831088026828354562681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21585729877905671564003861 1011831088026828354562681)
                    ·
                      rfl

theorem cell23_5911602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_5911602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911602 prefixEnd_5911602 := by exact prefixLift 5911602
  have htrace : WordTrace (prefixWord ++ tailWord_5911602) baseStart_5911602 baseEnd_5911602 := by
    simpa [prefixWord, tailWord_5911602, baseEnd_5911602] using wordTrace_append hprefix tailTrace_5911602
  have hstable : (prefixWord ++ tailWord_5911602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911602).length < 2 ^ (prefixWord ++ tailWord_5911602).sum := by decide
  have hdescent : baseEnd_5911602 < baseStart_5911602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911609 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5911609 : Nat := 118140960795 + 5911609 * 2 ^ 59
def prefixEnd_5911609 : Nat := 4983230072969 + 3 ^ 40 * 5911609 * 2
def baseEnd_5911609 : Nat := 3035496858445066536300511

theorem tailTrace_5911609 : CollatzResearch.WordTrace tailWord_5911609 prefixEnd_5911609 3035496858445066536300511 := by
  unfold tailWord_5911609
  simp only [CollatzResearch.WordTrace]
  refine ⟨215614093640257690282161881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143742729093505126854774587 215614093640257690282161881)
  ·
    refine ⟨161710570230193267711621411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215614093640257690282161881 161710570230193267711621411)
    ·
      refine ⟨242565855345289901567432117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161710570230193267711621411 242565855345289901567432117)
      ·
        refine ⟨22740548938620928271946761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242565855345289901567432117 22740548938620928271946761)
        ·
          refine ⟨17055411703965696203960071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22740548938620928271946761 17055411703965696203960071)
          ·
            refine ⟨25583117555948544305940107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17055411703965696203960071 25583117555948544305940107)
            ·
              refine ⟨38374676333922816458910161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25583117555948544305940107 38374676333922816458910161)
              ·
                refine ⟨28781007250442112344182621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38374676333922816458910161 28781007250442112344182621)
                ·
                  refine ⟨10792877718915792129068483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28781007250442112344182621 10792877718915792129068483)
                  ·
                    refine ⟨16189316578373688193602725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10792877718915792129068483 16189316578373688193602725)
                    ·
                      refine ⟨3035496858445066536300511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16189316578373688193602725 3035496858445066536300511)
                      ·
                        rfl

theorem cell23_5911609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5911609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911609 prefixEnd_5911609 := by exact prefixLift 5911609
  have htrace : WordTrace (prefixWord ++ tailWord_5911609) baseStart_5911609 baseEnd_5911609 := by
    simpa [prefixWord, tailWord_5911609, baseEnd_5911609] using wordTrace_append hprefix tailTrace_5911609
  have hstable : (prefixWord ++ tailWord_5911609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911609).length < 2 ^ (prefixWord ++ tailWord_5911609).sum := by decide
  have hdescent : baseEnd_5911609 < baseStart_5911609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911619 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 2, 4]
def baseStart_5911619 : Nat := 118140960795 + 5911619 * 2 ^ 59
def prefixEnd_5911619 : Nat := 4983230072969 + 3 ^ 40 * 5911619 * 2
def baseEnd_5911619 : Nat := 1011833997750537165725155

theorem tailTrace_5911619 : CollatzResearch.WordTrace tailWord_5911619 prefixEnd_5911619 1011833997750537165725155 := by
  unfold tailWord_5911619
  simp only [CollatzResearch.WordTrace]
  refine ⟨215614458370221461990025911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143742972246814307993350607 215614458370221461990025911)
  ·
    refine ⟨323421687555332192985038867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215614458370221461990025911 323421687555332192985038867)
    ·
      refine ⟨485132531332998289477558301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323421687555332192985038867 485132531332998289477558301)
      ·
        refine ⟨181924699249874358554084363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485132531332998289477558301 181924699249874358554084363)
        ·
          refine ⟨272887048874811537831126545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181924699249874358554084363 272887048874811537831126545)
          ·
            refine ⟨204665286656108653373344909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272887048874811537831126545 204665286656108653373344909)
            ·
              refine ⟨76749482496040745015004341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204665286656108653373344909 76749482496040745015004341)
              ·
                refine ⟨7195263984003819845156657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76749482496040745015004341 7195263984003819845156657)
                ·
                  refine ⟨5396447988002864883867493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7195263984003819845156657 5396447988002864883867493)
                  ·
                    refine ⟨1011833997750537165725155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5396447988002864883867493 1011833997750537165725155)
                    ·
                      rfl

theorem cell23_5911619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 2, 4].length) (baseStart_5911619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911619 prefixEnd_5911619 := by exact prefixLift 5911619
  have htrace : WordTrace (prefixWord ++ tailWord_5911619) baseStart_5911619 baseEnd_5911619 := by
    simpa [prefixWord, tailWord_5911619, baseEnd_5911619] using wordTrace_append hprefix tailTrace_5911619
  have hstable : (prefixWord ++ tailWord_5911619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911619).length < 2 ^ (prefixWord ++ tailWord_5911619).sum := by decide
  have hdescent : baseEnd_5911619 < baseStart_5911619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911626 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2]
def baseStart_5911626 : Nat := 118140960795 + 5911626 * 2 ^ 59
def prefixEnd_5911626 : Nat := 4983230072969 + 3 ^ 40 * 5911626 * 2
def baseEnd_5911626 : Nat := 3035505587616192969787933

theorem tailTrace_5911626 : CollatzResearch.WordTrace tailWord_5911626 prefixEnd_5911626 3035505587616192969787933 := by
  unfold tailWord_5911626
  simp only [CollatzResearch.WordTrace]
  refine ⟨53903678420299025546382683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143743142454130734790353821 53903678420299025546382683)
  ·
    refine ⟨80855517630448538319574025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53903678420299025546382683 80855517630448538319574025)
    ·
      refine ⟨60641638222836403739680519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80855517630448538319574025 60641638222836403739680519)
      ·
        refine ⟨90962457334254605609520779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60641638222836403739680519 90962457334254605609520779)
        ·
          refine ⟨136443686001381908414281169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90962457334254605609520779 136443686001381908414281169)
          ·
            refine ⟨102332764501036431310710877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136443686001381908414281169 102332764501036431310710877)
            ·
              refine ⟨38374786687888661741516579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102332764501036431310710877 38374786687888661741516579)
              ·
                refine ⟨57562180031832992612274869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38374786687888661741516579 57562180031832992612274869)
                ·
                  refine ⟨5396454377984343057400769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57562180031832992612274869 5396454377984343057400769)
                  ·
                    refine ⟨4047340783488257293050577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396454377984343057400769 4047340783488257293050577)
                    ·
                      refine ⟨3035505587616192969787933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047340783488257293050577 3035505587616192969787933)
                      ·
                        rfl

theorem cell23_5911626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_5911626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911626 prefixEnd_5911626 := by exact prefixLift 5911626
  have htrace : WordTrace (prefixWord ++ tailWord_5911626) baseStart_5911626 baseEnd_5911626 := by
    simpa [prefixWord, tailWord_5911626, baseEnd_5911626] using wordTrace_append hprefix tailTrace_5911626
  have hstable : (prefixWord ++ tailWord_5911626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911626).length < 2 ^ (prefixWord ++ tailWord_5911626).sum := by decide
  have hdescent : baseEnd_5911626 < baseStart_5911626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911652 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_5911652 : Nat := 118140960795 + 5911652 * 2 ^ 59
def prefixEnd_5911652 : Nat := 4983230072969 + 3 ^ 40 * 5911652 * 2
def baseEnd_5911652 : Nat := 3035518938113209868062813

theorem tailTrace_5911652 : CollatzResearch.WordTrace tailWord_5911652 prefixEnd_5911652 3035518938113209868062813 := by
  unfold tailWord_5911652
  simp only [CollatzResearch.WordTrace]
  refine ⟨107807830989550954312988605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143743774652734605750651473 107807830989550954312988605)
  ·
    refine ⟨40427936621081607867370727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107807830989550954312988605 40427936621081607867370727)
    ·
      refine ⟨60641904931622411801056091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40427936621081607867370727 60641904931622411801056091)
      ·
        refine ⟨90962857397433617701584137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60641904931622411801056091 90962857397433617701584137)
        ·
          refine ⟨68222143048075213276188103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90962857397433617701584137 68222143048075213276188103)
          ·
            refine ⟨102333214572112819914282155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68222143048075213276188103 102333214572112819914282155)
            ·
              refine ⟨153499821858169229871423233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102333214572112819914282155 153499821858169229871423233)
              ·
                refine ⟨115124866393626922403567425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153499821858169229871423233 115124866393626922403567425)
                ·
                  refine ⟨86343649795220191802675569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115124866393626922403567425 86343649795220191802675569)
                  ·
                    refine ⟨64757737346415143852006677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86343649795220191802675569 64757737346415143852006677)
                    ·
                      refine ⟨3035518938113209868062813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64757737346415143852006677 3035518938113209868062813)
                      ·
                        rfl

theorem cell23_5911652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_5911652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911652 prefixEnd_5911652 := by exact prefixLift 5911652
  have htrace : WordTrace (prefixWord ++ tailWord_5911652) baseStart_5911652 baseEnd_5911652 := by
    simpa [prefixWord, tailWord_5911652, baseEnd_5911652] using wordTrace_append hprefix tailTrace_5911652
  have hstable : (prefixWord ++ tailWord_5911652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911652).length < 2 ^ (prefixWord ++ tailWord_5911652).sum := by decide
  have hdescent : baseEnd_5911652 < baseStart_5911652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911673 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 1, 2, 4]
def baseStart_5911673 : Nat := 118140960795 + 5911673 * 2 ^ 59
def prefixEnd_5911673 : Nat := 4983230072969 + 3 ^ 40 * 5911673 * 2
def baseEnd_5911673 : Nat := 3035529721206954285900217

theorem tailTrace_5911673 : CollatzResearch.WordTrace tailWord_5911673 prefixEnd_5911673 3035529721206954285900217 := by
  unfold tailWord_5911673
  simp only [CollatzResearch.WordTrace]
  refine ⟨215616427912025829212491673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143744285274683886141661115 215616427912025829212491673)
  ·
    refine ⟨161712320934019371909368755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215616427912025829212491673 161712320934019371909368755)
    ·
      refine ⟨242568481401029057864053133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161712320934019371909368755 242568481401029057864053133)
      ·
        refine ⟨90963180525385896699019925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242568481401029057864053133 90963180525385896699019925)
        ·
          refine ⟨4263899087127463907766559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90963180525385896699019925 4263899087127463907766559)
          ·
            refine ⟨6395848630691195861649839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4263899087127463907766559 6395848630691195861649839)
            ·
              refine ⟨9593772946036793792474759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6395848630691195861649839 9593772946036793792474759)
              ·
                refine ⟨14390659419055190688712139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9593772946036793792474759 14390659419055190688712139)
                ·
                  refine ⟨21585989128582786033068209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14390659419055190688712139 21585989128582786033068209)
                  ·
                    refine ⟨16189491846437089524801157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21585989128582786033068209 16189491846437089524801157)
                    ·
                      refine ⟨3035529721206954285900217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16189491846437089524801157 3035529721206954285900217)
                      ·
                        rfl

theorem cell23_5911673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_5911673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911673 prefixEnd_5911673 := by exact prefixLift 5911673
  have htrace : WordTrace (prefixWord ++ tailWord_5911673) baseStart_5911673 baseEnd_5911673 := by
    simpa [prefixWord, tailWord_5911673, baseEnd_5911673] using wordTrace_append hprefix tailTrace_5911673
  have hstable : (prefixWord ++ tailWord_5911673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911673).length < 2 ^ (prefixWord ++ tailWord_5911673).sum := by decide
  have hdescent : baseEnd_5911673 < baseStart_5911673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911692 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_5911692 : Nat := 118140960795 + 5911692 * 2 ^ 59
def prefixEnd_5911692 : Nat := 4983230072969 + 3 ^ 40 * 5911692 * 2
def baseEnd_5911692 : Nat := 1011846492446463237187543

theorem tailTrace_5911692 : CollatzResearch.WordTrace tailWord_5911692 prefixEnd_5911692 1011846492446463237187543 := by
  unfold tailWord_5911692
  simp only [CollatzResearch.WordTrace]
  refine ⟨107808560449478497728716665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143744747265971330304955553 107808560449478497728716665)
  ·
    refine ⟨80856420337108873296537499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107808560449478497728716665 80856420337108873296537499)
    ·
      refine ⟨121284630505663309944806249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80856420337108873296537499 121284630505663309944806249)
      ·
        refine ⟨90963472879247482458604687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121284630505663309944806249 90963472879247482458604687)
        ·
          refine ⟨136445209318871223687907031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90963472879247482458604687 136445209318871223687907031)
          ·
            refine ⟨204667813978306835531860547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136445209318871223687907031 204667813978306835531860547)
            ·
              refine ⟨307001720967460253297790821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204667813978306835531860547 307001720967460253297790821)
              ·
                refine ⟨57562822681398797493335779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307001720967460253297790821 57562822681398797493335779)
                ·
                  refine ⟨86344234022098196240003669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57562822681398797493335779 86344234022098196240003669)
                  ·
                    refine ⟨1011846492446463237187543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86344234022098196240003669 1011846492446463237187543)
                    ·
                      rfl

theorem cell23_5911692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_5911692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911692 prefixEnd_5911692 := by exact prefixLift 5911692
  have htrace : WordTrace (prefixWord ++ tailWord_5911692) baseStart_5911692 baseEnd_5911692 := by
    simpa [prefixWord, tailWord_5911692, baseEnd_5911692] using wordTrace_append hprefix tailTrace_5911692
  have hstable : (prefixWord ++ tailWord_5911692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911692).length < 2 ^ (prefixWord ++ tailWord_5911692).sum := by decide
  have hdescent : baseEnd_5911692 < baseStart_5911692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911703 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_5911703 : Nat := 118140960795 + 5911703 * 2 ^ 59
def prefixEnd_5911703 : Nat := 4983230072969 + 3 ^ 40 * 5911703 * 2
def baseEnd_5911703 : Nat := 3035545125626589168525079

theorem tailTrace_5911703 : CollatzResearch.WordTrace tailWord_5911703 prefixEnd_5911703 3035545125626589168525079 := by
  unfold tailWord_5911703
  simp only [CollatzResearch.WordTrace]
  refine ⟨215617522101917144336083763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143745014734611429557389175 215617522101917144336083763)
  ·
    refine ⟨323426283152875716504125645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215617522101917144336083763 323426283152875716504125645)
    ·
      refine ⟨121284856182328393689047117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323426283152875716504125645 121284856182328393689047117)
      ·
        refine ⟨45481821068373147633392669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121284856182328393689047117 45481821068373147633392669)
        ·
          refine ⟨17055682900639930362522251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45481821068373147633392669 17055682900639930362522251)
          ·
            refine ⟨25583524350959895543783377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17055682900639930362522251 25583524350959895543783377)
            ·
              refine ⟨19187643263219921657837533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25583524350959895543783377 19187643263219921657837533)
              ·
                refine ⟨7195366223707470621689075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19187643263219921657837533 7195366223707470621689075)
                ·
                  refine ⟨10793049335561205932533613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7195366223707470621689075 10793049335561205932533613)
                  ·
                    refine ⟨4047393500835452224700105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10793049335561205932533613 4047393500835452224700105)
                    ·
                      refine ⟨3035545125626589168525079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047393500835452224700105 3035545125626589168525079)
                      ·
                        rfl

theorem cell23_5911703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_5911703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911703 prefixEnd_5911703 := by exact prefixLift 5911703
  have htrace : WordTrace (prefixWord ++ tailWord_5911703) baseStart_5911703 baseEnd_5911703 := by
    simpa [prefixWord, tailWord_5911703, baseEnd_5911703] using wordTrace_append hprefix tailTrace_5911703
  have hstable : (prefixWord ++ tailWord_5911703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911703).length < 2 ^ (prefixWord ++ tailWord_5911703).sum := by decide
  have hdescent : baseEnd_5911703 < baseStart_5911703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911749 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_5911749 : Nat := 118140960795 + 5911749 * 2 ^ 59
def prefixEnd_5911749 : Nat := 4983230072969 + 3 ^ 40 * 5911749 * 2
def baseEnd_5911749 : Nat := 3035568745736695988549867

theorem tailTrace_5911749 : CollatzResearch.WordTrace tailWord_5911749 prefixEnd_5911749 3035568745736695988549867 := by
  unfold tailWord_5911749
  simp only [CollatzResearch.WordTrace]
  refine ⟨215619199859750494192258301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143746133239833662794838867 215619199859750494192258301)
  ·
    refine ⟨80857199947406435322096863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215619199859750494192258301 80857199947406435322096863)
    ·
      refine ⟨121285799921109652983145295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80857199947406435322096863 121285799921109652983145295)
      ·
        refine ⟨181928699881664479474717943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121285799921109652983145295 181928699881664479474717943)
        ·
          refine ⟨272893049822496719212076915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181928699881664479474717943 272893049822496719212076915)
          ·
            refine ⟨409339574733745078818115373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272893049822496719212076915 409339574733745078818115373)
            ·
              refine ⟨153502340525154404556793265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409339574733745078818115373 153502340525154404556793265)
              ·
                refine ⟨115126755393865803417594949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153502340525154404556793265 115126755393865803417594949)
                ·
                  refine ⟨21586266636349838140799053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115126755393865803417594949 21586266636349838140799053)
                  ·
                    refine ⟨8094849988631189302799645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21586266636349838140799053 8094849988631189302799645)
                    ·
                      refine ⟨3035568745736695988549867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094849988631189302799645 3035568745736695988549867)
                      ·
                        rfl

theorem cell23_5911749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_5911749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911749 prefixEnd_5911749 := by exact prefixLift 5911749
  have htrace : WordTrace (prefixWord ++ tailWord_5911749) baseStart_5911749 baseEnd_5911749 := by
    simpa [prefixWord, tailWord_5911749, baseEnd_5911749] using wordTrace_append hprefix tailTrace_5911749
  have hstable : (prefixWord ++ tailWord_5911749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911749).length < 2 ^ (prefixWord ++ tailWord_5911749).sum := by decide
  have hdescent : baseEnd_5911749 < baseStart_5911749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911776 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2]
def baseStart_5911776 : Nat := 118140960795 + 5911776 * 2 ^ 59
def prefixEnd_5911776 : Nat := 4983230072969 + 3 ^ 40 * 5911776 * 2
def baseEnd_5911776 : Nat := 3035582609714367382912243

theorem tailTrace_5911776 : CollatzResearch.WordTrace tailWord_5911776 prefixEnd_5911776 3035582609714367382912243 := by
  unfold tailWord_5911776
  simp only [CollatzResearch.WordTrace]
  refine ⟨107810092315326338901745591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143746789753768451868994121 107810092315326338901745591)
  ·
    refine ⟨161715138472989508352618387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107810092315326338901745591 161715138472989508352618387)
    ·
      refine ⟨242572707709484262528927581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161715138472989508352618387 242572707709484262528927581)
      ·
        refine ⟨90964765391056598448347843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242572707709484262528927581 90964765391056598448347843)
        ·
          refine ⟨136447148086584897672521765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90964765391056598448347843 136447148086584897672521765)
          ·
            refine ⟨25583840266234668313597831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136447148086584897672521765 25583840266234668313597831)
            ·
              refine ⟨38375760399352002470396747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25583840266234668313597831 38375760399352002470396747)
              ·
                refine ⟨57563640599028003705595121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38375760399352002470396747 57563640599028003705595121)
                ·
                  refine ⟨43172730449271002779196341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57563640599028003705595121 43172730449271002779196341)
                  ·
                    refine ⟨4047443479619156510549657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43172730449271002779196341 4047443479619156510549657)
                    ·
                      refine ⟨3035582609714367382912243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047443479619156510549657 3035582609714367382912243)
                      ·
                        rfl

theorem cell23_5911776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_5911776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911776 prefixEnd_5911776 := by exact prefixLift 5911776
  have htrace : WordTrace (prefixWord ++ tailWord_5911776) baseStart_5911776 baseEnd_5911776 := by
    simpa [prefixWord, tailWord_5911776, baseEnd_5911776] using wordTrace_append hprefix tailTrace_5911776
  have hstable : (prefixWord ++ tailWord_5911776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911776).length < 2 ^ (prefixWord ++ tailWord_5911776).sum := by decide
  have hdescent : baseEnd_5911776 < baseStart_5911776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911783 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5911783 : Nat := 118140960795 + 5911783 * 2 ^ 59
def prefixEnd_5911783 : Nat := 4983230072969 + 3 ^ 40 * 5911783 * 2
def baseEnd_5911783 : Nat := 3035586204078948855524711

theorem tailTrace_5911783 : CollatzResearch.WordTrace tailWord_5911783 prefixEnd_5911783 3035586204078948855524711 := by
  unfold tailWord_5911783
  simp only [CollatzResearch.WordTrace]
  refine ⟨215620439941627317998996003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143746959961084878665997335 215620439941627317998996003)
  ·
    refine ⟨323430659912440976998494005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215620439941627317998996003 323430659912440976998494005)
    ·
      refine ⟨30321624366791341593608813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323430659912440976998494005 30321624366791341593608813)
      ·
        refine ⟨11370609137546753097603305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30321624366791341593608813 11370609137546753097603305)
        ·
          refine ⟨8527956853160064823202479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11370609137546753097603305 8527956853160064823202479)
          ·
            refine ⟨12791935279740097234803719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8527956853160064823202479 12791935279740097234803719)
            ·
              refine ⟨19187902919610145852205579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12791935279740097234803719 19187902919610145852205579)
              ·
                refine ⟨28781854379415218778308369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19187902919610145852205579 28781854379415218778308369)
                ·
                  refine ⟨21586390784561414083731277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28781854379415218778308369 21586390784561414083731277)
                  ·
                    refine ⟨8094896544210530281399229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21586390784561414083731277 8094896544210530281399229)
                    ·
                      refine ⟨3035586204078948855524711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8094896544210530281399229 3035586204078948855524711)
                      ·
                        rfl

theorem cell23_5911783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5911783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911783 prefixEnd_5911783 := by exact prefixLift 5911783
  have htrace : WordTrace (prefixWord ++ tailWord_5911783) baseStart_5911783 baseEnd_5911783 := by
    simpa [prefixWord, tailWord_5911783, baseEnd_5911783] using wordTrace_append hprefix tailTrace_5911783
  have hstable : (prefixWord ++ tailWord_5911783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911783).length < 2 ^ (prefixWord ++ tailWord_5911783).sum := by decide
  have hdescent : baseEnd_5911783 < baseStart_5911783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911819 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_5911819 : Nat := 118140960795 + 5911819 * 2 ^ 59
def prefixEnd_5911819 : Nat := 4983230072969 + 3 ^ 40 * 5911819 * 2
def baseEnd_5911819 : Nat := 3035604689382510714674545

theorem tailTrace_5911819 : CollatzResearch.WordTrace tailWord_5911819 prefixEnd_5911819 3035604689382510714674545 := by
  unfold tailWord_5911819
  simp only [CollatzResearch.WordTrace]
  refine ⟨215621752969496896147306511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143747835312997930764871007 215621752969496896147306511)
  ·
    refine ⟨323432629454245344220959767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215621752969496896147306511 323432629454245344220959767)
    ·
      refine ⟨485148944181368016331439651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323432629454245344220959767 485148944181368016331439651)
      ·
        refine ⟨727723416272052024497159477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485148944181368016331439651 727723416272052024497159477)
        ·
          refine ⟨68224070275504877296608701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 727723416272052024497159477 68224070275504877296608701)
          ·
            refine ⟨25584026353314328986228263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68224070275504877296608701 25584026353314328986228263)
            ·
              refine ⟨38376039529971493479342395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25584026353314328986228263 38376039529971493479342395)
              ·
                refine ⟨57564059294957240219013593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38376039529971493479342395 57564059294957240219013593)
                ·
                  refine ⟨43173044471217930164260195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57564059294957240219013593 43173044471217930164260195)
                  ·
                    refine ⟨64759566706826895246390293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43173044471217930164260195 64759566706826895246390293)
                    ·
                      refine ⟨3035604689382510714674545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64759566706826895246390293 3035604689382510714674545)
                      ·
                        rfl

theorem cell23_5911819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_5911819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911819 prefixEnd_5911819 := by exact prefixLift 5911819
  have htrace : WordTrace (prefixWord ++ tailWord_5911819) baseStart_5911819 baseEnd_5911819 := by
    simpa [prefixWord, tailWord_5911819, baseEnd_5911819] using wordTrace_append hprefix tailTrace_5911819
  have hstable : (prefixWord ++ tailWord_5911819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911819).length < 2 ^ (prefixWord ++ tailWord_5911819).sum := by decide
  have hdescent : baseEnd_5911819 < baseStart_5911819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911896 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_5911896 : Nat := 118140960795 + 5911896 * 2 ^ 59
def prefixEnd_5911896 : Nat := 4983230072969 + 3 ^ 40 * 5911896 * 2
def baseEnd_5911896 : Nat := 3035644227392906913411691

theorem tailTrace_5911896 : CollatzResearch.WordTrace tailWord_5911896 prefixEnd_5911896 3035644227392906913411691 := by
  unfold tailWord_5911896
  simp only [CollatzResearch.WordTrace]
  refine ⟨107812280695108969148929771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143749707593478625531906361 107812280695108969148929771)
  ·
    refine ⟨161718421042663453723394657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107812280695108969148929771 161718421042663453723394657)
    ·
      refine ⟨121288815781997590292545993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161718421042663453723394657 121288815781997590292545993)
      ·
        refine ⟨90966611836498192719409495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121288815781997590292545993 90966611836498192719409495)
        ·
          refine ⟨136449917754747289079114243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90966611836498192719409495 136449917754747289079114243)
          ·
            refine ⟨204674876632120933618671365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136449917754747289079114243 204674876632120933618671365)
            ·
              refine ⟨38376539368522675053500881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204674876632120933618671365 38376539368522675053500881)
              ·
                refine ⟨28782404526392006290125661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38376539368522675053500881 28782404526392006290125661)
                ·
                  refine ⟨10793401697397002358797123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28782404526392006290125661 10793401697397002358797123)
                  ·
                    refine ⟨16190102546095503538195685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10793401697397002358797123 16190102546095503538195685)
                    ·
                      refine ⟨3035644227392906913411691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16190102546095503538195685 3035644227392906913411691)
                      ·
                        rfl

theorem cell23_5911896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_5911896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911896 prefixEnd_5911896 := by exact prefixLift 5911896
  have htrace : WordTrace (prefixWord ++ tailWord_5911896) baseStart_5911896 baseEnd_5911896 := by
    simpa [prefixWord, tailWord_5911896, baseEnd_5911896] using wordTrace_append hprefix tailTrace_5911896
  have hstable : (prefixWord ++ tailWord_5911896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911896).length < 2 ^ (prefixWord ++ tailWord_5911896).sum := by decide
  have hdescent : baseEnd_5911896 < baseStart_5911896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911919 : List Nat := [1, 1, 2, 1, 3, 1, 3, 11]
def baseStart_5911919 : Nat := 118140960795 + 5911919 * 2 ^ 59
def prefixEnd_5911919 : Nat := 4983230072969 + 3 ^ 40 * 5911919 * 2
def baseEnd_5911919 : Nat := 112431705090665197163855

theorem tailTrace_5911919 : CollatzResearch.WordTrace tailWord_5911919 prefixEnd_5911919 112431705090665197163855 := by
  unfold tailWord_5911919
  simp only [CollatzResearch.WordTrace]
  refine ⟨215625400269134613225946811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143750266846089742150631207 215625400269134613225946811)
  ·
    refine ⟨323438100403701919838920217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215625400269134613225946811 323438100403701919838920217)
    ·
      refine ⟨242578575302776439879190163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323438100403701919838920217 242578575302776439879190163)
      ·
        refine ⟨363867862954164659818785245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242578575302776439879190163 363867862954164659818785245)
        ·
          refine ⟨136450448607811747432044467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363867862954164659818785245 136450448607811747432044467)
          ·
            refine ⟨204675672911717621148066701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136450448607811747432044467 204675672911717621148066701)
            ·
              refine ⟨76753377341894107930525013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204675672911717621148066701 76753377341894107930525013)
              ·
                refine ⟨112431705090665197163855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 76753377341894107930525013 112431705090665197163855)
                ·
                  rfl

theorem cell23_5911919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 11].length) (baseStart_5911919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911919 prefixEnd_5911919 := by exact prefixLift 5911919
  have htrace : WordTrace (prefixWord ++ tailWord_5911919) baseStart_5911919 baseEnd_5911919 := by
    simpa [prefixWord, tailWord_5911919, baseEnd_5911919] using wordTrace_append hprefix tailTrace_5911919
  have hstable : (prefixWord ++ tailWord_5911919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911919).length < 2 ^ (prefixWord ++ tailWord_5911919).sum := by decide
  have hdescent : baseEnd_5911919 < baseStart_5911919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911940 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5911940 : Nat := 118140960795 + 5911940 * 2 ^ 59
def prefixEnd_5911940 : Nat := 4983230072969 + 3 ^ 40 * 5911940 * 2
def baseEnd_5911940 : Nat := 1011888940180568247087163

theorem tailTrace_5911940 : CollatzResearch.WordTrace tailWord_5911940 prefixEnd_5911940 1011888940180568247087163 := by
  unfold tailWord_5911940
  simp only [CollatzResearch.WordTrace]
  refine ⟨107813083101029266906230637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143750777468039022541640849 107813083101029266906230637)
  ·
    refine ⟨40429906162885975089836489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107813083101029266906230637 40429906162885975089836489)
    ·
      refine ⟨30322429622164481317377367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40429906162885975089836489 30322429622164481317377367)
      ·
        refine ⟨45483644433246721976066051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30322429622164481317377367 45483644433246721976066051)
        ·
          refine ⟨68225466649870082964099077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45483644433246721976066051 68225466649870082964099077)
          ·
            refine ⟨12792274996850640555768577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68225466649870082964099077 12792274996850640555768577)
            ·
              refine ⟨9594206247637980416826433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12792274996850640555768577 9594206247637980416826433)
              ·
                refine ⟨7195654685728485312619825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594206247637980416826433 7195654685728485312619825)
                ·
                  refine ⟨5396741014296363984464869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7195654685728485312619825 5396741014296363984464869)
                  ·
                    refine ⟨1011888940180568247087163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5396741014296363984464869 1011888940180568247087163)
                    ·
                      rfl

theorem cell23_5911940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5911940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911940 prefixEnd_5911940 := by exact prefixLift 5911940
  have htrace : WordTrace (prefixWord ++ tailWord_5911940) baseStart_5911940 baseEnd_5911940 := by
    simpa [prefixWord, tailWord_5911940, baseEnd_5911940] using wordTrace_append hprefix tailTrace_5911940
  have hstable : (prefixWord ++ tailWord_5911940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911940).length < 2 ^ (prefixWord ++ tailWord_5911940).sum := by decide
  have hdescent : baseEnd_5911940 < baseStart_5911940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911947 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 1, 2, 2]
def baseStart_5911947 : Nat := 118140960795 + 5911947 * 2 ^ 59
def prefixEnd_5911947 : Nat := 4983230072969 + 3 ^ 40 * 5911947 * 2
def baseEnd_5911947 : Nat := 3035670414906286213873957

theorem tailTrace_5911947 : CollatzResearch.WordTrace tailWord_5911947 prefixEnd_5911947 3035670414906286213873957 := by
  unfold tailWord_5911947
  simp only [CollatzResearch.WordTrace]
  refine ⟨215626421513033174007966095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143750947675355449338644063 215626421513033174007966095)
  ·
    refine ⟨323439632269549761011949143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215626421513033174007966095 323439632269549761011949143)
    ·
      refine ⟨485159448404324641517923715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323439632269549761011949143 485159448404324641517923715)
      ·
        refine ⟨727739172606486962276885573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485159448404324641517923715 727739172606486962276885573)
        ·
          refine ⟨136451094863716305426916045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 727739172606486962276885573 136451094863716305426916045)
          ·
            refine ⟨51169160573893614535093517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136451094863716305426916045 51169160573893614535093517)
            ·
              refine ⟨19188435215210105450660069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51169160573893614535093517 19188435215210105450660069)
              ·
                refine ⟨3597831602851894771998763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19188435215210105450660069 3597831602851894771998763)
                ·
                  refine ⟨5396747404277842157998145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597831602851894771998763 5396747404277842157998145)
                  ·
                    refine ⟨4047560553208381618498609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396747404277842157998145 4047560553208381618498609)
                    ·
                      refine ⟨3035670414906286213873957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047560553208381618498609 3035670414906286213873957)
                      ·
                        rfl

theorem cell23_5911947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 2, 2].length) (baseStart_5911947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911947 prefixEnd_5911947 := by exact prefixLift 5911947
  have htrace : WordTrace (prefixWord ++ tailWord_5911947) baseStart_5911947 baseEnd_5911947 := by
    simpa [prefixWord, tailWord_5911947, baseEnd_5911947] using wordTrace_append hprefix tailTrace_5911947
  have hstable : (prefixWord ++ tailWord_5911947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911947).length < 2 ^ (prefixWord ++ tailWord_5911947).sum := by decide
  have hdescent : baseEnd_5911947 < baseStart_5911947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911960 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5911960 : Nat := 118140960795 + 5911960 * 2 ^ 59
def prefixEnd_5911960 : Nat := 4983230072969 + 3 ^ 40 * 5911960 * 2
def baseEnd_5911960 : Nat := 3035677090154794663011397

theorem tailTrace_5911960 : CollatzResearch.WordTrace tailWord_5911960 prefixEnd_5911960 3035677090154794663011397 := by
  unfold tailWord_5911960
  simp only [CollatzResearch.WordTrace]
  refine ⟨107813447830993038614094667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143751263774657384818792889 107813447830993038614094667)
  ·
    refine ⟨161720171746489557921142001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107813447830993038614094667 161720171746489557921142001)
    ·
      refine ⟨121290128809867168440856501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161720171746489557921142001 121290128809867168440856501)
      ·
        refine ⟨11370949575925047041330297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121290128809867168440856501 11370949575925047041330297)
        ·
          refine ⟨8528212181943785280997723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11370949575925047041330297 8528212181943785280997723)
          ·
            refine ⟨12792318272915677921496585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8528212181943785280997723 12792318272915677921496585)
            ·
              refine ⟨9594238704686758441122439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12792318272915677921496585 9594238704686758441122439)
              ·
                refine ⟨14391358057030137661683659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9594238704686758441122439 14391358057030137661683659)
                ·
                  refine ⟨21587037085545206492525489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14391358057030137661683659 21587037085545206492525489)
                  ·
                    refine ⟨16190277814158904869394117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21587037085545206492525489 16190277814158904869394117)
                    ·
                      refine ⟨3035677090154794663011397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16190277814158904869394117 3035677090154794663011397)
                      ·
                        rfl

theorem cell23_5911960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5911960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911960 prefixEnd_5911960 := by exact prefixLift 5911960
  have htrace : WordTrace (prefixWord ++ tailWord_5911960) baseStart_5911960 baseEnd_5911960 := by
    simpa [prefixWord, tailWord_5911960, baseEnd_5911960] using wordTrace_append hprefix tailTrace_5911960
  have hstable : (prefixWord ++ tailWord_5911960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911960).length < 2 ^ (prefixWord ++ tailWord_5911960).sum := by decide
  have hdescent : baseEnd_5911960 < baseStart_5911960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911964 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5911964 : Nat := 118140960795 + 5911964 * 2 ^ 59
def prefixEnd_5911964 : Nat := 4983230072969 + 3 ^ 40 * 5911964 * 2
def baseEnd_5911964 : Nat := 3035679144077412647361379

theorem tailTrace_5911964 : CollatzResearch.WordTrace tailWord_5911964 prefixEnd_5911964 3035679144077412647361379 := by
  unfold tailWord_5911964
  simp only [CollatzResearch.WordTrace]
  refine ⟨107813520776985792955667473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143751361035981057274223297 107813520776985792955667473)
  ·
    refine ⟨80860140582739344716750605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107813520776985792955667473 80860140582739344716750605)
    ·
      refine ⟨30322552718527254268781477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80860140582739344716750605 30322552718527254268781477)
      ·
        refine ⟨5685478634723860175396527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30322552718527254268781477 5685478634723860175396527)
        ·
          refine ⟨8528217952085790263094791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685478634723860175396527 8528217952085790263094791)
          ·
            refine ⟨12792326928128685394642187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8528217952085790263094791 12792326928128685394642187)
            ·
              refine ⟨19188490392193028091963281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12792326928128685394642187 19188490392193028091963281)
              ·
                refine ⟨14391367794144771068972461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19188490392193028091963281 14391367794144771068972461)
                ·
                  refine ⟨5396762922804289150864673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14391367794144771068972461 5396762922804289150864673)
                  ·
                    refine ⟨4047572192103216863148505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396762922804289150864673 4047572192103216863148505)
                    ·
                      refine ⟨3035679144077412647361379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047572192103216863148505 3035679144077412647361379)
                      ·
                        rfl

theorem cell23_5911964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5911964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911964 prefixEnd_5911964 := by exact prefixLift 5911964
  have htrace : WordTrace (prefixWord ++ tailWord_5911964) baseStart_5911964 baseEnd_5911964 := by
    simpa [prefixWord, tailWord_5911964, baseEnd_5911964] using wordTrace_append hprefix tailTrace_5911964
  have hstable : (prefixWord ++ tailWord_5911964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911964).length < 2 ^ (prefixWord ++ tailWord_5911964).sum := by decide
  have hdescent : baseEnd_5911964 < baseStart_5911964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911981 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5911981 : Nat := 118140960795 + 5911981 * 2 ^ 59
def prefixEnd_5911981 : Nat := 4983230072969 + 3 ^ 40 * 5911981 * 2
def baseEnd_5911981 : Nat := 3035687873248539080848801

theorem tailTrace_5911981 : CollatzResearch.WordTrace tailWord_5911981 prefixEnd_5911981 3035687873248539080848801 := by
  unfold tailWord_5911981
  simp only [CollatzResearch.WordTrace]
  refine ⟨215627661594909997814703797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143751774396606665209802531 215627661594909997814703797)
  ·
    refine ⟨20215093274522812295128481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215627661594909997814703797 20215093274522812295128481)
    ·
      refine ⟨15161319955892109221346361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215093274522812295128481 15161319955892109221346361)
      ·
        refine ⟨11370989966919081916009771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15161319955892109221346361 11370989966919081916009771)
        ·
          refine ⟨17056484950378622874014657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11370989966919081916009771 17056484950378622874014657)
          ·
            refine ⟨12792363712783967155510993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17056484950378622874014657 12792363712783967155510993)
            ·
              refine ⟨9594272784587975366633245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12792363712783967155510993 9594272784587975366633245)
              ·
                refine ⟨3597852294220490762487467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9594272784587975366633245 3597852294220490762487467)
                ·
                  refine ⟨5396778441330736143731201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3597852294220490762487467 5396778441330736143731201)
                  ·
                    refine ⟨4047583830998052107798401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396778441330736143731201 4047583830998052107798401)
                    ·
                      refine ⟨3035687873248539080848801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047583830998052107798401 3035687873248539080848801)
                      ·
                        rfl

theorem cell23_5911981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5911981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911981 prefixEnd_5911981 := by exact prefixLift 5911981
  have htrace : WordTrace (prefixWord ++ tailWord_5911981) baseStart_5911981 baseEnd_5911981 := by
    simpa [prefixWord, tailWord_5911981, baseEnd_5911981] using wordTrace_append hprefix tailTrace_5911981
  have hstable : (prefixWord ++ tailWord_5911981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911981).length < 2 ^ (prefixWord ++ tailWord_5911981).sum := by decide
  have hdescent : baseEnd_5911981 < baseStart_5911981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5911986 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_5911986 : Nat := 118140960795 + 5911986 * 2 ^ 59
def prefixEnd_5911986 : Nat := 4983230072969 + 3 ^ 40 * 5911986 * 2
def baseEnd_5911986 : Nat := 3035690440651811561286277

theorem tailTrace_5911986 : CollatzResearch.WordTrace tailWord_5911986 prefixEnd_5911986 3035690440651811561286277 := by
  unfold tailWord_5911986
  simp only [CollatzResearch.WordTrace]
  refine ⟨53906960989972970917158953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143751895973261255779090541 53906960989972970917158953)
  ·
    refine ⟨40430220742479728187869215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53906960989972970917158953 40430220742479728187869215)
    ·
      refine ⟨60645331113719592281803823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40430220742479728187869215 60645331113719592281803823)
      ·
        refine ⟨90967996670579388422705735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60645331113719592281803823 90967996670579388422705735)
        ·
          refine ⟨136451995005869082634058603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90967996670579388422705735 136451995005869082634058603)
          ·
            refine ⟨204677992508803623951087905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136451995005869082634058603 204677992508803623951087905)
            ·
              refine ⟨153508494381602717963315929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204677992508803623951087905 153508494381602717963315929)
              ·
                refine ⟨115131370786202038472486947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153508494381602717963315929 115131370786202038472486947)
                ·
                  refine ⟨172697056179303057708730421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115131370786202038472486947 172697056179303057708730421)
                  ·
                    refine ⟨16190349016809661660193477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172697056179303057708730421 16190349016809661660193477)
                    ·
                      refine ⟨3035690440651811561286277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16190349016809661660193477 3035690440651811561286277)
                      ·
                        rfl

theorem cell23_5911986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_5911986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5911986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5911986 prefixEnd_5911986 := by exact prefixLift 5911986
  have htrace : WordTrace (prefixWord ++ tailWord_5911986) baseStart_5911986 baseEnd_5911986 := by
    simpa [prefixWord, tailWord_5911986, baseEnd_5911986] using wordTrace_append hprefix tailTrace_5911986
  have hstable : (prefixWord ++ tailWord_5911986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5911986).length < 2 ^ (prefixWord ++ tailWord_5911986).sum := by decide
  have hdescent : baseEnd_5911986 < baseStart_5911986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5911986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912003 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 3, 4, 2]
def baseStart_5912003 : Nat := 118140960795 + 5912003 * 2 ^ 59
def prefixEnd_5912003 : Nat := 4983230072969 + 3 ^ 40 * 5912003 * 2
def baseEnd_5912003 : Nat := 3035699169822937994773699

theorem tailTrace_5912003 : CollatzResearch.WordTrace tailWord_5912003 prefixEnd_5912003 3035699169822937994773699 := by
  unfold tailWord_5912003
  simp only [CollatzResearch.WordTrace]
  refine ⟨215628464000830295572004663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143752309333886863714669775 215628464000830295572004663)
  ·
    refine ⟨323442696001245443358006995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215628464000830295572004663 323442696001245443358006995)
    ·
      refine ⟨485164044001868165037010493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323442696001245443358006995 485164044001868165037010493)
      ·
        refine ⟨181936516500700561888878935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485164044001868165037010493 181936516500700561888878935)
        ·
          refine ⟨272904774751050842833318403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181936516500700561888878935 272904774751050842833318403)
          ·
            refine ⟨409357162126576264249977605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272904774751050842833318403 409357162126576264249977605)
            ·
              refine ⟨76754467898733049546870801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409357162126576264249977605 76754467898733049546870801)
              ·
                refine ⟨57565850924049787160153101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76754467898733049546870801 57565850924049787160153101)
                ·
                  refine ⟨21587194096518670185057413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57565850924049787160153101 21587194096518670185057413)
                  ·
                    refine ⟨4047598893097250659698265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21587194096518670185057413 4047598893097250659698265)
                    ·
                      refine ⟨3035699169822937994773699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047598893097250659698265 3035699169822937994773699)
                      ·
                        rfl

theorem cell23_5912003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_5912003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912003 prefixEnd_5912003 := by exact prefixLift 5912003
  have htrace : WordTrace (prefixWord ++ tailWord_5912003) baseStart_5912003 baseEnd_5912003 := by
    simpa [prefixWord, tailWord_5912003, baseEnd_5912003] using wordTrace_append hprefix tailTrace_5912003
  have hstable : (prefixWord ++ tailWord_5912003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912003).length < 2 ^ (prefixWord ++ tailWord_5912003).sum := by decide
  have hdescent : baseEnd_5912003 < baseStart_5912003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912037 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5912037 : Nat := 118140960795 + 5912037 * 2 ^ 59
def prefixEnd_5912037 : Nat := 4983230072969 + 3 ^ 40 * 5912037 * 2
def baseEnd_5912037 : Nat := 3035716628165190861748543

theorem tailTrace_5912037 : CollatzResearch.WordTrace tailWord_5912037 prefixEnd_5912037 3035716628165190861748543 := by
  unfold tailWord_5912037
  simp only [CollatzResearch.WordTrace]
  refine ⟨215629704082707119378742365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143753136055138079585828243 215629704082707119378742365)
  ·
    refine ⟨80861139031015169767028387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215629704082707119378742365 80861139031015169767028387)
    ·
      refine ⟨121291708546522754650542581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80861139031015169767028387 121291708546522754650542581)
      ·
        refine ⟨11371097676236508248488367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121291708546522754650542581 11371097676236508248488367)
        ·
          refine ⟨17056646514354762372732551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371097676236508248488367 17056646514354762372732551)
          ·
            refine ⟨25584969771532143559098827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17056646514354762372732551 25584969771532143559098827)
            ·
              refine ⟨38377454657298215338648241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25584969771532143559098827 38377454657298215338648241)
              ·
                refine ⟨28783090992973661503986181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38377454657298215338648241 28783090992973661503986181)
                ·
                  refine ⟨5396829561182561531997409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28783090992973661503986181 5396829561182561531997409)
                  ·
                    refine ⟨4047622170886921148998057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396829561182561531997409 4047622170886921148998057)
                    ·
                      refine ⟨3035716628165190861748543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047622170886921148998057 3035716628165190861748543)
                      ·
                        rfl

theorem cell23_5912037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5912037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912037 prefixEnd_5912037 := by exact prefixLift 5912037
  have htrace : WordTrace (prefixWord ++ tailWord_5912037) baseStart_5912037 baseEnd_5912037 := by
    simpa [prefixWord, tailWord_5912037, baseEnd_5912037] using wordTrace_append hprefix tailTrace_5912037
  have hstable : (prefixWord ++ tailWord_5912037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912037).length < 2 ^ (prefixWord ++ tailWord_5912037).sum := by decide
  have hdescent : baseEnd_5912037 < baseStart_5912037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912043 : List Nat := [1, 1, 1, 1, 2, 3, 2, 7, 5]
def baseStart_5912043 : Nat := 118140960795 + 5912043 * 2 ^ 59
def prefixEnd_5912043 : Nat := 4983230072969 + 3 ^ 40 * 5912043 * 2
def baseEnd_5912043 : Nat := 337302189894346426474835

theorem tailTrace_5912043 : CollatzResearch.WordTrace tailWord_5912043 prefixEnd_5912043 337302189894346426474835 := by
  unfold tailWord_5912043
  simp only [CollatzResearch.WordTrace]
  refine ⟨215629922920685382403460783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143753281947123588268973855 215629922920685382403460783)
  ·
    refine ⟨323444884381028073605191175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215629922920685382403460783 323444884381028073605191175)
    ·
      refine ⟨485167326571542110407786763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323444884381028073605191175 485167326571542110407786763)
      ·
        refine ⟨727750989857313165611680145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485167326571542110407786763 727750989857313165611680145)
        ·
          refine ⟨545813242392984874208760109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727750989857313165611680145 545813242392984874208760109)
          ·
            refine ⟨204679965897369327828285041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 545813242392984874208760109 204679965897369327828285041)
            ·
              refine ⟨153509974423026995871213781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204679965897369327828285041 153509974423026995871213781)
              ·
                refine ⟨3597890025539695215731573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153509974423026995871213781 3597890025539695215731573)
                ·
                  refine ⟨337302189894346426474835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3597890025539695215731573 337302189894346426474835)
                  ·
                    rfl

theorem cell23_5912043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 5].length) (baseStart_5912043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912043 prefixEnd_5912043 := by exact prefixLift 5912043
  have htrace : WordTrace (prefixWord ++ tailWord_5912043) baseStart_5912043 baseEnd_5912043 := by
    simpa [prefixWord, tailWord_5912043, baseEnd_5912043] using wordTrace_append hprefix tailTrace_5912043
  have hstable : (prefixWord ++ tailWord_5912043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912043).length < 2 ^ (prefixWord ++ tailWord_5912043).sum := by decide
  have hdescent : baseEnd_5912043 < baseStart_5912043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912071 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5912071 : Nat := 118140960795 + 5912071 * 2 ^ 59
def prefixEnd_5912071 : Nat := 4983230072969 + 3 ^ 40 * 5912071 * 2
def baseEnd_5912071 : Nat := 3035734086507443728723387

theorem tailTrace_5912071 : CollatzResearch.WordTrace tailWord_5912071 prefixEnd_5912071 3035734086507443728723387 := by
  unfold tailWord_5912071
  simp only [CollatzResearch.WordTrace]
  refine ⟨215630944164583943185480067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143753962776389295456986711 215630944164583943185480067)
  ·
    refine ⟨323446416246875914778220101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215630944164583943185480067 323446416246875914778220101)
    ·
      refine ⟨60646203046289234020916269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323446416246875914778220101 60646203046289234020916269)
      ·
        refine ⟨22742326142358462757843601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60646203046289234020916269 22742326142358462757843601)
        ·
          refine ⟨17056744606768847068382701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22742326142358462757843601 17056744606768847068382701)
          ·
            refine ⟨6396279227538317650643513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17056744606768847068382701 6396279227538317650643513)
            ·
              refine ⟨4797209420653738237982635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6396279227538317650643513 4797209420653738237982635)
              ·
                refine ⟨7195814130980607356973953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797209420653738237982635 7195814130980607356973953)
                ·
                  refine ⟨5396860598235455517730465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7195814130980607356973953 5396860598235455517730465)
                  ·
                    refine ⟨4047645448676591638297849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5396860598235455517730465 4047645448676591638297849)
                    ·
                      refine ⟨3035734086507443728723387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047645448676591638297849 3035734086507443728723387)
                      ·
                        rfl

theorem cell23_5912071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5912071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912071 prefixEnd_5912071 := by exact prefixLift 5912071
  have htrace : WordTrace (prefixWord ++ tailWord_5912071) baseStart_5912071 baseEnd_5912071 := by
    simpa [prefixWord, tailWord_5912071, baseEnd_5912071] using wordTrace_append hprefix tailTrace_5912071
  have hstable : (prefixWord ++ tailWord_5912071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912071).length < 2 ^ (prefixWord ++ tailWord_5912071).sum := by decide
  have hdescent : baseEnd_5912071 < baseStart_5912071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912113 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_5912113 : Nat := 118140960795 + 5912113 * 2 ^ 59
def prefixEnd_5912113 : Nat := 4983230072969 + 3 ^ 40 * 5912113 * 2
def baseEnd_5912113 : Nat := 3035755652694932564398193

theorem tailTrace_5912113 : CollatzResearch.WordTrace tailWord_5912113 prefixEnd_5912113 3035755652694932564398193 := by
  unfold tailWord_5912113
  simp only [CollatzResearch.WordTrace]
  refine ⟨215632476030431784358508993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143754984020287856239005995 215632476030431784358508993)
  ·
    refine ⟨161724357022823838268881745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215632476030431784358508993 161724357022823838268881745)
    ·
      refine ⟨121293267767117878701661309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161724357022823838268881745 121293267767117878701661309)
      ·
        refine ⟨45484975412669204513122991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121293267767117878701661309 45484975412669204513122991)
        ·
          refine ⟨68227463119003806769684487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45484975412669204513122991 68227463119003806769684487)
          ·
            refine ⟨102341194678505710154526731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68227463119003806769684487 102341194678505710154526731)
            ·
              refine ⟨153511792017758565231790097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102341194678505710154526731 153511792017758565231790097)
              ·
                refine ⟨115133844013318923923842573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153511792017758565231790097 115133844013318923923842573)
                ·
                  refine ⟨43175191504994596471440965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115133844013318923923842573 43175191504994596471440965)
                  ·
                    refine ⟨8095348407186486838395181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43175191504994596471440965 8095348407186486838395181)
                    ·
                      refine ⟨3035755652694932564398193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095348407186486838395181 3035755652694932564398193)
                      ·
                        rfl

theorem cell23_5912113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_5912113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912113 prefixEnd_5912113 := by exact prefixLift 5912113
  have htrace : WordTrace (prefixWord ++ tailWord_5912113) baseStart_5912113 baseEnd_5912113 := by
    simpa [prefixWord, tailWord_5912113, baseEnd_5912113] using wordTrace_append hprefix tailTrace_5912113
  have hstable : (prefixWord ++ tailWord_5912113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912113).length < 2 ^ (prefixWord ++ tailWord_5912113).sum := by decide
  have hdescent : baseEnd_5912113 < baseStart_5912113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912133 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 6]
def baseStart_5912133 : Nat := 118140960795 + 5912133 * 2 ^ 59
def prefixEnd_5912133 : Nat := 4983230072969 + 3 ^ 40 * 5912133 * 2
def baseEnd_5912133 : Nat := 337307324700891387349789

theorem tailTrace_5912133 : CollatzResearch.WordTrace tailWord_5912133 prefixEnd_5912133 337307324700891387349789 := by
  unfold tailWord_5912133
  simp only [CollatzResearch.WordTrace]
  refine ⟨215633205490359327774237053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143755470326906218516158035 215633205490359327774237053)
  ·
    refine ⟨80862452058884747915338895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215633205490359327774237053 80862452058884747915338895)
    ·
      refine ⟨121293678088327121873008343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80862452058884747915338895 121293678088327121873008343)
      ·
        refine ⟨181940517132490682809512515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121293678088327121873008343 181940517132490682809512515)
        ·
          refine ⟨272910775698736024214268773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181940517132490682809512515 272910775698736024214268773)
          ·
            refine ⟨51170770443513004540175395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272910775698736024214268773 51170770443513004540175395)
            ·
              refine ⟨76756155665269506810263093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51170770443513004540175395 76756155665269506810263093)
              ·
                refine ⟨7195889593619016263462165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76756155665269506810263093 7195889593619016263462165)
                ·
                  refine ⟨337307324700891387349789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7195889593619016263462165 337307324700891387349789)
                  ·
                    rfl

theorem cell23_5912133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_5912133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912133 prefixEnd_5912133 := by exact prefixLift 5912133
  have htrace : WordTrace (prefixWord ++ tailWord_5912133) baseStart_5912133 baseEnd_5912133 := by
    simpa [prefixWord, tailWord_5912133, baseEnd_5912133] using wordTrace_append hprefix tailTrace_5912133
  have hstable : (prefixWord ++ tailWord_5912133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912133).length < 2 ^ (prefixWord ++ tailWord_5912133).sum := by decide
  have hdescent : baseEnd_5912133 < baseStart_5912133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912160 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3]
def baseStart_5912160 : Nat := 118140960795 + 5912160 * 2 ^ 59
def prefixEnd_5912160 : Nat := 4983230072969 + 3 ^ 40 * 5912160 * 2
def baseEnd_5912160 : Nat := 3035779786285693880510477

theorem tailTrace_5912160 : CollatzResearch.WordTrace tailWord_5912160 prefixEnd_5912160 3035779786285693880510477 := by
  unfold tailWord_5912160
  simp only [CollatzResearch.WordTrace]
  refine ⟨107817095130630755692734967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143756126840841007590313289 107817095130630755692734967)
  ·
    refine ⟨161725642695946133539102451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107817095130630755692734967 161725642695946133539102451)
    ·
      refine ⟨242588464043919200308653677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161725642695946133539102451 242588464043919200308653677)
      ·
        refine ⟨90970674016469700115745129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242588464043919200308653677 90970674016469700115745129)
        ·
          refine ⟨68228005512352275086808847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90970674016469700115745129 68228005512352275086808847)
          ·
            refine ⟨102342008268528412630213271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68228005512352275086808847 102342008268528412630213271)
            ·
              refine ⟨153513012402792618945319907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102342008268528412630213271 153513012402792618945319907)
              ·
                refine ⟨230269518604188928417979861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153513012402792618945319907 230269518604188928417979861)
                ·
                  refine ⟨5396941842285678009796403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 230269518604188928417979861 5396941842285678009796403)
                  ·
                    refine ⟨8095412763428517014694605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5396941842285678009796403 8095412763428517014694605)
                    ·
                      refine ⟨3035779786285693880510477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095412763428517014694605 3035779786285693880510477)
                      ·
                        rfl

theorem cell23_5912160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_5912160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912160 prefixEnd_5912160 := by exact prefixLift 5912160
  have htrace : WordTrace (prefixWord ++ tailWord_5912160) baseStart_5912160 baseEnd_5912160 := by
    simpa [prefixWord, tailWord_5912160, baseEnd_5912160] using wordTrace_append hprefix tailTrace_5912160
  have hstable : (prefixWord ++ tailWord_5912160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912160).length < 2 ^ (prefixWord ++ tailWord_5912160).sum := by decide
  have hdescent : baseEnd_5912160 < baseStart_5912160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912203 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_5912203 : Nat := 118140960795 + 5912203 * 2 ^ 59
def prefixEnd_5912203 : Nat := 4983230072969 + 3 ^ 40 * 5912203 * 2
def baseEnd_5912203 : Nat := 3035801865953837212272779

theorem tailTrace_5912203 : CollatzResearch.WordTrace tailWord_5912203 prefixEnd_5912203 3035801865953837212272779 := by
  unfold tailWord_5912203
  simp only [CollatzResearch.WordTrace]
  refine ⟨215635758600105729729285263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143757172400070486486190175 215635758600105729729285263)
  ·
    refine ⟨323453637900158594593927895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215635758600105729729285263 323453637900158594593927895)
    ·
      refine ⟨485180456850237891890891843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323453637900158594593927895 485180456850237891890891843)
      ·
        refine ⟨727770685275356837836337765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485180456850237891890891843 727770685275356837836337765)
        ·
          refine ⟨136457003489129407094313331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 727770685275356837836337765 136457003489129407094313331)
          ·
            refine ⟨204685505233694110641469997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136457003489129407094313331 204685505233694110641469997)
            ·
              refine ⟨76757064462635291490551249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204685505233694110641469997 76757064462635291490551249)
              ·
                refine ⟨57567798346976468617913437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76757064462635291490551249 57567798346976468617913437)
                ·
                  refine ⟨21587924380116175731717539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57567798346976468617913437 21587924380116175731717539)
                  ·
                    refine ⟨32381886570174263597576309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21587924380116175731717539 32381886570174263597576309)
                    ·
                      refine ⟨3035801865953837212272779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32381886570174263597576309 3035801865953837212272779)
                      ·
                        rfl

theorem cell23_5912203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_5912203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912203 prefixEnd_5912203 := by exact prefixLift 5912203
  have htrace : WordTrace (prefixWord ++ tailWord_5912203) baseStart_5912203 baseEnd_5912203 := by
    simpa [prefixWord, tailWord_5912203, baseEnd_5912203] using wordTrace_append hprefix tailTrace_5912203
  have hstable : (prefixWord ++ tailWord_5912203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912203).length < 2 ^ (prefixWord ++ tailWord_5912203).sum := by decide
  have hdescent : baseEnd_5912203 < baseStart_5912203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912237 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_5912237 : Nat := 118140960795 + 5912237 * 2 ^ 59
def prefixEnd_5912237 : Nat := 4983230072969 + 3 ^ 40 * 5912237 * 2
def baseEnd_5912237 : Nat := 3035819324296090079247623

theorem tailTrace_5912237 : CollatzResearch.WordTrace tailWord_5912237 prefixEnd_5912237 3035819324296090079247623 := by
  unfold tailWord_5912237
  simp only [CollatzResearch.WordTrace]
  refine ⟨215636998681982553536022965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143757999121321702357348643 215636998681982553536022965)
  ·
    refine ⟨20215968626435864394002153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 215636998681982553536022965 20215968626435864394002153)
    ·
      refine ⟨15161976469826898295501615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20215968626435864394002153 15161976469826898295501615)
      ·
        refine ⟨22742964704740347443252423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15161976469826898295501615 22742964704740347443252423)
        ·
          refine ⟨34114447057110521164878635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22742964704740347443252423 34114447057110521164878635)
          ·
            refine ⟨51171670585665781747317953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34114447057110521164878635 51171670585665781747317953)
            ·
              refine ⟨38378752939249336310488465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51171670585665781747317953 38378752939249336310488465)
              ·
                refine ⟨28784064704437002232866349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38378752939249336310488465 28784064704437002232866349)
                ·
                  refine ⟨10794024264163875837324881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28784064704437002232866349 10794024264163875837324881)
                  ·
                    refine ⟨8095518198122906877993661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10794024264163875837324881 8095518198122906877993661)
                    ·
                      refine ⟨3035819324296090079247623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095518198122906877993661 3035819324296090079247623)
                      ·
                        rfl

theorem cell23_5912237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_5912237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912237 prefixEnd_5912237 := by exact prefixLift 5912237
  have htrace : WordTrace (prefixWord ++ tailWord_5912237) baseStart_5912237 baseEnd_5912237 := by
    simpa [prefixWord, tailWord_5912237, baseEnd_5912237] using wordTrace_append hprefix tailTrace_5912237
  have hstable : (prefixWord ++ tailWord_5912237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912237).length < 2 ^ (prefixWord ++ tailWord_5912237).sum := by decide
  have hdescent : baseEnd_5912237 < baseStart_5912237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912243 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_5912243 : Nat := 118140960795 + 5912243 * 2 ^ 59
def prefixEnd_5912243 : Nat := 4983230072969 + 3 ^ 40 * 5912243 * 2
def baseEnd_5912243 : Nat := 3035822405180017055772595

theorem tailTrace_5912243 : CollatzResearch.WordTrace tailWord_5912243 prefixEnd_5912243 3035822405180017055772595 := by
  unfold tailWord_5912243
  simp only [CollatzResearch.WordTrace]
  refine ⟨215637217519960816560741383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143758145013307211040494255 215637217519960816560741383)
  ·
    refine ⟨323455826279941224841112075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215637217519960816560741383 323455826279941224841112075)
    ·
      refine ⟨485183739419911837261668113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323455826279941224841112075 485183739419911837261668113)
      ·
        refine ⟨363887804564933877946251085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485183739419911837261668113 363887804564933877946251085)
        ·
          refine ⟨136457926711850204229844157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363887804564933877946251085 136457926711850204229844157)
          ·
            refine ⟨51171722516943826586191559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136457926711850204229844157 51171722516943826586191559)
            ·
              refine ⟨76757583775415739879287339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51171722516943826586191559 76757583775415739879287339)
              ·
                refine ⟨115136375663123609818931009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76757583775415739879287339 115136375663123609818931009)
                ·
                  refine ⟨86352281747342707364198257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115136375663123609818931009 86352281747342707364198257)
                  ·
                    refine ⟨64764211310507030523148693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86352281747342707364198257 64764211310507030523148693)
                    ·
                      refine ⟨3035822405180017055772595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64764211310507030523148693 3035822405180017055772595)
                      ·
                        rfl

theorem cell23_5912243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_5912243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912243 prefixEnd_5912243 := by exact prefixLift 5912243
  have htrace : WordTrace (prefixWord ++ tailWord_5912243) baseStart_5912243 baseEnd_5912243 := by
    simpa [prefixWord, tailWord_5912243, baseEnd_5912243] using wordTrace_append hprefix tailTrace_5912243
  have hstable : (prefixWord ++ tailWord_5912243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912243).length < 2 ^ (prefixWord ++ tailWord_5912243).sum := by decide
  have hdescent : baseEnd_5912243 < baseStart_5912243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912254 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_5912254 : Nat := 118140960795 + 5912254 * 2 ^ 59
def prefixEnd_5912254 : Nat := 4983230072969 + 3 ^ 40 * 5912254 * 2
def baseEnd_5912254 : Nat := 3035828053467216512735045

theorem tailTrace_5912254 : CollatzResearch.WordTrace tailWord_5912254 prefixEnd_5912254 3035828053467216512735045 := by
  unfold tailWord_5912254
  simp only [CollatzResearch.WordTrace]
  refine ⟨26954702340365120679923977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143758412481947310292927877 26954702340365120679923977)
  ·
    refine ⟨20216026755273840509942983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26954702340365120679923977 20216026755273840509942983)
    ·
      refine ⟨30324040132910760764914475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20216026755273840509942983 30324040132910760764914475)
      ·
        refine ⟨45486060199366141147371713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30324040132910760764914475 45486060199366141147371713)
        ·
          refine ⟨34114545149524605860528785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45486060199366141147371713 34114545149524605860528785)
          ·
            refine ⟨25585908862143454395396589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34114545149524605860528785 25585908862143454395396589)
            ·
              refine ⟨9594715823303795398273721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25585908862143454395396589 9594715823303795398273721)
              ·
                refine ⟨7196036867477846548705291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594715823303795398273721 7196036867477846548705291)
                ·
                  refine ⟨10794055301216769823057937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7196036867477846548705291 10794055301216769823057937)
                  ·
                    refine ⟨8095541475912577367293453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10794055301216769823057937 8095541475912577367293453)
                    ·
                      refine ⟨3035828053467216512735045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095541475912577367293453 3035828053467216512735045)
                      ·
                        rfl

theorem cell23_5912254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_5912254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912254 prefixEnd_5912254 := by exact prefixLift 5912254
  have htrace : WordTrace (prefixWord ++ tailWord_5912254) baseStart_5912254 baseEnd_5912254 := by
    simpa [prefixWord, tailWord_5912254, baseEnd_5912254] using wordTrace_append hprefix tailTrace_5912254
  have hstable : (prefixWord ++ tailWord_5912254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912254).length < 2 ^ (prefixWord ++ tailWord_5912254).sum := by decide
  have hdescent : baseEnd_5912254 < baseStart_5912254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912278 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5912278 : Nat := 118140960795 + 5912278 * 2 ^ 59
def prefixEnd_5912278 : Nat := 4983230072969 + 3 ^ 40 * 5912278 * 2
def baseEnd_5912278 : Nat := 1011946792334308139611645

theorem tailTrace_5912278 : CollatzResearch.WordTrace tailWord_5912278 prefixEnd_5912278 1011946792334308139611645 := by
  unfold tailWord_5912278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477405879677126096141593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143758996049889345025510325 13477405879677126096141593)
  ·
    refine ⟨10108054409757844572106195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13477405879677126096141593 10108054409757844572106195)
    ·
      refine ⟨15162081614636766858159293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10108054409757844572106195 15162081614636766858159293)
      ·
        refine ⟨5685780605488787571809735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15162081614636766858159293 5685780605488787571809735)
        ·
          refine ⟨8528670908233181357714603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685780605488787571809735 8528670908233181357714603)
          ·
            refine ⟨12793006362349772036571905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8528670908233181357714603 12793006362349772036571905)
            ·
              refine ⟨9594754771762329027428929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12793006362349772036571905 9594754771762329027428929)
              ·
                refine ⟨7196066078821746770571697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594754771762329027428929 7196066078821746770571697)
                ·
                  refine ⟨5397049559116310077928773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7196066078821746770571697 5397049559116310077928773)
                  ·
                    refine ⟨1011946792334308139611645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397049559116310077928773 1011946792334308139611645)
                    ·
                      rfl

theorem cell23_5912278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5912278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912278 prefixEnd_5912278 := by exact prefixLift 5912278
  have htrace : WordTrace (prefixWord ++ tailWord_5912278) baseStart_5912278 baseEnd_5912278 := by
    simpa [prefixWord, tailWord_5912278, baseEnd_5912278] using wordTrace_append hprefix tailTrace_5912278
  have hstable : (prefixWord ++ tailWord_5912278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912278).length < 2 ^ (prefixWord ++ tailWord_5912278).sum := by decide
  have hdescent : baseEnd_5912278 < baseStart_5912278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912285 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5912285 : Nat := 118140960795 + 5912285 * 2 ^ 59
def prefixEnd_5912285 : Nat := 4983230072969 + 3 ^ 40 * 5912285 * 2
def baseEnd_5912285 : Nat := 3035843971367505891447403

theorem tailTrace_5912285 : CollatzResearch.WordTrace tailWord_5912285 prefixEnd_5912285 3035843971367505891447403 := by
  unfold tailWord_5912285
  simp only [CollatzResearch.WordTrace]
  refine ⟨215638749385808657733770309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143759166257205771822513539 215638749385808657733770309)
  ·
    refine ⟨40432265509839123325081933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215638749385808657733770309 40432265509839123325081933)
    ·
      refine ⟨15162099566189671246905725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40432265509839123325081933 15162099566189671246905725)
      ·
        refine ⟨5685787337321126717589647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15162099566189671246905725 5685787337321126717589647)
        ·
          refine ⟨8528681005981690076384471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685787337321126717589647 8528681005981690076384471)
          ·
            refine ⟨12793021508972535114576707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8528681005981690076384471 12793021508972535114576707)
            ·
              refine ⟨19189532263458802671865061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793021508972535114576707 19189532263458802671865061)
              ·
                refine ⟨3598037299398525500974699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19189532263458802671865061 3598037299398525500974699)
                ·
                  refine ⟨5397055949097788251462049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598037299398525500974699 5397055949097788251462049)
                  ·
                    refine ⟨4047791961823341188596537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397055949097788251462049 4047791961823341188596537)
                    ·
                      refine ⟨3035843971367505891447403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047791961823341188596537 3035843971367505891447403)
                      ·
                        rfl

theorem cell23_5912285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5912285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912285 prefixEnd_5912285 := by exact prefixLift 5912285
  have htrace : WordTrace (prefixWord ++ tailWord_5912285) baseStart_5912285 baseEnd_5912285 := by
    simpa [prefixWord, tailWord_5912285, baseEnd_5912285] using wordTrace_append hprefix tailTrace_5912285
  have hstable : (prefixWord ++ tailWord_5912285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912285).length < 2 ^ (prefixWord ++ tailWord_5912285).sum := by decide
  have hdescent : baseEnd_5912285 < baseStart_5912285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912307 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 1, 4, 2]
def baseStart_5912307 : Nat := 118140960795 + 5912307 * 2 ^ 59
def prefixEnd_5912307 : Nat := 4983230072969 + 3 ^ 40 * 5912307 * 2
def baseEnd_5912307 : Nat := 3035855267941904805372301

theorem tailTrace_5912307 : CollatzResearch.WordTrace tailWord_5912307 prefixEnd_5912307 3035855267941904805372301 := by
  unfold tailWord_5912307
  simp only [CollatzResearch.WordTrace]
  refine ⟨215639551791728955491071175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143759701194485970327380783 215639551791728955491071175)
  ·
    refine ⟨323459327687593433236606763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215639551791728955491071175 323459327687593433236606763)
    ·
      refine ⟨485188991531390149854910145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323459327687593433236606763 485188991531390149854910145)
      ·
        refine ⟨363891743648542612391182609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485188991531390149854910145 363891743648542612391182609)
        ·
          refine ⟨272918807736406959293386957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363891743648542612391182609 272918807736406959293386957)
          ·
            refine ⟨102344552901152609735020109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 272918807736406959293386957 102344552901152609735020109)
            ·
              refine ⟨38379207337932228650632541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102344552901152609735020109 38379207337932228650632541)
              ·
                refine ⟨14392202751724585743987203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38379207337932228650632541 14392202751724585743987203)
                ·
                  refine ⟨21588304127586878615980805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14392202751724585743987203 21588304127586878615980805)
                  ·
                    refine ⟨4047807023922539740496401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21588304127586878615980805 4047807023922539740496401)
                    ·
                      refine ⟨3035855267941904805372301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047807023922539740496401 3035855267941904805372301)
                      ·
                        rfl

theorem cell23_5912307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 4, 2].length) (baseStart_5912307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912307 prefixEnd_5912307 := by exact prefixLift 5912307
  have htrace : WordTrace (prefixWord ++ tailWord_5912307) baseStart_5912307 baseEnd_5912307 := by
    simpa [prefixWord, tailWord_5912307, baseEnd_5912307] using wordTrace_append hprefix tailTrace_5912307
  have hstable : (prefixWord ++ tailWord_5912307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912307).length < 2 ^ (prefixWord ++ tailWord_5912307).sum := by decide
  have hdescent : baseEnd_5912307 < baseStart_5912307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912324 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5912324 : Nat := 118140960795 + 5912324 * 2 ^ 59
def prefixEnd_5912324 : Nat := 4983230072969 + 3 ^ 40 * 5912324 * 2
def baseEnd_5912324 : Nat := 3035863997113031238859723

theorem tailTrace_5912324 : CollatzResearch.WordTrace tailWord_5912324 prefixEnd_5912324 3035863997113031238859723 := by
  unfold tailWord_5912324
  simp only [CollatzResearch.WordTrace]
  refine ⟨107820085916333683697220013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143760114555111578262960017 107820085916333683697220013)
  ·
    refine ⟨40432532218625131386457505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107820085916333683697220013 40432532218625131386457505)
    ·
      refine ⟨30324399163968848539843129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40432532218625131386457505 30324399163968848539843129)
      ·
        refine ⟨22743299372976636404882347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30324399163968848539843129 22743299372976636404882347)
        ·
          refine ⟨34114949059464954607323521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22743299372976636404882347 34114949059464954607323521)
          ·
            refine ⟨25586211794598715955492641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34114949059464954607323521 25586211794598715955492641)
            ·
              refine ⟨19189658845949036966619481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25586211794598715955492641 19189658845949036966619481)
              ·
                refine ⟨14392244134461777724964611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19189658845949036966619481 14392244134461777724964611)
                ·
                  refine ⟨21588366201692666587446917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14392244134461777724964611 21588366201692666587446917)
                  ·
                    refine ⟨4047818662817374985146297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21588366201692666587446917 4047818662817374985146297)
                    ·
                      refine ⟨3035863997113031238859723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047818662817374985146297 3035863997113031238859723)
                      ·
                        rfl

theorem cell23_5912324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5912324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912324 prefixEnd_5912324 := by exact prefixLift 5912324
  have htrace : WordTrace (prefixWord ++ tailWord_5912324) baseStart_5912324 baseEnd_5912324 := by
    simpa [prefixWord, tailWord_5912324, baseEnd_5912324] using wordTrace_append hprefix tailTrace_5912324
  have hstable : (prefixWord ++ tailWord_5912324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912324).length < 2 ^ (prefixWord ++ tailWord_5912324).sum := by decide
  have hdescent : baseEnd_5912324 < baseStart_5912324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912341 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_5912341 : Nat := 118140960795 + 5912341 * 2 ^ 59
def prefixEnd_5912341 : Nat := 4983230072969 + 3 ^ 40 * 5912341 * 2
def baseEnd_5912341 : Nat := 3035872726284157672347145

theorem tailTrace_5912341 : CollatzResearch.WordTrace tailWord_5912341 prefixEnd_5912341 3035872726284157672347145 := by
  unfold tailWord_5912341
  simp only [CollatzResearch.WordTrace]
  refine ⟨215640791873605779297808877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143760527915737186198539251 215640791873605779297808877)
  ·
    refine ⟨80865296952602167236678329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215640791873605779297808877 80865296952602167236678329)
    ·
      refine ⟨60648972714451625427508747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80865296952602167236678329 60648972714451625427508747)
      ·
        refine ⟨90973459071677438141263121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60648972714451625427508747 90973459071677438141263121)
        ·
          refine ⟨68230094303758078605947341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90973459071677438141263121 68230094303758078605947341)
          ·
            refine ⟨25586285363909279477230253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68230094303758078605947341 25586285363909279477230253)
            ·
              refine ⟨9594857011465979803961345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25586285363909279477230253 9594857011465979803961345)
              ·
                refine ⟨7196142758599484852971009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9594857011465979803961345 7196142758599484852971009)
                ·
                  refine ⟨5397107068949613639728257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7196142758599484852971009 5397107068949613639728257)
                  ·
                    refine ⟨4047830301712210229796193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397107068949613639728257 4047830301712210229796193)
                    ·
                      refine ⟨3035872726284157672347145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4047830301712210229796193 3035872726284157672347145)
                      ·
                        rfl

theorem cell23_5912341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_5912341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912341 prefixEnd_5912341 := by exact prefixLift 5912341
  have htrace : WordTrace (prefixWord ++ tailWord_5912341) baseStart_5912341 baseEnd_5912341 := by
    simpa [prefixWord, tailWord_5912341, baseEnd_5912341] using wordTrace_append hprefix tailTrace_5912341
  have hstable : (prefixWord ++ tailWord_5912341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912341).length < 2 ^ (prefixWord ++ tailWord_5912341).sum := by decide
  have hdescent : baseEnd_5912341 < baseStart_5912341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912357 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_5912357 : Nat := 118140960795 + 5912357 * 2 ^ 59
def prefixEnd_5912357 : Nat := 4983230072969 + 3 ^ 40 * 5912357 * 2
def baseEnd_5912357 : Nat := 3035880941974629609747071

theorem tailTrace_5912357 : CollatzResearch.WordTrace tailWord_5912357 prefixEnd_5912357 3035880941974629609747071 := by
  unfold tailWord_5912357
  simp only [CollatzResearch.WordTrace]
  refine ⟨215641375441547814030391325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143760916961031876020260883 215641375441547814030391325)
  ·
    refine ⟨80865515790580430261396747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215641375441547814030391325 80865515790580430261396747)
    ·
      refine ⟨121298273685870645392095121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80865515790580430261396747 121298273685870645392095121)
      ·
        refine ⟨90973705264402984044071341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121298273685870645392095121 90973705264402984044071341)
        ·
          refine ⟨34115139474151119016526753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90973705264402984044071341 34115139474151119016526753)
          ·
            refine ⟨25586354605613339262395065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34115139474151119016526753 25586354605613339262395065)
            ·
              refine ⟨19189765954210004446796299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25586354605613339262395065 19189765954210004446796299)
              ·
                refine ⟨28784648931315006670194449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19189765954210004446796299 28784648931315006670194449)
                ·
                  refine ⟨21588486698486255002645837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28784648931315006670194449 21588486698486255002645837)
                  ·
                    refine ⟨8095682511932345625992189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21588486698486255002645837 8095682511932345625992189)
                    ·
                      refine ⟨3035880941974629609747071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095682511932345625992189 3035880941974629609747071)
                      ·
                        rfl

theorem cell23_5912357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_5912357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912357 prefixEnd_5912357 := by exact prefixLift 5912357
  have htrace : WordTrace (prefixWord ++ tailWord_5912357) baseStart_5912357 baseEnd_5912357 := by
    simpa [prefixWord, tailWord_5912357, baseEnd_5912357] using wordTrace_append hprefix tailTrace_5912357
  have hstable : (prefixWord ++ tailWord_5912357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912357).length < 2 ^ (prefixWord ++ tailWord_5912357).sum := by decide
  have hdescent : baseEnd_5912357 < baseStart_5912357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912381 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 5]
def baseStart_5912381 : Nat := 118140960795 + 5912381 * 2 ^ 59
def prefixEnd_5912381 : Nat := 4983230072969 + 3 ^ 40 * 5912381 * 2
def baseEnd_5912381 : Nat := 337321473945593057316329

theorem tailTrace_5912381 : CollatzResearch.WordTrace tailWord_5912381 prefixEnd_5912381 337321473945593057316329 := by
  unfold tailWord_5912381
  simp only [CollatzResearch.WordTrace]
  refine ⟨215642250793460866129264997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143761500528973910752843331 215642250793460866129264997)
  ·
    refine ⟨40432922023773912399237187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215642250793460866129264997 40432922023773912399237187)
    ·
      refine ⟨60649383035660868598855781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40432922023773912399237187 60649383035660868598855781)
      ·
        refine ⟨11371759319186412862285459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60649383035660868598855781 11371759319186412862285459)
        ·
          refine ⟨17057638978779619293428189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371759319186412862285459 17057638978779619293428189)
          ·
            refine ⟨6396614617042357235035571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17057638978779619293428189 6396614617042357235035571)
            ·
              refine ⟨9594921925563535852553357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396614617042357235035571 9594921925563535852553357)
              ·
                refine ⟨3598095722086325944707509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9594921925563535852553357 3598095722086325944707509)
                ·
                  refine ⟨337321473945593057316329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598095722086325944707509 337321473945593057316329)
                  ·
                    rfl

theorem cell23_5912381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_5912381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912381 prefixEnd_5912381 := by exact prefixLift 5912381
  have htrace : WordTrace (prefixWord ++ tailWord_5912381) baseStart_5912381 baseEnd_5912381 := by
    simpa [prefixWord, tailWord_5912381, baseEnd_5912381] using wordTrace_append hprefix tailTrace_5912381
  have hstable : (prefixWord ++ tailWord_5912381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912381).length < 2 ^ (prefixWord ++ tailWord_5912381).sum := by decide
  have hdescent : baseEnd_5912381 < baseStart_5912381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912417 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_5912417 : Nat := 118140960795 + 5912417 * 2 ^ 59
def prefixEnd_5912417 : Nat := 4983230072969 + 3 ^ 40 * 5912417 * 2
def baseEnd_5912417 : Nat := 3035911750813899374996795

theorem tailTrace_5912417 : CollatzResearch.WordTrace tailWord_5912417 prefixEnd_5912417 3035911750813899374996795 := by
  unfold tailWord_5912417
  simp only [CollatzResearch.WordTrace]
  refine ⟨215643563821330444277575505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143762375880886962851717003 215643563821330444277575505)
  ·
    refine ⟨161732672865997833208181629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215643563821330444277575505 161732672865997833208181629)
    ·
      refine ⟨60649752324749187453068111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161732672865997833208181629 60649752324749187453068111)
      ·
        refine ⟨90974628487123781179602167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60649752324749187453068111 90974628487123781179602167)
        ·
          refine ⟨136461942730685671769403251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90974628487123781179602167 136461942730685671769403251)
          ·
            refine ⟨204692914096028507654104877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136461942730685671769403251 204692914096028507654104877)
            ·
              refine ⟨76759842786010690370289329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204692914096028507654104877 76759842786010690370289329)
              ·
                refine ⟨57569882089508017777716997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76759842786010690370289329 57569882089508017777716997)
                ·
                  refine ⟨10794352891782753333321937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57569882089508017777716997 10794352891782753333321937)
                  ·
                    refine ⟨8095764668837064999991453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10794352891782753333321937 8095764668837064999991453)
                    ·
                      refine ⟨3035911750813899374996795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095764668837064999991453 3035911750813899374996795)
                      ·
                        rfl

theorem cell23_5912417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_5912417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912417 prefixEnd_5912417 := by exact prefixLift 5912417
  have htrace : WordTrace (prefixWord ++ tailWord_5912417) baseStart_5912417 baseEnd_5912417 := by
    simpa [prefixWord, tailWord_5912417, baseEnd_5912417] using wordTrace_append hprefix tailTrace_5912417
  have hstable : (prefixWord ++ tailWord_5912417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912417).length < 2 ^ (prefixWord ++ tailWord_5912417).sum := by decide
  have hdescent : baseEnd_5912417 < baseStart_5912417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912458 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_5912458 : Nat := 118140960795 + 5912458 * 2 ^ 59
def prefixEnd_5912458 : Nat := 4983230072969 + 3 ^ 40 * 5912458 * 2
def baseEnd_5912458 : Nat := 1011977601173577904861369

theorem tailTrace_5912458 : CollatzResearch.WordTrace tailWord_5912458 prefixEnd_5912458 1011977601173577904861369 := by
  unfold tailWord_5912458
  simp only [CollatzResearch.WordTrace]
  refine ⟨53911264803545477069954507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143763372809454605519878685 53911264803545477069954507)
  ·
    refine ⟨80866897205318215604931761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53911264803545477069954507 80866897205318215604931761)
    ·
      refine ⟨60650172903988661703698821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80866897205318215604931761 60650172903988661703698821)
      ·
        refine ⟨11371907419497874069443529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60650172903988661703698821 11371907419497874069443529)
        ·
          refine ⟨8528930564623405552082647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11371907419497874069443529 8528930564623405552082647)
          ·
            refine ⟨12793395846935108328123971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8528930564623405552082647 12793395846935108328123971)
            ·
              refine ⟨19190093770402662492185957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793395846935108328123971 19190093770402662492185957)
              ·
                refine ⟨3598142581950499217284867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19190093770402662492185957 3598142581950499217284867)
                ·
                  refine ⟨5397213872925748825927301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598142581950499217284867 5397213872925748825927301)
                  ·
                    refine ⟨1011977601173577904861369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397213872925748825927301 1011977601173577904861369)
                    ·
                      rfl

theorem cell23_5912458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_5912458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912458 prefixEnd_5912458 := by exact prefixLift 5912458
  have htrace : WordTrace (prefixWord ++ tailWord_5912458) baseStart_5912458 baseEnd_5912458 := by
    simpa [prefixWord, tailWord_5912458, baseEnd_5912458] using wordTrace_append hprefix tailTrace_5912458
  have hstable : (prefixWord ++ tailWord_5912458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912458).length < 2 ^ (prefixWord ++ tailWord_5912458).sum := by decide
  have hdescent : baseEnd_5912458 < baseStart_5912458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912501 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5912501 : Nat := 118140960795 + 5912501 * 2 ^ 59
def prefixEnd_5912501 : Nat := 4983230072969 + 3 ^ 40 * 5912501 * 2
def baseEnd_5912501 : Nat := 1011984961062959015448803

theorem tailTrace_5912501 : CollatzResearch.WordTrace tailWord_5912501 prefixEnd_5912501 1011984961062959015448803 := by
  unfold tailWord_5912501
  simp only [CollatzResearch.WordTrace]
  refine ⟨215646627553026126623633357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143764418368684084415755571 215646627553026126623633357)
  ·
    refine ⟨80867485332384797483862509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215646627553026126623633357 80867485332384797483862509)
    ·
      refine ⟨30325306999644299056448441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80867485332384797483862509 30325306999644299056448441)
      ·
        refine ⟨22743980249733224292336331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30325306999644299056448441 22743980249733224292336331)
        ·
          refine ⟨34115970374599836438504497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22743980249733224292336331 34115970374599836438504497)
          ·
            refine ⟨25586977780949877328878373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34115970374599836438504497 25586977780949877328878373)
            ·
              refine ⟨4797558333928101999164695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25586977780949877328878373 4797558333928101999164695)
              ·
                refine ⟨7196337500892152998747043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797558333928101999164695 7196337500892152998747043)
                ·
                  refine ⟨10794506251338229498120565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7196337500892152998747043 10794506251338229498120565)
                  ·
                    refine ⟨1011984961062959015448803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10794506251338229498120565 1011984961062959015448803)
                    ·
                      rfl

theorem cell23_5912501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5912501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912501 prefixEnd_5912501 := by exact prefixLift 5912501
  have htrace : WordTrace (prefixWord ++ tailWord_5912501) baseStart_5912501 baseEnd_5912501 := by
    simpa [prefixWord, tailWord_5912501, baseEnd_5912501] using wordTrace_append hprefix tailTrace_5912501
  have hstable : (prefixWord ++ tailWord_5912501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912501).length < 2 ^ (prefixWord ++ tailWord_5912501).sum := by decide
  have hdescent : baseEnd_5912501 < baseStart_5912501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912504 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_5912504 : Nat := 118140960795 + 5912504 * 2 ^ 59
def prefixEnd_5912504 : Nat := 4983230072969 + 3 ^ 40 * 5912504 * 2
def baseEnd_5912504 : Nat := 3035956423630840534608895

theorem tailTrace_5912504 : CollatzResearch.WordTrace tailWord_5912504 prefixEnd_5912504 3035956423630840534608895 := by
  unfold tailWord_5912504
  simp only [CollatzResearch.WordTrace]
  refine ⟨107823368486007629067996283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143764491314676838757328377 107823368486007629067996283)
  ·
    refine ⟨161735052729011443601994425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107823368486007629067996283 161735052729011443601994425)
    ·
      refine ⟨121301289546758582701495819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161735052729011443601994425 121301289546758582701495819)
      ·
        refine ⟨181951934320137874052243729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121301289546758582701495819 181951934320137874052243729)
        ·
          refine ⟨136463950740103405539182797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181951934320137874052243729 136463950740103405539182797)
          ·
            refine ⟨51173981527538777077193549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136463950740103405539182797 51173981527538777077193549)
            ·
              refine ⟨19190243072827041403947581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51173981527538777077193549 19190243072827041403947581)
              ·
                refine ⟨7196341152310140526480343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19190243072827041403947581 7196341152310140526480343)
                ·
                  refine ⟨10794511728465210789720515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7196341152310140526480343 10794511728465210789720515)
                  ·
                    refine ⟨16191767592697816184580773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10794511728465210789720515 16191767592697816184580773)
                    ·
                      refine ⟨3035956423630840534608895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16191767592697816184580773 3035956423630840534608895)
                      ·
                        rfl

theorem cell23_5912504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_5912504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912504 prefixEnd_5912504 := by exact prefixLift 5912504
  have htrace : WordTrace (prefixWord ++ tailWord_5912504) baseStart_5912504 baseEnd_5912504 := by
    simpa [prefixWord, tailWord_5912504, baseEnd_5912504] using wordTrace_append hprefix tailTrace_5912504
  have hstable : (prefixWord ++ tailWord_5912504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912504).length < 2 ^ (prefixWord ++ tailWord_5912504).sum := by decide
  have hdescent : baseEnd_5912504 < baseStart_5912504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912524 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5912524 : Nat := 118140960795 + 5912524 * 2 ^ 59
def prefixEnd_5912524 : Nat := 4983230072969 + 3 ^ 40 * 5912524 * 2
def baseEnd_5912524 : Nat := 3035966693243930456358803

theorem tailTrace_5912524 : CollatzResearch.WordTrace tailWord_5912524 prefixEnd_5912524 3035966693243930456358803 := by
  unfold tailWord_5912524
  simp only [CollatzResearch.WordTrace]
  refine ⟨107823733215971400775860313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143764977621295201034480417 107823733215971400775860313)
  ·
    refine ⟨80867799911978550581895235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107823733215971400775860313 80867799911978550581895235)
    ·
      refine ⟨121301699867967825872842853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80867799911978550581895235 121301699867967825872842853)
      ·
        refine ⟨22744068725243967351158035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121301699867967825872842853 22744068725243967351158035)
        ·
          refine ⟨34116103087865951026737053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22744068725243967351158035 34116103087865951026737053)
          ·
            refine ⟨12793538657949731635026395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34116103087865951026737053 12793538657949731635026395)
            ·
              refine ⟨19190307986924597452539593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793538657949731635026395 19190307986924597452539593)
              ·
                refine ⟨14392730990193448089404695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19190307986924597452539593 14392730990193448089404695)
                ·
                  refine ⟨21589096485290172134107043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14392730990193448089404695 21589096485290172134107043)
                  ·
                    refine ⟨32383644727935258201160565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21589096485290172134107043 32383644727935258201160565)
                    ·
                      refine ⟨3035966693243930456358803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32383644727935258201160565 3035966693243930456358803)
                      ·
                        rfl

theorem cell23_5912524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5912524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912524 prefixEnd_5912524 := by exact prefixLift 5912524
  have htrace : WordTrace (prefixWord ++ tailWord_5912524) baseStart_5912524 baseEnd_5912524 := by
    simpa [prefixWord, tailWord_5912524, baseEnd_5912524] using wordTrace_append hprefix tailTrace_5912524
  have hstable : (prefixWord ++ tailWord_5912524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912524).length < 2 ^ (prefixWord ++ tailWord_5912524).sum := by decide
  have hdescent : baseEnd_5912524 < baseStart_5912524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912554 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_5912554 : Nat := 118140960795 + 5912554 * 2 ^ 59
def prefixEnd_5912554 : Nat := 4983230072969 + 3 ^ 40 * 5912554 * 2
def baseEnd_5912554 : Nat := 3035982097663565338983665

theorem tailTrace_5912554 : CollatzResearch.WordTrace tailWord_5912554 prefixEnd_5912554 3035982097663565338983665 := by
  unfold tailWord_5912554
  simp only [CollatzResearch.WordTrace]
  refine ⟨53912140155458529168828179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143765707081222744450208477 53912140155458529168828179)
  ·
    refine ⟨80868210233187793753242269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53912140155458529168828179 80868210233187793753242269)
    ·
      refine ⟨30325578837445422657465851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80868210233187793753242269 30325578837445422657465851)
      ·
        refine ⟨45488368256168133986198777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30325578837445422657465851 45488368256168133986198777)
        ·
          refine ⟨34116276192126100489649083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45488368256168133986198777 34116276192126100489649083)
          ·
            refine ⟨51174414288189150734473625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34116276192126100489649083 51174414288189150734473625)
            ·
              refine ⟨38380810716141863050855219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51174414288189150734473625 38380810716141863050855219)
              ·
                refine ⟨57571216074212794576282829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38380810716141863050855219 57571216074212794576282829)
                ·
                  refine ⟨21589206027829797966106061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57571216074212794576282829 21589206027829797966106061)
                  ·
                    refine ⟨8095952260436174237289773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21589206027829797966106061 8095952260436174237289773)
                    ·
                      refine ⟨3035982097663565338983665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8095952260436174237289773 3035982097663565338983665)
                      ·
                        rfl

theorem cell23_5912554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_5912554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912554 prefixEnd_5912554 := by exact prefixLift 5912554
  have htrace : WordTrace (prefixWord ++ tailWord_5912554) baseStart_5912554 baseEnd_5912554 := by
    simpa [prefixWord, tailWord_5912554, baseEnd_5912554] using wordTrace_append hprefix tailTrace_5912554
  have hstable : (prefixWord ++ tailWord_5912554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912554).length < 2 ^ (prefixWord ++ tailWord_5912554).sum := by decide
  have hdescent : baseEnd_5912554 < baseStart_5912554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912587 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 1, 8]
def baseStart_5912587 : Nat := 118140960795 + 5912587 * 2 ^ 59
def prefixEnd_5912587 : Nat := 4983230072969 + 3 ^ 40 * 5912587 * 2
def baseEnd_5912587 : Nat := 1011999680841721236623671

theorem tailTrace_5912587 : CollatzResearch.WordTrace tailWord_5912587 prefixEnd_5912587 1011999680841721236623671 := by
  unfold tailWord_5912587
  simp only [CollatzResearch.WordTrace]
  refine ⟨215649764230714563311264015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143766509487143042207509343 215649764230714563311264015)
  ·
    refine ⟨323474646346071844966896023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215649764230714563311264015 323474646346071844966896023)
    ·
      refine ⟨485211969519107767450344035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323474646346071844966896023 485211969519107767450344035)
      ·
        refine ⟨727817954278661651175516053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485211969519107767450344035 727817954278661651175516053)
        ·
          refine ⟨34116466606812264898852315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 727817954278661651175516053 34116466606812264898852315)
          ·
            refine ⟨51174699910218397348278473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34116466606812264898852315 51174699910218397348278473)
            ·
              refine ⟨38381024932663798011208855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51174699910218397348278473 38381024932663798011208855)
              ·
                refine ⟨57571537398995697016813283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38381024932663798011208855 57571537398995697016813283)
                ·
                  refine ⟨86357306098493545525219925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57571537398995697016813283 86357306098493545525219925)
                  ·
                    refine ⟨1011999680841721236623671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86357306098493545525219925 1011999680841721236623671)
                    ·
                      rfl

theorem cell23_5912587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_5912587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912587 prefixEnd_5912587 := by exact prefixLift 5912587
  have htrace : WordTrace (prefixWord ++ tailWord_5912587) baseStart_5912587 baseEnd_5912587 := by
    simpa [prefixWord, tailWord_5912587, baseEnd_5912587] using wordTrace_append hprefix tailTrace_5912587
  have hstable : (prefixWord ++ tailWord_5912587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912587).length < 2 ^ (prefixWord ++ tailWord_5912587).sum := by decide
  have hdescent : baseEnd_5912587 < baseStart_5912587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912589 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5912589 : Nat := 118140960795 + 5912589 * 2 ^ 59
def prefixEnd_5912589 : Nat := 4983230072969 + 3 ^ 40 * 5912589 * 2
def baseEnd_5912589 : Nat := 3036000069486472702046005

theorem tailTrace_5912589 : CollatzResearch.WordTrace tailWord_5912589 prefixEnd_5912589 3036000069486472702046005 := by
  unfold tailWord_5912589
  simp only [CollatzResearch.WordTrace]
  refine ⟨215649837176707317652836821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143766558117804878435224547 215649837176707317652836821)
  ·
    refine ⟨5054293058829077757488363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 215649837176707317652836821 5054293058829077757488363)
    ·
      refine ⟨7581439588243616636232545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054293058829077757488363 7581439588243616636232545)
      ·
        refine ⟨5686079691182712477174409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7581439588243616636232545 5686079691182712477174409)
        ·
          refine ⟨4264559768387034357880807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5686079691182712477174409 4264559768387034357880807)
          ·
            refine ⟨6396839652580551536821211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264559768387034357880807 6396839652580551536821211)
            ·
              refine ⟨9595259478870827305231817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396839652580551536821211 9595259478870827305231817)
              ·
                refine ⟨7196444609153120478923863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9595259478870827305231817 7196444609153120478923863)
                ·
                  refine ⟨10794666913729680718385795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7196444609153120478923863 10794666913729680718385795)
                  ·
                    refine ⟨16192000370594521077578693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10794666913729680718385795 16192000370594521077578693)
                    ·
                      refine ⟨3036000069486472702046005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16192000370594521077578693 3036000069486472702046005)
                      ·
                        rfl

theorem cell23_5912589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5912589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912589 prefixEnd_5912589 := by exact prefixLift 5912589
  have htrace : WordTrace (prefixWord ++ tailWord_5912589) baseStart_5912589 baseEnd_5912589 := by
    simpa [prefixWord, tailWord_5912589, baseEnd_5912589] using wordTrace_append hprefix tailTrace_5912589
  have hstable : (prefixWord ++ tailWord_5912589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912589).length < 2 ^ (prefixWord ++ tailWord_5912589).sum := by decide
  have hdescent : baseEnd_5912589 < baseStart_5912589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912611 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 1, 4, 2]
def baseStart_5912611 : Nat := 118140960795 + 5912611 * 2 ^ 59
def prefixEnd_5912611 : Nat := 4983230072969 + 3 ^ 40 * 5912611 * 2
def baseEnd_5912611 : Nat := 3036011366060871615970903

theorem tailTrace_5912611 : CollatzResearch.WordTrace tailWord_5912611 prefixEnd_5912611 3036011366060871615970903 := by
  unfold tailWord_5912611
  simp only [CollatzResearch.WordTrace]
  refine ⟨215650639582627615410137687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143767093055085076940091791 215650639582627615410137687)
  ·
    refine ⟨323475959373941423115206531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215650639582627615410137687 323475959373941423115206531)
    ·
      refine ⟨485213939060912134672809797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323475959373941423115206531 485213939060912134672809797)
      ·
        refine ⟨90977613573921025251151837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 485213939060912134672809797 90977613573921025251151837)
        ·
          refine ⟨34116605090220384469181939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90977613573921025251151837 34116605090220384469181939)
          ·
            refine ⟨51174907635330576703772909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34116605090220384469181939 51174907635330576703772909)
            ·
              refine ⟨19190590363248966263914841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51174907635330576703772909 19190590363248966263914841)
              ·
                refine ⟨14392942772436724697936131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19190590363248966263914841 14392942772436724697936131)
                ·
                  refine ⟨21589414158655087046904197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14392942772436724697936131 21589414158655087046904197)
                  ·
                    refine ⟨4048015154747828821294537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21589414158655087046904197 4048015154747828821294537)
                    ·
                      refine ⟨3036011366060871615970903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048015154747828821294537 3036011366060871615970903)
                      ·
                        rfl

theorem cell23_5912611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_5912611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912611 prefixEnd_5912611 := by exact prefixLift 5912611
  have htrace : WordTrace (prefixWord ++ tailWord_5912611) baseStart_5912611 baseEnd_5912611 := by
    simpa [prefixWord, tailWord_5912611, baseEnd_5912611] using wordTrace_append hprefix tailTrace_5912611
  have hstable : (prefixWord ++ tailWord_5912611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912611).length < 2 ^ (prefixWord ++ tailWord_5912611).sum := by decide
  have hdescent : baseEnd_5912611 < baseStart_5912611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912627 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_5912627 : Nat := 118140960795 + 5912627 * 2 ^ 59
def prefixEnd_5912627 : Nat := 4983230072969 + 3 ^ 40 * 5912627 * 2
def baseEnd_5912627 : Nat := 3036019581751343553370829

theorem tailTrace_5912627 : CollatzResearch.WordTrace tailWord_5912627 prefixEnd_5912627 3036019581751343553370829 := by
  unfold tailWord_5912627
  simp only [CollatzResearch.WordTrace]
  refine ⟨215651223150569650142720135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143767482100379766761813423 215651223150569650142720135)
  ·
    refine ⟨323476834725854475214080203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215651223150569650142720135 323476834725854475214080203)
    ·
      refine ⟨485215252088781712821120305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323476834725854475214080203 485215252088781712821120305)
      ·
        refine ⟨363911439066586284615840229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485215252088781712821120305 363911439066586284615840229)
        ·
          refine ⟨68233394824984928365470043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 363911439066586284615840229 68233394824984928365470043)
          ·
            refine ⟨102350092237477392548205065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68233394824984928365470043 102350092237477392548205065)
            ·
              refine ⟨76762569178108044411153799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102350092237477392548205065 76762569178108044411153799)
              ·
                refine ⟨115143853767162066616730699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76762569178108044411153799 115143853767162066616730699)
                ·
                  refine ⟨172715780650743099925096049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115143853767162066616730699 172715780650743099925096049)
                  ·
                    refine ⟨129536835488057324943822037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172715780650743099925096049 129536835488057324943822037)
                    ·
                      refine ⟨3036019581751343553370829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129536835488057324943822037 3036019581751343553370829)
                      ·
                        rfl

theorem cell23_5912627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_5912627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912627 prefixEnd_5912627 := by exact prefixLift 5912627
  have htrace : WordTrace (prefixWord ++ tailWord_5912627) baseStart_5912627 baseEnd_5912627 := by
    simpa [prefixWord, tailWord_5912627, baseEnd_5912627] using wordTrace_append hprefix tailTrace_5912627
  have hstable : (prefixWord ++ tailWord_5912627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912627).length < 2 ^ (prefixWord ++ tailWord_5912627).sum := by decide
  have hdescent : baseEnd_5912627 < baseStart_5912627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912641 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5912641 : Nat := 118140960795 + 5912641 * 2 ^ 59
def prefixEnd_5912641 : Nat := 4983230072969 + 3 ^ 40 * 5912641 * 2
def baseEnd_5912641 : Nat := 3036026770480506498595765

theorem tailTrace_5912641 : CollatzResearch.WordTrace tailWord_5912641 prefixEnd_5912641 3036026770480506498595765 := by
  unfold tailWord_5912641
  simp only [CollatzResearch.WordTrace]
  refine ⟨215651733772518930533729777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143767822515012620355819851 215651733772518930533729777)
  ·
    refine ⟨161738800329389197900297333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215651733772518930533729777 161738800329389197900297333)
    ·
      refine ⟨15163012530880237303152875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161738800329389197900297333 15163012530880237303152875)
      ·
        refine ⟨22744518796320355954729313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15163012530880237303152875 22744518796320355954729313)
        ·
          refine ⟨17058389097240266966046985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22744518796320355954729313 17058389097240266966046985)
          ·
            refine ⟨12793791822930200224535239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17058389097240266966046985 12793791822930200224535239)
            ·
              refine ⟨19190687734395300336802859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793791822930200224535239 19190687734395300336802859)
              ·
                refine ⟨28786031601592950505204289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19190687734395300336802859 28786031601592950505204289)
                ·
                  refine ⟨21589523701194712878903217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28786031601592950505204289 21589523701194712878903217)
                  ·
                    refine ⟨16192142775896034659177413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21589523701194712878903217 16192142775896034659177413)
                    ·
                      refine ⟨3036026770480506498595765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16192142775896034659177413 3036026770480506498595765)
                      ·
                        rfl

theorem cell23_5912641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5912641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912641 prefixEnd_5912641 := by exact prefixLift 5912641
  have htrace : WordTrace (prefixWord ++ tailWord_5912641) baseStart_5912641 baseEnd_5912641 := by
    simpa [prefixWord, tailWord_5912641, baseEnd_5912641] using wordTrace_append hprefix tailTrace_5912641
  have hstable : (prefixWord ++ tailWord_5912641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912641).length < 2 ^ (prefixWord ++ tailWord_5912641).sum := by decide
  have hdescent : baseEnd_5912641 < baseStart_5912641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912664 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_5912664 : Nat := 118140960795 + 5912664 * 2 ^ 59
def prefixEnd_5912664 : Nat := 4983230072969 + 3 ^ 40 * 5912664 * 2
def baseEnd_5912664 : Nat := 1012012860178519969536053

theorem tailTrace_5912664 : CollatzResearch.WordTrace tailWord_5912664 prefixEnd_5912664 1012012860178519969536053 := by
  unfold tailWord_5912664
  simp only [CollatzResearch.WordTrace]
  refine ⟨107826286325717802730908523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143768381767623736974544697 107826286325717802730908523)
  ·
    refine ⟨161739429488576704096362785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107826286325717802730908523 161739429488576704096362785)
    ·
      refine ⟨121304572116432528072272089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161739429488576704096362785 121304572116432528072272089)
      ·
        refine ⟨90978429087324396054204067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121304572116432528072272089 90978429087324396054204067)
        ·
          refine ⟨136467643630986594081306101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90978429087324396054204067 136467643630986594081306101)
          ·
            refine ⟨12793841590404993195122447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136467643630986594081306101 12793841590404993195122447)
            ·
              refine ⟨19190762385607489792683671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12793841590404993195122447 19190762385607489792683671)
              ·
                refine ⟨28786143578411234689025507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19190762385607489792683671 28786143578411234689025507)
                ·
                  refine ⟨43179215367616852033538261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28786143578411234689025507 43179215367616852033538261)
                  ·
                    refine ⟨1012012860178519969536053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43179215367616852033538261 1012012860178519969536053)
                    ·
                      rfl

theorem cell23_5912664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_5912664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912664 prefixEnd_5912664 := by exact prefixLift 5912664
  have htrace : WordTrace (prefixWord ++ tailWord_5912664) baseStart_5912664 baseEnd_5912664 := by
    simpa [prefixWord, tailWord_5912664, baseEnd_5912664] using wordTrace_append hprefix tailTrace_5912664
  have hstable : (prefixWord ++ tailWord_5912664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912664).length < 2 ^ (prefixWord ++ tailWord_5912664).sum := by decide
  have hdescent : baseEnd_5912664 < baseStart_5912664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912668 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 5]
def baseStart_5912668 : Nat := 118140960795 + 5912668 * 2 ^ 59
def prefixEnd_5912668 : Nat := 4983230072969 + 3 ^ 40 * 5912668 * 2
def baseEnd_5912668 : Nat := 337337848273130876995349

theorem tailTrace_5912668 : CollatzResearch.WordTrace tailWord_5912668 prefixEnd_5912668 337337848273130876995349 := by
  unfold tailWord_5912668
  simp only [CollatzResearch.WordTrace]
  refine ⟨107826359271710557072481329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143768479028947409429975105 107826359271710557072481329)
  ·
    refine ⟨80869769453782917804360997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107826359271710557072481329 80869769453782917804360997)
    ·
      refine ⟨15163081772584297088317687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80869769453782917804360997 15163081772584297088317687)
      ·
        refine ⟨22744622658876445632476531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15163081772584297088317687 22744622658876445632476531)
        ·
          refine ⟨34116933988314668448714797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22744622658876445632476531 34116933988314668448714797)
          ·
            refine ⟨12793850245618000668268049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34116933988314668448714797 12793850245618000668268049)
            ·
              refine ⟨9595387684213500501201037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12793850245618000668268049 9595387684213500501201037)
              ·
                refine ⟨3598270381580062687950389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9595387684213500501201037 3598270381580062687950389)
                ·
                  refine ⟨337337848273130876995349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598270381580062687950389 337337848273130876995349)
                  ·
                    rfl

theorem cell23_5912668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_5912668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912668 prefixEnd_5912668 := by exact prefixLift 5912668
  have htrace : WordTrace (prefixWord ++ tailWord_5912668) baseStart_5912668 baseEnd_5912668 := by
    simpa [prefixWord, tailWord_5912668, baseEnd_5912668] using wordTrace_append hprefix tailTrace_5912668
  have hstable : (prefixWord ++ tailWord_5912668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912668).length < 2 ^ (prefixWord ++ tailWord_5912668).sum := by decide
  have hdescent : baseEnd_5912668 < baseStart_5912668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912711 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 3, 4]
def baseStart_5912711 : Nat := 118140960795 + 5912711 * 2 ^ 59
def prefixEnd_5912711 : Nat := 4983230072969 + 3 ^ 40 * 5912711 * 2
def baseEnd_5912711 : Nat := 1012020904708773741573481

theorem tailTrace_5912711 : CollatzResearch.WordTrace tailWord_5912711 prefixEnd_5912711 1012020904708773741573481 := by
  unfold tailWord_5912711
  simp only [CollatzResearch.WordTrace]
  refine ⟨215654286882265332488777987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143769524588176888325851991 215654286882265332488777987)
  ·
    refine ⟨323481430323397998733166981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215654286882265332488777987 323481430323397998733166981)
    ·
      refine ⟨60652768185637124762468809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323481430323397998733166981 60652768185637124762468809)
      ·
        refine ⟨45489576139227843571851607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60652768185637124762468809 45489576139227843571851607)
        ·
          refine ⟨68234364208841765357777411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45489576139227843571851607 68234364208841765357777411)
          ·
            refine ⟨102351546313262648036666117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68234364208841765357777411 102351546313262648036666117)
            ·
              refine ⟨19190914933736746506874897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102351546313262648036666117 19190914933736746506874897)
              ·
                refine ⟨14393186200302559880156173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19190914933736746506874897 14393186200302559880156173)
                ·
                  refine ⟨5397444825113459955058565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14393186200302559880156173 5397444825113459955058565)
                  ·
                    refine ⟨1012020904708773741573481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397444825113459955058565 1012020904708773741573481)
                    ·
                      rfl

theorem cell23_5912711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_5912711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912711 prefixEnd_5912711 := by exact prefixLift 5912711
  have htrace : WordTrace (prefixWord ++ tailWord_5912711) baseStart_5912711 baseEnd_5912711 := by
    simpa [prefixWord, tailWord_5912711, baseEnd_5912711] using wordTrace_append hprefix tailTrace_5912711
  have hstable : (prefixWord ++ tailWord_5912711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912711).length < 2 ^ (prefixWord ++ tailWord_5912711).sum := by decide
  have hdescent : baseEnd_5912711 < baseStart_5912711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912738 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5912738 : Nat := 118140960795 + 5912738 * 2 ^ 59
def prefixEnd_5912738 : Nat := 4983230072969 + 3 ^ 40 * 5912738 * 2
def baseEnd_5912738 : Nat := 3036076578103992619082819

theorem tailTrace_5912738 : CollatzResearch.WordTrace tailWord_5912738 prefixEnd_5912738 3036076578103992619082819 := by
  unfold tailWord_5912738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53913817913291879025002717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143770181102111677400007245 53913817913291879025002717)
  ·
    refine ⟨20217681717484454634376019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53913817913291879025002717 20217681717484454634376019)
    ·
      refine ⟨30326522576226681951564029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20217681717484454634376019 30326522576226681951564029)
      ·
        refine ⟨11372445966085005731836511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30326522576226681951564029 11372445966085005731836511)
        ·
          refine ⟨17058668949127508597754767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11372445966085005731836511 17058668949127508597754767)
          ·
            refine ⟨25588003423691262896632151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17058668949127508597754767 25588003423691262896632151)
            ·
              refine ⟨38382005135536894344948227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25588003423691262896632151 38382005135536894344948227)
              ·
                refine ⟨57573007703305341517422341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38382005135536894344948227 57573007703305341517422341)
                ·
                  refine ⟨10794938944369751534516689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57573007703305341517422341 10794938944369751534516689)
                  ·
                    refine ⟨8096204208277313650887517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10794938944369751534516689 8096204208277313650887517)
                    ·
                      refine ⟨3036076578103992619082819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096204208277313650887517 3036076578103992619082819)
                      ·
                        rfl

theorem cell23_5912738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5912738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912738 prefixEnd_5912738 := by exact prefixLift 5912738
  have htrace : WordTrace (prefixWord ++ tailWord_5912738) baseStart_5912738 baseEnd_5912738 := by
    simpa [prefixWord, tailWord_5912738, baseEnd_5912738] using wordTrace_append hprefix tailTrace_5912738
  have hstable : (prefixWord ++ tailWord_5912738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912738).length < 2 ^ (prefixWord ++ tailWord_5912738).sum := by decide
  have hdescent : baseEnd_5912738 < baseStart_5912738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912796 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5912796 : Nat := 118140960795 + 5912796 * 2 ^ 59
def prefixEnd_5912796 : Nat := 4983230072969 + 3 ^ 40 * 5912796 * 2
def baseEnd_5912796 : Nat := 1012035453327317797385851

theorem tailTrace_5912796 : CollatzResearch.WordTrace tailWord_5912796 prefixEnd_5912796 1012035453327317797385851 := by
  unfold tailWord_5912796
  simp only [CollatzResearch.WordTrace]
  refine ⟨107828693543478696002811121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143771591391304928003748161 107828693543478696002811121)
  ·
    refine ⟨80871520157609022002108341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107828693543478696002811121 80871520157609022002108341)
    ·
      refine ⟨7581705014775845812697657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80871520157609022002108341 7581705014775845812697657)
      ·
        refine ⟨5686278761081884359523243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7581705014775845812697657 5686278761081884359523243)
        ·
          refine ⟨8529418141622826539284865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686278761081884359523243 8529418141622826539284865)
          ·
            refine ⟨6397063606217119904463649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8529418141622826539284865 6397063606217119904463649)
            ·
              refine ⟨4797797704662839928347737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397063606217119904463649 4797797704662839928347737)
              ·
                refine ⟨3598348278497129946260803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797797704662839928347737 3598348278497129946260803)
                ·
                  refine ⟨5397522417745694919391205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598348278497129946260803 5397522417745694919391205)
                  ·
                    refine ⟨1012035453327317797385851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397522417745694919391205 1012035453327317797385851)
                    ·
                      rfl

theorem cell23_5912796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5912796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912796 prefixEnd_5912796 := by exact prefixLift 5912796
  have htrace : WordTrace (prefixWord ++ tailWord_5912796) baseStart_5912796 baseEnd_5912796 := by
    simpa [prefixWord, tailWord_5912796, baseEnd_5912796] using wordTrace_append hprefix tailTrace_5912796
  have hstable : (prefixWord ++ tailWord_5912796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912796).length < 2 ^ (prefixWord ++ tailWord_5912796).sum := by decide
  have hdescent : baseEnd_5912796 < baseStart_5912796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912811 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3]
def baseStart_5912811 : Nat := 118140960795 + 5912811 * 2 ^ 59
def prefixEnd_5912811 : Nat := 4983230072969 + 3 ^ 40 * 5912811 * 2
def baseEnd_5912811 : Nat := 3036114062191770833469983

theorem tailTrace_5912811 : CollatzResearch.WordTrace tailWord_5912811 prefixEnd_5912811 3036114062191770833469983 := by
  unfold tailWord_5912811
  simp only [CollatzResearch.WordTrace]
  refine ⟨215657934181903049567418287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143771956121268699711612191 215657934181903049567418287)
  ·
    refine ⟨323486901272854574351127431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215657934181903049567418287 323486901272854574351127431)
    ·
      refine ⟨485230351909281861526691147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323486901272854574351127431 485230351909281861526691147)
      ·
        refine ⟨727845527863922792290036721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485230351909281861526691147 727845527863922792290036721)
        ·
          refine ⟨545884145897942094217527541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 727845527863922792290036721 545884145897942094217527541)
          ·
            refine ⟨51176638677932071332893207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 545884145897942094217527541 51176638677932071332893207)
            ·
              refine ⟨76764958016898106999339811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51176638677932071332893207 76764958016898106999339811)
              ·
                refine ⟨115147437025347160499009717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76764958016898106999339811 115147437025347160499009717)
                ·
                  refine ⟨10795072221126296296782161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115147437025347160499009717 10795072221126296296782161)
                  ·
                    refine ⟨8096304165844722222586621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10795072221126296296782161 8096304165844722222586621)
                    ·
                      refine ⟨3036114062191770833469983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096304165844722222586621 3036114062191770833469983)
                      ·
                        rfl

theorem cell23_5912811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3].length) (baseStart_5912811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912811 prefixEnd_5912811 := by exact prefixLift 5912811
  have htrace : WordTrace (prefixWord ++ tailWord_5912811) baseStart_5912811 baseEnd_5912811 := by
    simpa [prefixWord, tailWord_5912811, baseEnd_5912811] using wordTrace_append hprefix tailTrace_5912811
  have hstable : (prefixWord ++ tailWord_5912811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912811).length < 2 ^ (prefixWord ++ tailWord_5912811).sum := by decide
  have hdescent : baseEnd_5912811 < baseStart_5912811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912818 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_5912818 : Nat := 118140960795 + 5912818 * 2 ^ 59
def prefixEnd_5912818 : Nat := 4983230072969 + 3 ^ 40 * 5912818 * 2
def baseEnd_5912818 : Nat := 1012039218852117435360817

theorem tailTrace_5912818 : CollatzResearch.WordTrace tailWord_5912818 prefixEnd_5912818 1012039218852117435360817 := by
  unfold tailWord_5912818
  simp only [CollatzResearch.WordTrace]
  refine ⟨53914547373219422440730777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143772126328585126508615405 53914547373219422440730777)
  ·
    refine ⟨40435910529914566830548083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53914547373219422440730777 40435910529914566830548083)
    ·
      refine ⟨60653865794871850245822125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40435910529914566830548083 60653865794871850245822125)
      ·
        refine ⟨22745199673076943842183297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60653865794871850245822125 22745199673076943842183297)
        ·
          refine ⟨17058899754807707881637473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22745199673076943842183297 17058899754807707881637473)
          ·
            refine ⟨12794174816105780911228105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17058899754807707881637473 12794174816105780911228105)
            ·
              refine ⟨9595631112079335683421079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794174816105780911228105 9595631112079335683421079)
              ·
                refine ⟨14393446668119003525131619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9595631112079335683421079 14393446668119003525131619)
                ·
                  refine ⟨21590170002178505287697429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14393446668119003525131619 21590170002178505287697429)
                  ·
                    refine ⟨1012039218852117435360817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21590170002178505287697429 1012039218852117435360817)
                    ·
                      rfl

theorem cell23_5912818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_5912818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912818 prefixEnd_5912818 := by exact prefixLift 5912818
  have htrace : WordTrace (prefixWord ++ tailWord_5912818) baseStart_5912818 baseEnd_5912818 := by
    simpa [prefixWord, tailWord_5912818, baseEnd_5912818] using wordTrace_append hprefix tailTrace_5912818
  have hstable : (prefixWord ++ tailWord_5912818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912818).length < 2 ^ (prefixWord ++ tailWord_5912818).sum := by decide
  have hdescent : baseEnd_5912818 < baseStart_5912818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912824 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_5912824 : Nat := 118140960795 + 5912824 * 2 ^ 59
def prefixEnd_5912824 : Nat := 4983230072969 + 3 ^ 40 * 5912824 * 2
def baseEnd_5912824 : Nat := 3036120737440279282607423

theorem tailTrace_5912824 : CollatzResearch.WordTrace tailWord_5912824 prefixEnd_5912824 3036120737440279282607423 := by
  unfold tailWord_5912824
  simp only [CollatzResearch.WordTrace]
  refine ⟨107829204165427976393820763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143772272220570635191761017 107829204165427976393820763)
  ·
    refine ⟨161743806248141964590731145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107829204165427976393820763 161743806248141964590731145)
    ·
      refine ⟨121307854686106473443048359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161743806248141964590731145 121307854686106473443048359)
      ·
        refine ⟨181961782029159710164572539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121307854686106473443048359 181961782029159710164572539)
        ·
          refine ⟨272942673043739565246858809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181961782029159710164572539 272942673043739565246858809)
          ·
            refine ⟨204707004782804673935144107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272942673043739565246858809 204707004782804673935144107)
            ·
              refine ⟨307060507174207010902716161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204707004782804673935144107 307060507174207010902716161)
              ·
                refine ⟨230295380380655258177037121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307060507174207010902716161 230295380380655258177037121)
                ·
                  refine ⟨172721535285491443632777841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230295380380655258177037121 172721535285491443632777841)
                  ·
                    refine ⟨129541151464118582724583381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172721535285491443632777841 129541151464118582724583381)
                    ·
                      refine ⟨3036120737440279282607423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129541151464118582724583381 3036120737440279282607423)
                      ·
                        rfl

theorem cell23_5912824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_5912824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912824 prefixEnd_5912824 := by exact prefixLift 5912824
  have htrace : WordTrace (prefixWord ++ tailWord_5912824) baseStart_5912824 baseEnd_5912824 := by
    simpa [prefixWord, tailWord_5912824, baseEnd_5912824] using wordTrace_append hprefix tailTrace_5912824
  have hstable : (prefixWord ++ tailWord_5912824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912824).length < 2 ^ (prefixWord ++ tailWord_5912824).sum := by decide
  have hdescent : baseEnd_5912824 < baseStart_5912824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912828 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_5912828 : Nat := 118140960795 + 5912828 * 2 ^ 59
def prefixEnd_5912828 : Nat := 4983230072969 + 3 ^ 40 * 5912828 * 2
def baseEnd_5912828 : Nat := 3036122791362897266957405

theorem tailTrace_5912828 : CollatzResearch.WordTrace tailWord_5912828 prefixEnd_5912828 3036122791362897266957405 := by
  unfold tailWord_5912828
  simp only [CollatzResearch.WordTrace]
  refine ⟨107829277111420730735393569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143772369481894307647191425 107829277111420730735393569)
  ·
    refine ⟨80871957833565548051545177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107829277111420730735393569 80871957833565548051545177)
    ·
      refine ⟨60653968375174161038658883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80871957833565548051545177 60653968375174161038658883)
      ·
        refine ⟨90980952562761241557988325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60653968375174161038658883 90980952562761241557988325)
        ·
          refine ⟨17058928605517732792122811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90980952562761241557988325 17058928605517732792122811)
          ·
            refine ⟨25588392908276599188184217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17058928605517732792122811 25588392908276599188184217)
            ·
              refine ⟨19191294681207449391138163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25588392908276599188184217 19191294681207449391138163)
              ·
                refine ⟨28786942021811174086707245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19191294681207449391138163 28786942021811174086707245)
                ·
                  refine ⟨10795103258179190282515217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28786942021811174086707245 10795103258179190282515217)
                  ·
                    refine ⟨8096327443634392711886413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10795103258179190282515217 8096327443634392711886413)
                    ·
                      refine ⟨3036122791362897266957405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096327443634392711886413 3036122791362897266957405)
                      ·
                        rfl

theorem cell23_5912828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_5912828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912828 prefixEnd_5912828 := by exact prefixLift 5912828
  have htrace : WordTrace (prefixWord ++ tailWord_5912828) baseStart_5912828 baseEnd_5912828 := by
    simpa [prefixWord, tailWord_5912828, baseEnd_5912828] using wordTrace_append hprefix tailTrace_5912828
  have hstable : (prefixWord ++ tailWord_5912828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912828).length < 2 ^ (prefixWord ++ tailWord_5912828).sum := by decide
  have hdescent : baseEnd_5912828 < baseStart_5912828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912831 : List Nat := [1, 1, 2, 2, 1, 4, 5, 7]
def baseStart_5912831 : Nat := 118140960795 + 5912831 * 2 ^ 59
def prefixEnd_5912831 : Nat := 4983230072969 + 3 ^ 40 * 5912831 * 2
def baseEnd_5912831 : Nat := 112449049326105953897033

theorem tailTrace_5912831 : CollatzResearch.WordTrace tailWord_5912831 prefixEnd_5912831 112449049326105953897033 := by
  unfold tailWord_5912831
  simp only [CollatzResearch.WordTrace]
  refine ⟨215658663641830592983146347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143772442427887061988764231 215658663641830592983146347)
  ·
    refine ⟨323487995462745889474719521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215658663641830592983146347 323487995462745889474719521)
    ·
      refine ⟨242615996597059417106039641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323487995462745889474719521 242615996597059417106039641)
      ·
        refine ⟨181961997447794562829529731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242615996597059417106039641 181961997447794562829529731)
        ·
          refine ⟨272942996171691844244294597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181961997447794562829529731 272942996171691844244294597)
          ·
            refine ⟨51176811782192220795805237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 272942996171691844244294597 51176811782192220795805237)
            ·
              refine ⟨4797826104580520699606741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51176811782192220795805237 4797826104580520699606741)
              ·
                refine ⟨112449049326105953897033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4797826104580520699606741 112449049326105953897033)
                ·
                  rfl

theorem cell23_5912831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 7].length) (baseStart_5912831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912831 prefixEnd_5912831 := by exact prefixLift 5912831
  have htrace : WordTrace (prefixWord ++ tailWord_5912831) baseStart_5912831 baseEnd_5912831 := by
    simpa [prefixWord, tailWord_5912831, baseEnd_5912831] using wordTrace_append hprefix tailTrace_5912831
  have hstable : (prefixWord ++ tailWord_5912831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912831).length < 2 ^ (prefixWord ++ tailWord_5912831).sum := by decide
  have hdescent : baseEnd_5912831 < baseStart_5912831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912839 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 1, 5]
def baseStart_5912839 : Nat := 118140960795 + 5912839 * 2 ^ 59
def prefixEnd_5912839 : Nat := 4983230072969 + 3 ^ 40 * 5912839 * 2
def baseEnd_5912839 : Nat := 1012042813216698907973285

theorem tailTrace_5912839 : CollatzResearch.WordTrace tailWord_5912839 prefixEnd_5912839 1012042813216698907973285 := by
  unfold tailWord_5912839
  simp only [CollatzResearch.WordTrace]
  refine ⟨215658955425801610349437571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143772636950534406899625047 215658955425801610349437571)
  ·
    refine ⟨323488433138702415524156357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215658955425801610349437571 323488433138702415524156357)
    ·
      refine ⟨60654081213506702910779317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323488433138702415524156357 60654081213506702910779317)
      ·
        refine ⟨5686320113766253397885561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60654081213506702910779317 5686320113766253397885561)
        ·
          refine ⟨4264740085324690048414171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5686320113766253397885561 4264740085324690048414171)
          ·
            refine ⟨6397110127987035072621257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264740085324690048414171 6397110127987035072621257)
            ·
              refine ⟨4797832595990276304465943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397110127987035072621257 4797832595990276304465943)
              ·
                refine ⟨7196748893985414456698915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4797832595990276304465943 7196748893985414456698915)
                ·
                  refine ⟨10795123340978121685048373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7196748893985414456698915 10795123340978121685048373)
                  ·
                    refine ⟨1012042813216698907973285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10795123340978121685048373 1012042813216698907973285)
                    ·
                      rfl

theorem cell23_5912839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_5912839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912839 prefixEnd_5912839 := by exact prefixLift 5912839
  have htrace : WordTrace (prefixWord ++ tailWord_5912839) baseStart_5912839 baseEnd_5912839 := by
    simpa [prefixWord, tailWord_5912839, baseEnd_5912839] using wordTrace_append hprefix tailTrace_5912839
  have hstable : (prefixWord ++ tailWord_5912839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912839).length < 2 ^ (prefixWord ++ tailWord_5912839).sum := by decide
  have hdescent : baseEnd_5912839 < baseStart_5912839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912842 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2]
def baseStart_5912842 : Nat := 118140960795 + 5912842 * 2 ^ 59
def prefixEnd_5912842 : Nat := 4983230072969 + 3 ^ 40 * 5912842 * 2
def baseEnd_5912842 : Nat := 3036129980092060212182341

theorem tailTrace_5912842 : CollatzResearch.WordTrace tailWord_5912842 prefixEnd_5912842 3036129980092060212182341 := by
  unfold tailWord_5912842
  simp only [CollatzResearch.WordTrace]
  refine ⟨53914766211197685465449195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143772709896527161241197853 53914766211197685465449195)
  ·
    refine ⟨80872149316796528198173793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53914766211197685465449195 80872149316796528198173793)
    ·
      refine ⟨60654111987597396148630345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80872149316796528198173793 60654111987597396148630345)
      ·
        refine ⟨45490583990698047111472759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60654111987597396148630345 45490583990698047111472759)
        ·
          refine ⟨68235875986047070667209139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45490583990698047111472759 68235875986047070667209139)
          ·
            refine ⟨102353813979070606000813709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68235875986047070667209139 102353813979070606000813709)
            ·
              refine ⟨38382680242151477250305141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102353813979070606000813709 38382680242151477250305141)
              ·
                refine ⟨3598376272701700992216107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38382680242151477250305141 3598376272701700992216107)
                ·
                  refine ⟨5397564409052551488324161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598376272701700992216107 5397564409052551488324161)
                  ·
                    refine ⟨4048173306789413616243121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397564409052551488324161 4048173306789413616243121)
                    ·
                      refine ⟨3036129980092060212182341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048173306789413616243121 3036129980092060212182341)
                      ·
                        rfl

theorem cell23_5912842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_5912842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912842 prefixEnd_5912842 := by exact prefixLift 5912842
  have htrace : WordTrace (prefixWord ++ tailWord_5912842) baseStart_5912842 baseEnd_5912842 := by
    simpa [prefixWord, tailWord_5912842, baseEnd_5912842] using wordTrace_append hprefix tailTrace_5912842
  have hstable : (prefixWord ++ tailWord_5912842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912842).length < 2 ^ (prefixWord ++ tailWord_5912842).sum := by decide
  have hdescent : baseEnd_5912842 < baseStart_5912842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912872 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5912872 : Nat := 118140960795 + 5912872 * 2 ^ 59
def prefixEnd_5912872 : Nat := 4983230072969 + 3 ^ 40 * 5912872 * 2
def baseEnd_5912872 : Nat := 3036145384511695094807203

theorem tailTrace_5912872 : CollatzResearch.WordTrace tailWord_5912872 prefixEnd_5912872 3036145384511695094807203 := by
  unfold tailWord_5912872
  simp only [CollatzResearch.WordTrace]
  refine ⟨107830079517341028492694435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143773439356454704656925913 107830079517341028492694435)
  ·
    refine ⟨161745119276011542739041653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107830079517341028492694435 161745119276011542739041653)
    ·
      refine ⟨15163604932126082131785155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161745119276011542739041653 15163604932126082131785155)
      ·
        refine ⟨22745407398189123197677733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15163604932126082131785155 22745407398189123197677733)
        ·
          refine ⟨4264763887160460599564575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22745407398189123197677733 4264763887160460599564575)
          ·
            refine ⟨6397145830740690899346863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264763887160460599564575 6397145830740690899346863)
            ·
              refine ⟨9595718746111036349020295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397145830740690899346863 9595718746111036349020295)
              ·
                refine ⟨14393578119166554523530443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9595718746111036349020295 14393578119166554523530443)
                ·
                  refine ⟨21590367178749831785295665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14393578119166554523530443 21590367178749831785295665)
                  ·
                    refine ⟨16192775384062373838971749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21590367178749831785295665 16192775384062373838971749)
                    ·
                      refine ⟨3036145384511695094807203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16192775384062373838971749 3036145384511695094807203)
                      ·
                        rfl

theorem cell23_5912872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5912872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912872 prefixEnd_5912872 := by exact prefixLift 5912872
  have htrace : WordTrace (prefixWord ++ tailWord_5912872) baseStart_5912872 baseEnd_5912872 := by
    simpa [prefixWord, tailWord_5912872, baseEnd_5912872] using wordTrace_append hprefix tailTrace_5912872
  have hstable : (prefixWord ++ tailWord_5912872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912872).length < 2 ^ (prefixWord ++ tailWord_5912872).sum := by decide
  have hdescent : baseEnd_5912872 < baseStart_5912872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912901 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_5912901 : Nat := 118140960795 + 5912901 * 2 ^ 59
def prefixEnd_5912901 : Nat := 4983230072969 + 3 ^ 40 * 5912901 * 2
def baseEnd_5912901 : Nat := 3036160275450675481344569

theorem tailTrace_5912901 : CollatzResearch.WordTrace tailWord_5912901 prefixEnd_5912901 3036160275450675481344569 := by
  unfold tailWord_5912901
  simp only [CollatzResearch.WordTrace]
  refine ⟨215661216751576994938194557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143774144501051329958796371 215661216751576994938194557)
  ·
    refine ⟨80872956281841373101822959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215661216751576994938194557 80872956281841373101822959)
    ·
      refine ⟨121309434422762059652734439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80872956281841373101822959 121309434422762059652734439)
      ·
        refine ⟨181964151634143089479101659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121309434422762059652734439 181964151634143089479101659)
        ·
          refine ⟨272946227451214634218652489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181964151634143089479101659 272946227451214634218652489)
          ·
            refine ⟨204709670588410975663989367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272946227451214634218652489 204709670588410975663989367)
            ·
              refine ⟨307064505882616463495984051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204709670588410975663989367 307064505882616463495984051)
              ·
                refine ⟨460596758823924695243976077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307064505882616463495984051 460596758823924695243976077)
                ·
                  refine ⟨172723784558971760716491029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460596758823924695243976077 172723784558971760716491029)
                  ·
                    refine ⟨8096427401201801283585517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172723784558971760716491029 8096427401201801283585517)
                    ·
                      refine ⟨3036160275450675481344569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096427401201801283585517 3036160275450675481344569)
                      ·
                        rfl

theorem cell23_5912901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_5912901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912901 prefixEnd_5912901 := by exact prefixLift 5912901
  have htrace : WordTrace (prefixWord ++ tailWord_5912901) baseStart_5912901 baseEnd_5912901 := by
    simpa [prefixWord, tailWord_5912901, baseEnd_5912901] using wordTrace_append hprefix tailTrace_5912901
  have hstable : (prefixWord ++ tailWord_5912901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912901).length < 2 ^ (prefixWord ++ tailWord_5912901).sum := by decide
  have hdescent : baseEnd_5912901 < baseStart_5912901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912911 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_5912911 : Nat := 118140960795 + 5912911 * 2 ^ 59
def prefixEnd_5912911 : Nat := 4983230072969 + 3 ^ 40 * 5912911 * 2
def baseEnd_5912911 : Nat := 3036165410257220442219523

theorem tailTrace_5912911 : CollatzResearch.WordTrace tailWord_5912911 prefixEnd_5912911 3036165410257220442219523 := by
  unfold tailWord_5912911
  simp only [CollatzResearch.WordTrace]
  refine ⟨215661581481540766646058587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143774387654360511097372391 215661581481540766646058587)
  ·
    refine ⟨323492372222311149969087881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215661581481540766646058587 323492372222311149969087881)
    ·
      refine ⟨242619279166733362476815911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323492372222311149969087881 242619279166733362476815911)
      ·
        refine ⟨363928918750100043715223867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242619279166733362476815911 363928918750100043715223867)
        ·
          refine ⟨545893378125150065572835801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363928918750100043715223867 545893378125150065572835801)
          ·
            refine ⟨409420033593862549179626851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545893378125150065572835801 409420033593862549179626851)
            ·
              refine ⟨614130050390793823769440277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409420033593862549179626851 614130050390793823769440277)
              ·
                refine ⟨28787346112068460489192513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 614130050390793823769440277 28787346112068460489192513)
                ·
                  refine ⟨21590509584051345366894385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28787346112068460489192513 21590509584051345366894385)
                  ·
                    refine ⟨16192882188038509025170789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21590509584051345366894385 16192882188038509025170789)
                    ·
                      refine ⟨3036165410257220442219523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16192882188038509025170789 3036165410257220442219523)
                      ·
                        rfl

theorem cell23_5912911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_5912911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912911 prefixEnd_5912911 := by exact prefixLift 5912911
  have htrace : WordTrace (prefixWord ++ tailWord_5912911) baseStart_5912911 baseEnd_5912911 := by
    simpa [prefixWord, tailWord_5912911, baseEnd_5912911] using wordTrace_append hprefix tailTrace_5912911
  have hstable : (prefixWord ++ tailWord_5912911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912911).length < 2 ^ (prefixWord ++ tailWord_5912911).sum := by decide
  have hdescent : baseEnd_5912911 < baseStart_5912911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912932 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_5912932 : Nat := 118140960795 + 5912932 * 2 ^ 59
def prefixEnd_5912932 : Nat := 4983230072969 + 3 ^ 40 * 5912932 * 2
def baseEnd_5912932 : Nat := 3036176193350964860056927

theorem tailTrace_5912932 : CollatzResearch.WordTrace tailWord_5912932 prefixEnd_5912932 3036176193350964860056927 := by
  unfold tailWord_5912932
  simp only [CollatzResearch.WordTrace]
  refine ⟨107831173707232343616286525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143774898276309791488382033 107831173707232343616286525)
  ·
    refine ⟨40436690140212128856107447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107831173707232343616286525 40436690140212128856107447)
    ·
      refine ⟨60655035210318193284161171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40436690140212128856107447 60655035210318193284161171)
      ·
        refine ⟨90982552815477289926241757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60655035210318193284161171 90982552815477289926241757)
        ·
          refine ⟨34118457305803983722340659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90982552815477289926241757 34118457305803983722340659)
          ·
            refine ⟨51177685958705975583510989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34118457305803983722340659 51177685958705975583510989)
            ·
              refine ⟨19191632234514740843816621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51177685958705975583510989 19191632234514740843816621)
              ·
                refine ⟨7196862087943027816431233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19191632234514740843816621 7196862087943027816431233)
                ·
                  refine ⟨5397646565957270862323425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7196862087943027816431233 5397646565957270862323425)
                  ·
                    refine ⟨4048234924467953146742569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397646565957270862323425 4048234924467953146742569)
                    ·
                      refine ⟨3036176193350964860056927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048234924467953146742569 3036176193350964860056927)
                      ·
                        rfl

theorem cell23_5912932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_5912932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912932 prefixEnd_5912932 := by exact prefixLift 5912932
  have htrace : WordTrace (prefixWord ++ tailWord_5912932) baseStart_5912932 baseEnd_5912932 := by
    simpa [prefixWord, tailWord_5912932, baseEnd_5912932] using wordTrace_append hprefix tailTrace_5912932
  have hstable : (prefixWord ++ tailWord_5912932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912932).length < 2 ^ (prefixWord ++ tailWord_5912932).sum := by decide
  have hdescent : baseEnd_5912932 < baseStart_5912932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912968 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_5912968 : Nat := 118140960795 + 5912968 * 2 ^ 59
def prefixEnd_5912968 : Nat := 4983230072969 + 3 ^ 40 * 5912968 * 2
def baseEnd_5912968 : Nat := 1012064892884842239735587

theorem tailTrace_5912968 : CollatzResearch.WordTrace tailWord_5912968 prefixEnd_5912968 1012064892884842239735587 := by
  unfold tailWord_5912968
  simp only [CollatzResearch.WordTrace]
  refine ⟨107831830221167132690441779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143775773628222843587255705 107831830221167132690441779)
  ·
    refine ⟨161747745331750699035662669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107831830221167132690441779 161747745331750699035662669)
    ·
      refine ⟨60655404499406512138373501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161747745331750699035662669 60655404499406512138373501)
      ·
        refine ⟨22745776687277442051890063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60655404499406512138373501 22745776687277442051890063)
        ·
          refine ⟨34118665030916163077835095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22745776687277442051890063 34118665030916163077835095)
          ·
            refine ⟨51177997546374244616752643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34118665030916163077835095 51177997546374244616752643)
            ·
              refine ⟨76766996319561366925128965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51177997546374244616752643 76766996319561366925128965)
              ·
                refine ⟨14393811809917756298461681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76766996319561366925128965 14393811809917756298461681)
                ·
                  refine ⟨10795358857438317223846261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14393811809917756298461681 10795358857438317223846261)
                  ·
                    refine ⟨1012064892884842239735587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10795358857438317223846261 1012064892884842239735587)
                    ·
                      rfl

theorem cell23_5912968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_5912968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912968 prefixEnd_5912968 := by exact prefixLift 5912968
  have htrace : WordTrace (prefixWord ++ tailWord_5912968) baseStart_5912968 baseEnd_5912968 := by
    simpa [prefixWord, tailWord_5912968, baseEnd_5912968] using wordTrace_append hprefix tailTrace_5912968
  have hstable : (prefixWord ++ tailWord_5912968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912968).length < 2 ^ (prefixWord ++ tailWord_5912968).sum := by decide
  have hdescent : baseEnd_5912968 < baseStart_5912968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912972 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 5]
def baseStart_5912972 : Nat := 118140960795 + 5912972 * 2 ^ 59
def prefixEnd_5912972 : Nat := 4983230072969 + 3 ^ 40 * 5912972 * 2
def baseEnd_5912972 : Nat := 337355192508571633728527

theorem tailTrace_5912972 : CollatzResearch.WordTrace tailWord_5912972 prefixEnd_5912972 337355192508571633728527 := by
  unfold tailWord_5912972
  simp only [CollatzResearch.WordTrace]
  refine ⟨107831903167159887032014585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143775870889546516042686113 107831903167159887032014585)
  ·
    refine ⟨80873927375369915274010939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107831903167159887032014585 80873927375369915274010939)
    ·
      refine ⟨121310891063054872911016409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80873927375369915274010939 121310891063054872911016409)
      ·
        refine ⟨90983168297291154683262307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121310891063054872911016409 90983168297291154683262307)
        ·
          refine ⟨136474752445936732024893461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90983168297291154683262307 136474752445936732024893461)
          ·
            refine ⟨6397254020903284313666881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136474752445936732024893461 6397254020903284313666881)
            ·
              refine ⟨4797940515677463235250161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397254020903284313666881 4797940515677463235250161)
              ·
                refine ⟨3598455386758097426437621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4797940515677463235250161 3598455386758097426437621)
                ·
                  refine ⟨337355192508571633728527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598455386758097426437621 337355192508571633728527)
                  ·
                    rfl

theorem cell23_5912972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_5912972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912972 prefixEnd_5912972 := by exact prefixLift 5912972
  have htrace : WordTrace (prefixWord ++ tailWord_5912972) baseStart_5912972 baseEnd_5912972 := by
    simpa [prefixWord, tailWord_5912972, baseEnd_5912972] using wordTrace_append hprefix tailTrace_5912972
  have hstable : (prefixWord ++ tailWord_5912972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912972).length < 2 ^ (prefixWord ++ tailWord_5912972).sum := by decide
  have hdescent : baseEnd_5912972 < baseStart_5912972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5912981 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_5912981 : Nat := 118140960795 + 5912981 * 2 ^ 59
def prefixEnd_5912981 : Nat := 4983230072969 + 3 ^ 40 * 5912981 * 2
def baseEnd_5912981 : Nat := 1012067117967678389448067

theorem tailTrace_5912981 : CollatzResearch.WordTrace tailWord_5912981 prefixEnd_5912981 1012067117967678389448067 := by
  unfold tailWord_5912981
  simp only [CollatzResearch.WordTrace]
  refine ⟨215664134591287168601106797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143776089727524779067404531 215664134591287168601106797)
  ·
    refine ⟨80874050471732688225415049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215664134591287168601106797 80874050471732688225415049)
    ·
      refine ⟨60655537853799516169061287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80874050471732688225415049 60655537853799516169061287)
      ·
        refine ⟨90983306780699274253591931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60655537853799516169061287 90983306780699274253591931)
        ·
          refine ⟨136474960171048911380387897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90983306780699274253591931 136474960171048911380387897)
          ·
            refine ⟨102356220128286683535290923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136474960171048911380387897 102356220128286683535290923)
            ·
              refine ⟨153534330192430025302936385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102356220128286683535290923 153534330192430025302936385)
              ·
                refine ⟨115150747644322518977202289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153534330192430025302936385 115150747644322518977202289)
                ·
                  refine ⟨86363060733241889232901717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115150747644322518977202289 86363060733241889232901717)
                  ·
                    refine ⟨1012067117967678389448067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86363060733241889232901717 1012067117967678389448067)
                    ·
                      rfl

theorem cell23_5912981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_5912981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5912981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5912981 prefixEnd_5912981 := by exact prefixLift 5912981
  have htrace : WordTrace (prefixWord ++ tailWord_5912981) baseStart_5912981 baseEnd_5912981 := by
    simpa [prefixWord, tailWord_5912981, baseEnd_5912981] using wordTrace_append hprefix tailTrace_5912981
  have hstable : (prefixWord ++ tailWord_5912981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5912981).length < 2 ^ (prefixWord ++ tailWord_5912981).sum := by decide
  have hdescent : baseEnd_5912981 < baseStart_5912981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5912981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913001 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_5913001 : Nat := 118140960795 + 5913001 * 2 ^ 59
def prefixEnd_5913001 : Nat := 4983230072969 + 3 ^ 40 * 5913001 * 2
def baseEnd_5913001 : Nat := 3036211623516125090094109

theorem tailTrace_5913001 : CollatzResearch.WordTrace tailWord_5913001 prefixEnd_5913001 3036211623516125090094109 := by
  unfold tailWord_5913001
  simp only [CollatzResearch.WordTrace]
  refine ⟨215664864051214712016834857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143776576034143141344556571 215664864051214712016834857)
  ·
    refine ⟨161748648038411034012626143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215664864051214712016834857 161748648038411034012626143)
    ·
      refine ⟨242622972057616551018939215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161748648038411034012626143 242622972057616551018939215)
      ·
        refine ⟨363934458086424826528408823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242622972057616551018939215 363934458086424826528408823)
        ·
          refine ⟨545901687129637239792613235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363934458086424826528408823 545901687129637239792613235)
          ·
            refine ⟨818852530694455859688919853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545901687129637239792613235 818852530694455859688919853)
            ·
              refine ⟨307069699010420947383344945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818852530694455859688919853 307069699010420947383344945)
              ·
                refine ⟨230302274257815710537508709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307069699010420947383344945 230302274257815710537508709)
                ·
                  refine ⟨43181676423340445725782883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230302274257815710537508709 43181676423340445725782883)
                  ·
                    refine ⟨64772514635010668588674325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43181676423340445725782883 64772514635010668588674325)
                    ·
                      refine ⟨3036211623516125090094109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64772514635010668588674325 3036211623516125090094109)
                      ·
                        rfl

theorem cell23_5913001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_5913001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913001 prefixEnd_5913001 := by exact prefixLift 5913001
  have htrace : WordTrace (prefixWord ++ tailWord_5913001) baseStart_5913001 baseEnd_5913001 := by
    simpa [prefixWord, tailWord_5913001, baseEnd_5913001] using wordTrace_append hprefix tailTrace_5913001
  have hstable : (prefixWord ++ tailWord_5913001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913001).length < 2 ^ (prefixWord ++ tailWord_5913001).sum := by decide
  have hdescent : baseEnd_5913001 < baseStart_5913001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913032 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 1, 4]
def baseStart_5913032 : Nat := 118140960795 + 5913032 * 2 ^ 59
def prefixEnd_5913032 : Nat := 4983230072969 + 3 ^ 40 * 5913032 * 2
def baseEnd_5913032 : Nat := 1012075847138804822935489

theorem tailTrace_5913032 : CollatzResearch.WordTrace tailWord_5913032 prefixEnd_5913032 1012075847138804822935489 := by
  unfold tailWord_5913032
  simp only [CollatzResearch.WordTrace]
  refine ⟨107832997357051202155606675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143777329809401602874142233 107832997357051202155606675)
  ·
    refine ⟨161749496035576803233410013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107832997357051202155606675 161749496035576803233410013)
    ·
      refine ⟨60656061013341301212528755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161749496035576803233410013 60656061013341301212528755)
      ·
        refine ⟨90984091520011951818793133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60656061013341301212528755 90984091520011951818793133)
        ·
          refine ⟨34119034320004481932047425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90984091520011951818793133 34119034320004481932047425)
          ·
            refine ⟨25589275740003361449035569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34119034320004481932047425 25589275740003361449035569)
            ·
              refine ⟨19191956805002521086776677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25589275740003361449035569 19191956805002521086776677)
              ·
                refine ⟨3598491900937972703770627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19191956805002521086776677 3598491900937972703770627)
                ·
                  refine ⟨5397737851406959055655941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598491900937972703770627 5397737851406959055655941)
                  ·
                    refine ⟨1012075847138804822935489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5397737851406959055655941 1012075847138804822935489)
                    ·
                      rfl

theorem cell23_5913032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_5913032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913032 prefixEnd_5913032 := by exact prefixLift 5913032
  have htrace : WordTrace (prefixWord ++ tailWord_5913032) baseStart_5913032 baseEnd_5913032 := by
    simpa [prefixWord, tailWord_5913032, baseEnd_5913032] using wordTrace_append hprefix tailTrace_5913032
  have hstable : (prefixWord ++ tailWord_5913032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913032).length < 2 ^ (prefixWord ++ tailWord_5913032).sum := by decide
  have hdescent : baseEnd_5913032 < baseStart_5913032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913089 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_5913089 : Nat := 118140960795 + 5913089 * 2 ^ 59
def prefixEnd_5913089 : Nat := 4983230072969 + 3 ^ 40 * 5913089 * 2
def baseEnd_5913089 : Nat := 3036256809813720745793705

theorem tailTrace_5913089 : CollatzResearch.WordTrace tailWord_5913089 prefixEnd_5913089 3036256809813720745793705 := by
  unfold tailWord_5913089
  simp only [CollatzResearch.WordTrace]
  refine ⟨215668073674895903046038321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143778715783263935364025547 215668073674895903046038321)
  ·
    refine ⟨161751055256171927284528741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215668073674895903046038321 161751055256171927284528741)
    ·
      refine ⟨30328322860532236365849139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161751055256171927284528741 30328322860532236365849139)
      ·
        refine ⟨45492484290798354548773709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30328322860532236365849139 45492484290798354548773709)
        ·
          refine ⟨17059681609049382955790141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45492484290798354548773709 17059681609049382955790141)
          ·
            refine ⟨6397380603393518608421303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17059681609049382955790141 6397380603393518608421303)
            ·
              refine ⟨9596070905090277912631955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397380603393518608421303 9596070905090277912631955)
              ·
                refine ⟨14394106357635416868947933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596070905090277912631955 14394106357635416868947933)
                ·
                  refine ⟨5397789884113281325855475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14394106357635416868947933 5397789884113281325855475)
                  ·
                    refine ⟨8096684826169921988783213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5397789884113281325855475 8096684826169921988783213)
                    ·
                      refine ⟨3036256809813720745793705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096684826169921988783213 3036256809813720745793705)
                      ·
                        rfl

theorem cell23_5913089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_5913089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913089 prefixEnd_5913089 := by exact prefixLift 5913089
  have htrace : WordTrace (prefixWord ++ tailWord_5913089) baseStart_5913089 baseEnd_5913089 := by
    simpa [prefixWord, tailWord_5913089, baseEnd_5913089] using wordTrace_append hprefix tailTrace_5913089
  have hstable : (prefixWord ++ tailWord_5913089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913089).length < 2 ^ (prefixWord ++ tailWord_5913089).sum := by decide
  have hdescent : baseEnd_5913089 < baseStart_5913089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913112 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_5913112 : Nat := 118140960795 + 5913112 * 2 ^ 59
def prefixEnd_5913112 : Nat := 4983230072969 + 3 ^ 40 * 5913112 * 2
def baseEnd_5913112 : Nat := 3036268619868774155806099

theorem tailTrace_5913112 : CollatzResearch.WordTrace tailWord_5913112 prefixEnd_5913112 3036268619868774155806099 := by
  unfold tailWord_5913112
  simp only [CollatzResearch.WordTrace]
  refine ⟨107834456276906288987062795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143779275035875051982750393 107834456276906288987062795)
  ·
    refine ⟨161751684415359433480594193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107834456276906288987062795 161751684415359433480594193)
    ·
      refine ⟨121313763311519575110445645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161751684415359433480594193 121313763311519575110445645)
      ·
        refine ⟨45492661241819840666417117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121313763311519575110445645 45492661241819840666417117)
        ·
          refine ⟨17059747965682440249906419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45492661241819840666417117 17059747965682440249906419)
          ·
            refine ⟨25589621948523660374859629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17059747965682440249906419 25589621948523660374859629)
            ·
              refine ⟨9596108230696372640572361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25589621948523660374859629 9596108230696372640572361)
              ·
                refine ⟨7197081173022279480429271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9596108230696372640572361 7197081173022279480429271)
                ·
                  refine ⟨10795621759533419220643907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7197081173022279480429271 10795621759533419220643907)
                  ·
                    refine ⟨16193432639300128830965861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10795621759533419220643907 16193432639300128830965861)
                    ·
                      refine ⟨3036268619868774155806099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16193432639300128830965861 3036268619868774155806099)
                      ·
                        rfl

theorem cell23_5913112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_5913112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913112 prefixEnd_5913112 := by exact prefixLift 5913112
  have htrace : WordTrace (prefixWord ++ tailWord_5913112) baseStart_5913112 baseEnd_5913112 := by
    simpa [prefixWord, tailWord_5913112, baseEnd_5913112] using wordTrace_append hprefix tailTrace_5913112
  have hstable : (prefixWord ++ tailWord_5913112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913112).length < 2 ^ (prefixWord ++ tailWord_5913112).sum := by decide
  have hdescent : baseEnd_5913112 < baseStart_5913112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913145 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5913145 : Nat := 118140960795 + 5913145 * 2 ^ 59
def prefixEnd_5913145 : Nat := 4983230072969 + 3 ^ 40 * 5913145 * 2
def baseEnd_5913145 : Nat := 3036285564730372526693447

theorem tailTrace_5913145 : CollatzResearch.WordTrace tailWord_5913145 prefixEnd_5913145 3036285564730372526693447 := by
  unfold tailWord_5913145
  simp only [CollatzResearch.WordTrace]
  refine ⟨215670116162693024610076889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143780077441795349740051259 215670116162693024610076889)
  ·
    refine ⟨161752587122019768457557667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215670116162693024610076889 161752587122019768457557667)
    ·
      refine ⟨242628880683029652686336501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161752587122019768457557667 242628880683029652686336501)
      ·
        refine ⟨22746457564034029939344047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242628880683029652686336501 22746457564034029939344047)
        ·
          refine ⟨34119686346051044909016071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22746457564034029939344047 34119686346051044909016071)
          ·
            refine ⟨51179529519076567363524107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34119686346051044909016071 51179529519076567363524107)
            ·
              refine ⟨76769294278614851045286161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51179529519076567363524107 76769294278614851045286161)
              ·
                refine ⟨57576970708961138283964621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76769294278614851045286161 57576970708961138283964621)
                ·
                  refine ⟨21591364015860426856486733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57576970708961138283964621 21591364015860426856486733)
                  ·
                    refine ⟨8096761505947660071182525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21591364015860426856486733 8096761505947660071182525)
                    ·
                      refine ⟨3036285564730372526693447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096761505947660071182525 3036285564730372526693447)
                      ·
                        rfl

theorem cell23_5913145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5913145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913145 prefixEnd_5913145 := by exact prefixLift 5913145
  have htrace : WordTrace (prefixWord ++ tailWord_5913145) baseStart_5913145 baseEnd_5913145 := by
    simpa [prefixWord, tailWord_5913145, baseEnd_5913145] using wordTrace_append hprefix tailTrace_5913145
  have hstable : (prefixWord ++ tailWord_5913145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913145).length < 2 ^ (prefixWord ++ tailWord_5913145).sum := by decide
  have hdescent : baseEnd_5913145 < baseStart_5913145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913146 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2]
def baseStart_5913146 : Nat := 118140960795 + 5913146 * 2 ^ 59
def prefixEnd_5913146 : Nat := 4983230072969 + 3 ^ 40 * 5913146 * 2
def baseEnd_5913146 : Nat := 3036286078211027022780943

theorem tailTrace_5913146 : CollatzResearch.WordTrace tailWord_5913146 prefixEnd_5913146 3036286078211027022780943 := by
  unfold tailWord_5913146
  simp only [CollatzResearch.WordTrace]
  refine ⟨53917538158922350445215823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143780101757126267853908861 53917538158922350445215823)
  ·
    refine ⟨80876307238383525667823735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53917538158922350445215823 80876307238383525667823735)
    ·
      refine ⟨121314460857575288501735603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80876307238383525667823735 121314460857575288501735603)
      ·
        refine ⟨181971691286362932752603405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121314460857575288501735603 181971691286362932752603405)
        ·
          refine ⟨68239384232386099782226277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181971691286362932752603405 68239384232386099782226277)
          ·
            refine ⟨12794884543572393709167427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68239384232386099782226277 12794884543572393709167427)
            ·
              refine ⟨19192326815358590563751141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12794884543572393709167427 19192326815358590563751141)
              ·
                refine ⟨3598561277879735730703339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19192326815358590563751141 3598561277879735730703339)
                ·
                  refine ⟨5397841916819603596055009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598561277879735730703339 5397841916819603596055009)
                  ·
                    refine ⟨4048381437614702697041257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397841916819603596055009 4048381437614702697041257)
                    ·
                      refine ⟨3036286078211027022780943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048381437614702697041257 3036286078211027022780943)
                      ·
                        rfl

theorem cell23_5913146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2].length) (baseStart_5913146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913146 prefixEnd_5913146 := by exact prefixLift 5913146
  have htrace : WordTrace (prefixWord ++ tailWord_5913146) baseStart_5913146 baseEnd_5913146 := by
    simpa [prefixWord, tailWord_5913146, baseEnd_5913146] using wordTrace_append hprefix tailTrace_5913146
  have hstable : (prefixWord ++ tailWord_5913146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913146).length < 2 ^ (prefixWord ++ tailWord_5913146).sum := by decide
  have hdescent : baseEnd_5913146 < baseStart_5913146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913156 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5913156 : Nat := 118140960795 + 5913156 * 2 ^ 59
def prefixEnd_5913156 : Nat := 4983230072969 + 3 ^ 40 * 5913156 * 2
def baseEnd_5913156 : Nat := 1012097071005857327885299

theorem tailTrace_5913156 : CollatzResearch.WordTrace tailWord_5913156 prefixEnd_5913156 1012097071005857327885299 := by
  unfold tailWord_5913156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107835258682826586744363661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143780344910435448992484881 107835258682826586744363661)
  ·
    refine ⟨40438222006059970029136373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107835258682826586744363661 40438222006059970029136373)
    ·
      refine ⟨3791083313068122190231535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40438222006059970029136373 3791083313068122190231535)
      ·
        refine ⟨5686624969602183285347303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791083313068122190231535 5686624969602183285347303)
        ·
          refine ⟨8529937454403274928020955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686624969602183285347303 8529937454403274928020955)
          ·
            refine ⟨12794906181604912392031433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529937454403274928020955 12794906181604912392031433)
            ·
              refine ⟨9596179636203684294023575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794906181604912392031433 9596179636203684294023575)
              ·
                refine ⟨14394269454305526441035363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596179636203684294023575 14394269454305526441035363)
                ·
                  refine ⟨21591404181458289661553045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14394269454305526441035363 21591404181458289661553045)
                  ·
                    refine ⟨1012097071005857327885299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21591404181458289661553045 1012097071005857327885299)
                    ·
                      rfl

theorem cell23_5913156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5913156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913156 prefixEnd_5913156 := by exact prefixLift 5913156
  have htrace : WordTrace (prefixWord ++ tailWord_5913156) baseStart_5913156 baseEnd_5913156 := by
    simpa [prefixWord, tailWord_5913156, baseEnd_5913156] using wordTrace_append hprefix tailTrace_5913156
  have hstable : (prefixWord ++ tailWord_5913156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913156).length < 2 ^ (prefixWord ++ tailWord_5913156).sum := by decide
  have hdescent : baseEnd_5913156 < baseStart_5913156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913162 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_5913162 : Nat := 118140960795 + 5913162 * 2 ^ 59
def prefixEnd_5913162 : Nat := 4983230072969 + 3 ^ 40 * 5913162 * 2
def baseEnd_5913162 : Nat := 3036294293901498960180869

theorem tailTrace_5913162 : CollatzResearch.WordTrace tailWord_5913162 prefixEnd_5913162 3036294293901498960180869 := by
  unfold tailWord_5913162
  simp only [CollatzResearch.WordTrace]
  refine ⟨53917684050907859128361435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143780490802420957675630493 53917684050907859128361435)
  ·
    refine ⟨80876526076361788692542153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53917684050907859128361435 80876526076361788692542153)
    ·
      refine ⟨60657394557271341519406615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80876526076361788692542153 60657394557271341519406615)
      ·
        refine ⟨90986091835907012279109923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60657394557271341519406615 90986091835907012279109923)
        ·
          refine ⟨136479137753860518418664885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90986091835907012279109923 136479137753860518418664885)
          ·
            refine ⟨12794919164424423601749833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136479137753860518418664885 12794919164424423601749833)
            ·
              refine ⟨9596189373318317701312375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12794919164424423601749833 9596189373318317701312375)
              ·
                refine ⟨14394284059977476551968563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596189373318317701312375 14394284059977476551968563)
                ·
                  refine ⟨21591426089966214827952845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14394284059977476551968563 21591426089966214827952845)
                  ·
                    refine ⟨8096784783737330560482317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21591426089966214827952845 8096784783737330560482317)
                    ·
                      refine ⟨3036294293901498960180869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8096784783737330560482317 3036294293901498960180869)
                      ·
                        rfl

theorem cell23_5913162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_5913162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913162 prefixEnd_5913162 := by exact prefixLift 5913162
  have htrace : WordTrace (prefixWord ++ tailWord_5913162) baseStart_5913162 baseEnd_5913162 := by
    simpa [prefixWord, tailWord_5913162, baseEnd_5913162] using wordTrace_append hprefix tailTrace_5913162
  have hstable : (prefixWord ++ tailWord_5913162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913162).length < 2 ^ (prefixWord ++ tailWord_5913162).sum := by decide
  have hdescent : baseEnd_5913162 < baseStart_5913162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913208 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 11]
def baseStart_5913208 : Nat := 118140960795 + 5913208 * 2 ^ 59
def prefixEnd_5913208 : Nat := 4983230072969 + 3 ^ 40 * 5913208 * 2
def baseEnd_5913208 : Nat := 337368657112400642245073

theorem tailTrace_5913208 : CollatzResearch.WordTrace tailWord_5913208 prefixEnd_5913208 337368657112400642245073 := by
  unfold tailWord_5913208
  simp only [CollatzResearch.WordTrace]
  refine ⟨107836206980732393184810139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143781609307643190913080185 107836206980732393184810139)
  ·
    refine ⟨161754310471098589777215209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107836206980732393184810139 161754310471098589777215209)
    ·
      refine ⟨121315732853323942332911407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161754310471098589777215209 121315732853323942332911407)
      ·
        refine ⟨181973599279985913499367111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121315732853323942332911407 181973599279985913499367111)
        ·
          refine ⟨272960398919978870249050667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181973599279985913499367111 272960398919978870249050667)
          ·
            refine ⟨409440598379968305373576001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272960398919978870249050667 409440598379968305373576001)
            ·
              refine ⟨307080448784976229030182001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409440598379968305373576001 307080448784976229030182001)
              ·
                refine ⟨230310336588732171772636501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307080448784976229030182001 230310336588732171772636501)
                ·
                  refine ⟨337368657112400642245073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 230310336588732171772636501 337368657112400642245073)
                  ·
                    rfl

theorem cell23_5913208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_5913208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913208 prefixEnd_5913208 := by exact prefixLift 5913208
  have htrace : WordTrace (prefixWord ++ tailWord_5913208) baseStart_5913208 baseEnd_5913208 := by
    simpa [prefixWord, tailWord_5913208, baseEnd_5913208] using wordTrace_append hprefix tailTrace_5913208
  have hstable : (prefixWord ++ tailWord_5913208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913208).length < 2 ^ (prefixWord ++ tailWord_5913208).sum := by decide
  have hdescent : baseEnd_5913208 < baseStart_5913208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913219 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 2, 2, 2]
def baseStart_5913219 : Nat := 118140960795 + 5913219 * 2 ^ 59
def prefixEnd_5913219 : Nat := 4983230072969 + 3 ^ 40 * 5913219 * 2
def baseEnd_5913219 : Nat := 3036323562298805237168107

theorem tailTrace_5913219 : CollatzResearch.WordTrace tailWord_5913219 prefixEnd_5913219 3036323562298805237168107 := by
  unfold tailWord_5913219
  simp only [CollatzResearch.WordTrace]
  refine ⟨215672815164424935248270711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143781876776283290165513807 215672815164424935248270711)
  ·
    refine ⟨323509222746637402872406067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215672815164424935248270711 323509222746637402872406067)
    ·
      refine ⟨485263834119956104308609101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323509222746637402872406067 485263834119956104308609101)
      ·
        refine ⟨181973937794983539115728413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485263834119956104308609101 181973937794983539115728413)
        ·
          refine ⟨68240226673118827168398155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181973937794983539115728413 68240226673118827168398155)
          ·
            refine ⟨102360340009678240752597233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68240226673118827168398155 102360340009678240752597233)
            ·
              refine ⟨76770255007258680564447925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102360340009678240752597233 76770255007258680564447925)
              ·
                refine ⟨7197211406930501302916993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76770255007258680564447925 7197211406930501302916993)
                ·
                  refine ⟨5397908555197875977187745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7197211406930501302916993 5397908555197875977187745)
                  ·
                    refine ⟨4048431416398406982890809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397908555197875977187745 4048431416398406982890809)
                    ·
                      refine ⟨3036323562298805237168107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048431416398406982890809 3036323562298805237168107)
                      ·
                        rfl

theorem cell23_5913219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_5913219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913219 prefixEnd_5913219 := by exact prefixLift 5913219
  have htrace : WordTrace (prefixWord ++ tailWord_5913219) baseStart_5913219 baseEnd_5913219 := by
    simpa [prefixWord, tailWord_5913219, baseEnd_5913219] using wordTrace_append hprefix tailTrace_5913219
  have hstable : (prefixWord ++ tailWord_5913219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913219).length < 2 ^ (prefixWord ++ tailWord_5913219).sum := by decide
  have hdescent : baseEnd_5913219 < baseStart_5913219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913236 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5913236 : Nat := 118140960795 + 5913236 * 2 ^ 59
def prefixEnd_5913236 : Nat := 4983230072969 + 3 ^ 40 * 5913236 * 2
def baseEnd_5913236 : Nat := 3036332291469931670655529

theorem tailTrace_5913236 : CollatzResearch.WordTrace tailWord_5913236 prefixEnd_5913236 3036332291469931670655529 := by
  unfold tailWord_5913236
  simp only [CollatzResearch.WordTrace]
  refine ⟨107836717602681673575819781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143782290136908898101093041 107836717602681673575819781)
  ·
    refine ⟨20219384550502813795466209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107836717602681673575819781 20219384550502813795466209)
    ·
      refine ⟨15164538412877110346599657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20219384550502813795466209 15164538412877110346599657)
      ·
        refine ⟨11373403809657832759949743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15164538412877110346599657 11373403809657832759949743)
        ·
          refine ⟨17060105714486749139924615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11373403809657832759949743 17060105714486749139924615)
          ·
            refine ⟨25590158571730123709886923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17060105714486749139924615 25590158571730123709886923)
            ·
              refine ⟨38385237857595185564830385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25590158571730123709886923 38385237857595185564830385)
              ·
                refine ⟨28788928393196389173622789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38385237857595185564830385 28788928393196389173622789)
                ·
                  refine ⟨5397924073724322970054273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28788928393196389173622789 5397924073724322970054273)
                  ·
                    refine ⟨4048443055293242227540705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397924073724322970054273 4048443055293242227540705)
                    ·
                      refine ⟨3036332291469931670655529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048443055293242227540705 3036332291469931670655529)
                      ·
                        rfl

theorem cell23_5913236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5913236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913236 prefixEnd_5913236 := by exact prefixLift 5913236
  have htrace : WordTrace (prefixWord ++ tailWord_5913236) baseStart_5913236 baseEnd_5913236 := by
    simpa [prefixWord, tailWord_5913236, baseEnd_5913236] using wordTrace_append hprefix tailTrace_5913236
  have hstable : (prefixWord ++ tailWord_5913236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913236).length < 2 ^ (prefixWord ++ tailWord_5913236).sum := by decide
  have hdescent : baseEnd_5913236 < baseStart_5913236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913270 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5913270 : Nat := 118140960795 + 5913270 * 2 ^ 59
def prefixEnd_5913270 : Nat := 4983230072969 + 3 ^ 40 * 5913270 * 2
def baseEnd_5913270 : Nat := 3036349749812184537630373

theorem tailTrace_5913270 : CollatzResearch.WordTrace tailWord_5913270 prefixEnd_5913270 3036349749812184537630373 := by
  unfold tailWord_5913270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13479667205452510684898579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143783116858160113972251509 13479667205452510684898579)
  ·
    refine ⟨20219500808178766027347869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13479667205452510684898579 20219500808178766027347869)
    ·
      refine ⟨7582312803067037260255451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20219500808178766027347869 7582312803067037260255451)
      ·
        refine ⟨11373469204600555890383177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582312803067037260255451 11373469204600555890383177)
        ·
          refine ⟨8530101903450416917787383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11373469204600555890383177 8530101903450416917787383)
          ·
            refine ⟨12795152855175625376681075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530101903450416917787383 12795152855175625376681075)
            ·
              refine ⟨19192729282763438065021613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12795152855175625376681075 19192729282763438065021613)
              ·
                refine ⟨7197273481036289274383105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19192729282763438065021613 7197273481036289274383105)
                ·
                  refine ⟨5397955110777216955787329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7197273481036289274383105 5397955110777216955787329)
                  ·
                    refine ⟨4048466333082912716840497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5397955110777216955787329 4048466333082912716840497)
                    ·
                      refine ⟨3036349749812184537630373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048466333082912716840497 3036349749812184537630373)
                      ·
                        rfl

theorem cell23_5913270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5913270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913270 prefixEnd_5913270 := by exact prefixLift 5913270
  have htrace : WordTrace (prefixWord ++ tailWord_5913270) baseStart_5913270 baseEnd_5913270 := by
    simpa [prefixWord, tailWord_5913270, baseEnd_5913270] using wordTrace_append hprefix tailTrace_5913270
  have hstable : (prefixWord ++ tailWord_5913270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913270).length < 2 ^ (prefixWord ++ tailWord_5913270).sum := by decide
  have hdescent : baseEnd_5913270 < baseStart_5913270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913305 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_5913305 : Nat := 118140960795 + 5913305 * 2 ^ 59
def prefixEnd_5913305 : Nat := 4983230072969 + 3 ^ 40 * 5913305 * 2
def baseEnd_5913305 : Nat := 3036367721635091900692711

theorem tailTrace_5913305 : CollatzResearch.WordTrace tailWord_5913305 prefixEnd_5913305 3036367721635091900692711 := by
  unfold tailWord_5913305
  simp only [CollatzResearch.WordTrace]
  refine ⟨215675951842113371935901369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143783967894742247957267579 215675951842113371935901369)
  ·
    refine ⟨161756963881585028951926027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215675951842113371935901369 161756963881585028951926027)
    ·
      refine ⟨242635445822377543427889041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161756963881585028951926027 242635445822377543427889041)
      ·
        refine ⟨181976584366783157570916781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242635445822377543427889041 181976584366783157570916781)
        ·
          refine ⟨68241219137543684089093793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181976584366783157570916781 68241219137543684089093793)
          ·
            refine ⟨51180914353157763066820345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68241219137543684089093793 51180914353157763066820345)
            ·
              refine ⟨38385685764868322300115259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51180914353157763066820345 38385685764868322300115259)
              ·
                refine ⟨57578528647302483450172889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38385685764868322300115259 57578528647302483450172889)
                ·
                  refine ⟨43183896485476862587629667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57578528647302483450172889 43183896485476862587629667)
                  ·
                    refine ⟨64775844728215293881444501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43183896485476862587629667 64775844728215293881444501)
                    ·
                      refine ⟨3036367721635091900692711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64775844728215293881444501 3036367721635091900692711)
                      ·
                        rfl

theorem cell23_5913305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_5913305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913305 prefixEnd_5913305 := by exact prefixLift 5913305
  have htrace : WordTrace (prefixWord ++ tailWord_5913305) baseStart_5913305 baseEnd_5913305 := by
    simpa [prefixWord, tailWord_5913305, baseEnd_5913305] using wordTrace_append hprefix tailTrace_5913305
  have hstable : (prefixWord ++ tailWord_5913305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913305).length < 2 ^ (prefixWord ++ tailWord_5913305).sum := by decide
  have hdescent : baseEnd_5913305 < baseStart_5913305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913346 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_5913346 : Nat := 118140960795 + 5913346 * 2 ^ 59
def prefixEnd_5913346 : Nat := 4983230072969 + 3 ^ 40 * 5913346 * 2
def baseEnd_5913346 : Nat := 3036388774341926240280023

theorem tailTrace_5913346 : CollatzResearch.WordTrace tailWord_5913346 prefixEnd_5913346 3036388774341926240280023 := by
  unfold tailWord_5913346
  simp only [CollatzResearch.WordTrace]
  refine ⟨53919361808741208984535973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143784964823309890625429261 53919361808741208984535973)
  ·
    refine ⟨10109880339138976684600495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53919361808741208984535973 10109880339138976684600495)
    ·
      refine ⟨15164820508708465026900743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10109880339138976684600495 15164820508708465026900743)
      ·
        refine ⟨22747230763062697540351115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15164820508708465026900743 22747230763062697540351115)
        ·
          refine ⟨34120846144594046310526673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22747230763062697540351115 34120846144594046310526673)
          ·
            refine ⟨25590634608445534732895005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34120846144594046310526673 25590634608445534732895005)
            ·
              refine ⟨9596487978167075524835627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25590634608445534732895005 9596487978167075524835627)
              ·
                refine ⟨14394731967250613287253441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596487978167075524835627 14394731967250613287253441)
                ·
                  refine ⟨10796048975437959965440081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14394731967250613287253441 10796048975437959965440081)
                  ·
                    refine ⟨8097036731578469974080061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10796048975437959965440081 8097036731578469974080061)
                    ·
                      refine ⟨3036388774341926240280023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097036731578469974080061 3036388774341926240280023)
                      ·
                        rfl

theorem cell23_5913346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_5913346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913346 prefixEnd_5913346 := by exact prefixLift 5913346
  have htrace : WordTrace (prefixWord ++ tailWord_5913346) baseStart_5913346 baseEnd_5913346 := by
    simpa [prefixWord, tailWord_5913346, baseEnd_5913346] using wordTrace_append hprefix tailTrace_5913346
  have hstable : (prefixWord ++ tailWord_5913346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913346).length < 2 ^ (prefixWord ++ tailWord_5913346).sum := by decide
  have hdescent : baseEnd_5913346 < baseStart_5913346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913355 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_5913355 : Nat := 118140960795 + 5913355 * 2 ^ 59
def prefixEnd_5913355 : Nat := 4983230072969 + 3 ^ 40 * 5913355 * 2
def baseEnd_5913355 : Nat := 3036393395667816705067481

theorem tailTrace_5913355 : CollatzResearch.WordTrace tailWord_5913355 prefixEnd_5913355 3036393395667816705067481 := by
  unfold tailWord_5913355
  simp only [CollatzResearch.WordTrace]
  refine ⟨215677775491932230475221519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143785183661288153650147679 215677775491932230475221519)
  ·
    refine ⟨323516663237898345712832279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215677775491932230475221519 323516663237898345712832279)
    ·
      refine ⟨485274994856847518569248419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323516663237898345712832279 485274994856847518569248419)
      ·
        refine ⟨727912492285271277853872629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485274994856847518569248419 727912492285271277853872629)
        ·
          refine ⟨68241796151744182298800559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 727912492285271277853872629 68241796151744182298800559)
          ·
            refine ⟨102362694227616273448200839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68241796151744182298800559 102362694227616273448200839)
            ·
              refine ⟨153544041341424410172301259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102362694227616273448200839 153544041341424410172301259)
              ·
                refine ⟨230316062012136615258451889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153544041341424410172301259 230316062012136615258451889)
                ·
                  refine ⟨172737046509102461443838917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230316062012136615258451889 172737046509102461443838917)
                  ·
                    refine ⟨32388196220456711520719797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172737046509102461443838917 32388196220456711520719797)
                    ·
                      refine ⟨3036393395667816705067481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32388196220456711520719797 3036393395667816705067481)
                      ·
                        rfl

theorem cell23_5913355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_5913355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913355 prefixEnd_5913355 := by exact prefixLift 5913355
  have htrace : WordTrace (prefixWord ++ tailWord_5913355) baseStart_5913355 baseEnd_5913355 := by
    simpa [prefixWord, tailWord_5913355, baseEnd_5913355] using wordTrace_append hprefix tailTrace_5913355
  have hstable : (prefixWord ++ tailWord_5913355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913355).length < 2 ^ (prefixWord ++ tailWord_5913355).sum := by decide
  have hdescent : baseEnd_5913355 < baseStart_5913355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913376 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5913376 : Nat := 118140960795 + 5913376 * 2 ^ 59
def prefixEnd_5913376 : Nat := 4983230072969 + 3 ^ 40 * 5913376 * 2
def baseEnd_5913376 : Nat := 3036404178761561122904885

theorem tailTrace_5913376 : CollatzResearch.WordTrace tailWord_5913376 prefixEnd_5913376 3036404178761561122904885 := by
  unfold tailWord_5913376
  simp only [CollatzResearch.WordTrace]
  refine ⟨107839270712428075530867991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143785694283237434041157321 107839270712428075530867991)
  ·
    refine ⟨161758906068642113296301987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107839270712428075530867991 161758906068642113296301987)
    ·
      refine ⟨242638359102963169944452981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161758906068642113296301987 242638359102963169944452981)
      ·
        refine ⟨22747346165902797182292467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242638359102963169944452981 22747346165902797182292467)
        ·
          refine ⟨34121019248854195773438701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22747346165902797182292467 34121019248854195773438701)
          ·
            refine ⟨12795382218320323415039513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34121019248854195773438701 12795382218320323415039513)
            ·
              refine ⟨9596536663740242561279635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12795382218320323415039513 9596536663740242561279635)
              ·
                refine ⟨14394804995610363841919453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596536663740242561279635 14394804995610363841919453)
                ·
                  refine ⟨5398051873353886440719795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14394804995610363841919453 5398051873353886440719795)
                  ·
                    refine ⟨8097077810030829661079693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5398051873353886440719795 8097077810030829661079693)
                    ·
                      refine ⟨3036404178761561122904885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097077810030829661079693 3036404178761561122904885)
                      ·
                        rfl

theorem cell23_5913376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5913376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913376 prefixEnd_5913376 := by exact prefixLift 5913376
  have htrace : WordTrace (prefixWord ++ tailWord_5913376) baseStart_5913376 baseEnd_5913376 := by
    simpa [prefixWord, tailWord_5913376, baseEnd_5913376] using wordTrace_append hprefix tailTrace_5913376
  have hstable : (prefixWord ++ tailWord_5913376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913376).length < 2 ^ (prefixWord ++ tailWord_5913376).sum := by decide
  have hdescent : baseEnd_5913376 < baseStart_5913376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913399 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_5913399 : Nat := 118140960795 + 5913399 * 2 ^ 59
def prefixEnd_5913399 : Nat := 4983230072969 + 3 ^ 40 * 5913399 * 2
def baseEnd_5913399 : Nat := 3036415988816614532917279

theorem tailTrace_5913399 : CollatzResearch.WordTrace tailWord_5913399 prefixEnd_5913399 3036415988816614532917279 := by
  unfold tailWord_5913399
  simp only [CollatzResearch.WordTrace]
  refine ⟨215679380303772825989823251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143786253535848550659882167 215679380303772825989823251)
  ·
    refine ⟨323519070455659238984734877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215679380303772825989823251 323519070455659238984734877)
    ·
      refine ⟨121319651420872214619275579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323519070455659238984734877 121319651420872214619275579)
      ·
        refine ⟨181979477131308321928913369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121319651420872214619275579 181979477131308321928913369)
        ·
          refine ⟨136484607848481241446685027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181979477131308321928913369 136484607848481241446685027)
          ·
            refine ⟨204726911772721862170027541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136484607848481241446685027 204726911772721862170027541)
            ·
              refine ⟨9596573989346337289220041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 204726911772721862170027541 9596573989346337289220041)
              ·
                refine ⟨7197430492009752966915031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9596573989346337289220041 7197430492009752966915031)
                ·
                  refine ⟨10796145738014629450372547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7197430492009752966915031 10796145738014629450372547)
                  ·
                    refine ⟨16194218607021944175558821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10796145738014629450372547 16194218607021944175558821)
                    ·
                      refine ⟨3036415988816614532917279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16194218607021944175558821 3036415988816614532917279)
                      ·
                        rfl

theorem cell23_5913399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_5913399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913399 prefixEnd_5913399 := by exact prefixLift 5913399
  have htrace : WordTrace (prefixWord ++ tailWord_5913399) baseStart_5913399 baseEnd_5913399 := by
    simpa [prefixWord, tailWord_5913399, baseEnd_5913399] using wordTrace_append hprefix tailTrace_5913399
  have hstable : (prefixWord ++ tailWord_5913399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913399).length < 2 ^ (prefixWord ++ tailWord_5913399).sum := by decide
  have hdescent : baseEnd_5913399 < baseStart_5913399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913433 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 3, 2, 2]
def baseStart_5913433 : Nat := 118140960795 + 5913433 * 2 ^ 59
def prefixEnd_5913433 : Nat := 4983230072969 + 3 ^ 40 * 5913433 * 2
def baseEnd_5913433 : Nat := 3036433447158867399892123

theorem tailTrace_5913433 : CollatzResearch.WordTrace tailWord_5913433 prefixEnd_5913433 3036433447158867399892123 := by
  unfold tailWord_5913433
  simp only [CollatzResearch.WordTrace]
  refine ⟨215680620385649649796560953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143787080257099766531040635 215680620385649649796560953)
  ·
    refine ⟨161760465289237237347420715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215680620385649649796560953 161760465289237237347420715)
    ·
      refine ⟨242640697933855856021131073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161760465289237237347420715 242640697933855856021131073)
      ·
        refine ⟨181980523450391892015848305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242640697933855856021131073 181980523450391892015848305)
        ·
          refine ⟨136485392587793919011886229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181980523450391892015848305 136485392587793919011886229)
          ·
            refine ⟨6397752777552839953682167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 136485392587793919011886229 6397752777552839953682167)
            ·
              refine ⟨9596629166329259930523251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397752777552839953682167 9596629166329259930523251)
              ·
                refine ⟨14394943749493889895784877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596629166329259930523251 14394943749493889895784877)
                ·
                  refine ⟨5398103906060208710919329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14394943749493889895784877 5398103906060208710919329)
                  ·
                    refine ⟨4048577929545156533189497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398103906060208710919329 4048577929545156533189497)
                    ·
                      refine ⟨3036433447158867399892123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048577929545156533189497 3036433447158867399892123)
                      ·
                        rfl

theorem cell23_5913433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_5913433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913433 prefixEnd_5913433 := by exact prefixLift 5913433
  have htrace : WordTrace (prefixWord ++ tailWord_5913433) baseStart_5913433 baseEnd_5913433 := by
    simpa [prefixWord, tailWord_5913433, baseEnd_5913433] using wordTrace_append hprefix tailTrace_5913433
  have hstable : (prefixWord ++ tailWord_5913433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913433).length < 2 ^ (prefixWord ++ tailWord_5913433).sum := by decide
  have hdescent : baseEnd_5913433 < baseStart_5913433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913443 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 2, 4]
def baseStart_5913443 : Nat := 118140960795 + 5913443 * 2 ^ 59
def prefixEnd_5913443 : Nat := 4983230072969 + 3 ^ 40 * 5913443 * 2
def baseEnd_5913443 : Nat := 1012146193988470786922359

theorem tailTrace_5913443 : CollatzResearch.WordTrace tailWord_5913443 prefixEnd_5913443 1012146193988470786922359 := by
  unfold tailWord_5913443
  simp only [CollatzResearch.WordTrace]
  refine ⟨215680985115613421504424983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143787323410408947669616655 215680985115613421504424983)
  ·
    refine ⟨323521477673420132256637475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215680985115613421504424983 323521477673420132256637475)
    ·
      refine ⟨485282216510130198384956213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323521477673420132256637475 485282216510130198384956213)
      ·
        refine ⟨45495207797824706098589645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 485282216510130198384956213 45495207797824706098589645)
        ·
          refine ⟨17060702924184264786971117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45495207797824706098589645 17060702924184264786971117)
          ·
            refine ⟨6397763596569099295114169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17060702924184264786971117 6397763596569099295114169)
            ·
              refine ⟨4798322697426824471335627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397763596569099295114169 4798322697426824471335627)
              ·
                refine ⟨7197484046140236707003441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798322697426824471335627 7197484046140236707003441)
                ·
                  refine ⟨5398113034605177530252581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7197484046140236707003441 5398113034605177530252581)
                  ·
                    refine ⟨1012146193988470786922359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398113034605177530252581 1012146193988470786922359)
                    ·
                      rfl

theorem cell23_5913443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 2, 4].length) (baseStart_5913443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913443 prefixEnd_5913443 := by exact prefixLift 5913443
  have htrace : WordTrace (prefixWord ++ tailWord_5913443) baseStart_5913443 baseEnd_5913443 := by
    simpa [prefixWord, tailWord_5913443, baseEnd_5913443] using wordTrace_append hprefix tailTrace_5913443
  have hstable : (prefixWord ++ tailWord_5913443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913443).length < 2 ^ (prefixWord ++ tailWord_5913443).sum := by decide
  have hdescent : baseEnd_5913443 < baseStart_5913443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913470 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5913470 : Nat := 118140960795 + 5913470 * 2 ^ 59
def prefixEnd_5913470 : Nat := 4983230072969 + 3 ^ 40 * 5913470 * 2
def baseEnd_5913470 : Nat := 3036452445943083755129453

theorem tailTrace_5913470 : CollatzResearch.WordTrace tailWord_5913470 prefixEnd_5913470 3036452445943083755129453 := by
  unfold tailWord_5913470
  simp only [CollatzResearch.WordTrace]
  refine ⟨26960246235814450639457233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143787979924343736743771909 26960246235814450639457233)
  ·
    refine ⟨20220184676860837979592925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26960246235814450639457233 20220184676860837979592925)
    ·
      refine ⟨7582569253822814242347347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20220184676860837979592925 7582569253822814242347347)
      ·
        refine ⟨11373853880734221363521021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582569253822814242347347 11373853880734221363521021)
        ·
          refine ⟨4265195205275333011320383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11373853880734221363521021 4265195205275333011320383)
          ·
            refine ⟨6397792807912999516980575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265195205275333011320383 6397792807912999516980575)
            ·
              refine ⟨9596689211869499275470863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397792807912999516980575 9596689211869499275470863)
              ·
                refine ⟨14395033817804248913206295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596689211869499275470863 14395033817804248913206295)
                ·
                  refine ⟨21592550726706373369809443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14395033817804248913206295 21592550726706373369809443)
                  ·
                    refine ⟨32388826090059560054714165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21592550726706373369809443 32388826090059560054714165)
                    ·
                      refine ⟨3036452445943083755129453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32388826090059560054714165 3036452445943083755129453)
                      ·
                        rfl

theorem cell23_5913470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5913470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913470 prefixEnd_5913470 := by exact prefixLift 5913470
  have htrace : WordTrace (prefixWord ++ tailWord_5913470) baseStart_5913470 baseEnd_5913470 := by
    simpa [prefixWord, tailWord_5913470, baseEnd_5913470] using wordTrace_append hprefix tailTrace_5913470
  have hstable : (prefixWord ++ tailWord_5913470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913470).length < 2 ^ (prefixWord ++ tailWord_5913470).sum := by decide
  have hdescent : baseEnd_5913470 < baseStart_5913470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913489 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_5913489 : Nat := 118140960795 + 5913489 * 2 ^ 59
def prefixEnd_5913489 : Nat := 4983230072969 + 3 ^ 40 * 5913489 * 2
def baseEnd_5913489 : Nat := 3036462202075519180791865

theorem tailTrace_5913489 : CollatzResearch.WordTrace tailWord_5913489 prefixEnd_5913489 3036462202075519180791865 := by
  unfold tailWord_5913489
  simp only [CollatzResearch.WordTrace]
  refine ⟨215682662873446771360599521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143788441915631180907066347 215682662873446771360599521)
  ·
    refine ⟨161761997155085078520449641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215682662873446771360599521 161761997155085078520449641)
    ·
      refine ⟨121321497866313808890337231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161761997155085078520449641 121321497866313808890337231)
      ·
        refine ⟨181982246799470713335505847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121321497866313808890337231 181982246799470713335505847)
        ·
          refine ⟨272973370199206070003258771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181982246799470713335505847 272973370199206070003258771)
          ·
            refine ⟨409460055298809105004888157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272973370199206070003258771 409460055298809105004888157)
            ·
              refine ⟨153547520737053414376833059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409460055298809105004888157 153547520737053414376833059)
              ·
                refine ⟨230321281105580121565249589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153547520737053414376833059 230321281105580121565249589)
                ·
                  refine ⟨21592620103648136396742149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230321281105580121565249589 21592620103648136396742149)
                  ·
                    refine ⟨4048616269434025574389153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21592620103648136396742149 4048616269434025574389153)
                    ·
                      refine ⟨3036462202075519180791865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048616269434025574389153 3036462202075519180791865)
                      ·
                        rfl

theorem cell23_5913489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_5913489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913489 prefixEnd_5913489 := by exact prefixLift 5913489
  have htrace : WordTrace (prefixWord ++ tailWord_5913489) baseStart_5913489 baseEnd_5913489 := by
    simpa [prefixWord, tailWord_5913489, baseEnd_5913489] using wordTrace_append hprefix tailTrace_5913489
  have hstable : (prefixWord ++ tailWord_5913489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913489).length < 2 ^ (prefixWord ++ tailWord_5913489).sum := by decide
  have hdescent : baseEnd_5913489 < baseStart_5913489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913522 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_5913522 : Nat := 118140960795 + 5913522 * 2 ^ 59
def prefixEnd_5913522 : Nat := 4983230072969 + 3 ^ 40 * 5913522 * 2
def baseEnd_5913522 : Nat := 3036479146937117551679213

theorem tailTrace_5913522 : CollatzResearch.WordTrace tailWord_5913522 prefixEnd_5913522 3036479146937117551679213 := by
  unfold tailWord_5913522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53920966620581804499137705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143789244321551478664367213 53920966620581804499137705)
  ·
    refine ⟨40440724965436353374353279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53920966620581804499137705 40440724965436353374353279)
    ·
      refine ⟨60661087448154530061529919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40440724965436353374353279 60661087448154530061529919)
      ·
        refine ⟨90991631172231795092294879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60661087448154530061529919 90991631172231795092294879)
        ·
          refine ⟨136487446758347692638442319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90991631172231795092294879 136487446758347692638442319)
          ·
            refine ⟨204731170137521538957663479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136487446758347692638442319 204731170137521538957663479)
            ·
              refine ⟨307096755206282308436495219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204731170137521538957663479 307096755206282308436495219)
              ·
                refine ⟨460645132809423462654742829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307096755206282308436495219 460645132809423462654742829)
                ·
                  refine ⟨172741924803533798495528561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460645132809423462654742829 172741924803533798495528561)
                  ·
                    refine ⟨129556443602650348871646421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172741924803533798495528561 129556443602650348871646421)
                    ·
                      refine ⟨3036479146937117551679213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129556443602650348871646421 3036479146937117551679213)
                      ·
                        rfl

theorem cell23_5913522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_5913522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913522 prefixEnd_5913522 := by exact prefixLift 5913522
  have htrace : WordTrace (prefixWord ++ tailWord_5913522) baseStart_5913522 baseEnd_5913522 := by
    simpa [prefixWord, tailWord_5913522, baseEnd_5913522] using wordTrace_append hprefix tailTrace_5913522
  have hstable : (prefixWord ++ tailWord_5913522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913522).length < 2 ^ (prefixWord ++ tailWord_5913522).sum := by decide
  have hdescent : baseEnd_5913522 < baseStart_5913522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913552 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_5913552 : Nat := 118140960795 + 5913552 * 2 ^ 59
def prefixEnd_5913552 : Nat := 4983230072969 + 3 ^ 40 * 5913552 * 2
def baseEnd_5913552 : Nat := 3036494551356752434304075

theorem tailTrace_5913552 : CollatzResearch.WordTrace tailWord_5913552 prefixEnd_5913552 3036494551356752434304075 := by
  unfold tailWord_5913552
  simp only [CollatzResearch.WordTrace]
  refine ⟨107842480336109266560071455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143789973781479022080095273 107842480336109266560071455)
  ·
    refine ⟨161763720504163899840107183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107842480336109266560071455 161763720504163899840107183)
    ·
      refine ⟨242645580756245849760160775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161763720504163899840107183 242645580756245849760160775)
      ·
        refine ⟨363968371134368774640241163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242645580756245849760160775 363968371134368774640241163)
        ·
          refine ⟨545952556701553161960361745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363968371134368774640241163 545952556701553161960361745)
          ·
            refine ⟨409464417526164871470271309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 545952556701553161960361745 409464417526164871470271309)
            ·
              refine ⟨153549156572311826801351741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409464417526164871470271309 153549156572311826801351741)
              ·
                refine ⟨57580933714616935050506903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153549156572311826801351741 57580933714616935050506903)
                ·
                  refine ⟨86371400571925402575760355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57580933714616935050506903 86371400571925402575760355)
                  ·
                    refine ⟨129557100857888103863640533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86371400571925402575760355 129557100857888103863640533)
                    ·
                      refine ⟨3036494551356752434304075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129557100857888103863640533 3036494551356752434304075)
                      ·
                        rfl

theorem cell23_5913552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_5913552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913552 prefixEnd_5913552 := by exact prefixLift 5913552
  have htrace : WordTrace (prefixWord ++ tailWord_5913552) baseStart_5913552 baseEnd_5913552 := by
    simpa [prefixWord, tailWord_5913552, baseEnd_5913552] using wordTrace_append hprefix tailTrace_5913552
  have hstable : (prefixWord ++ tailWord_5913552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913552).length < 2 ^ (prefixWord ++ tailWord_5913552).sum := by decide
  have hdescent : baseEnd_5913552 < baseStart_5913552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913556 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5913556 : Nat := 118140960795 + 5913556 * 2 ^ 59
def prefixEnd_5913556 : Nat := 4983230072969 + 3 ^ 40 * 5913556 * 2
def baseEnd_5913556 : Nat := 3036496605279370418654057

theorem tailTrace_5913556 : CollatzResearch.WordTrace tailWord_5913556 prefixEnd_5913556 3036496605279370418654057 := by
  unfold tailWord_5913556
  simp only [CollatzResearch.WordTrace]
  refine ⟨107842553282102020901644261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143790071042802694535525681 107842553282102020901644261)
  ·
    refine ⟨20220478740394128919058299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107842553282102020901644261 20220478740394128919058299)
    ·
      refine ⟨30330718110591193378587449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20220478740394128919058299 30330718110591193378587449)
      ·
        refine ⟨22748038582943395033940587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30330718110591193378587449 22748038582943395033940587)
        ·
          refine ⟨34122057874415092550910881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22748038582943395033940587 34122057874415092550910881)
          ·
            refine ⟨25591543405811319413183161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34122057874415092550910881 25591543405811319413183161)
            ·
              refine ⟨19193657554358489559887371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25591543405811319413183161 19193657554358489559887371)
              ·
                refine ⟨28790486331537734339831057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19193657554358489559887371 28790486331537734339831057)
                ·
                  refine ⟨21592864748653300754873293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28790486331537734339831057 21592864748653300754873293)
                  ·
                    refine ⟨8097324280744987783077485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21592864748653300754873293 8097324280744987783077485)
                    ·
                      refine ⟨3036496605279370418654057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097324280744987783077485 3036496605279370418654057)
                      ·
                        rfl

theorem cell23_5913556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5913556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913556 prefixEnd_5913556 := by exact prefixLift 5913556
  have htrace : WordTrace (prefixWord ++ tailWord_5913556) baseStart_5913556 baseEnd_5913556 := by
    simpa [prefixWord, tailWord_5913556, baseEnd_5913556] using wordTrace_append hprefix tailTrace_5913556
  have hstable : (prefixWord ++ tailWord_5913556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913556).length < 2 ^ (prefixWord ++ tailWord_5913556).sum := by decide
  have hdescent : baseEnd_5913556 < baseStart_5913556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913557 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5913557 : Nat := 118140960795 + 5913557 * 2 ^ 59
def prefixEnd_5913557 : Nat := 4983230072969 + 3 ^ 40 * 5913557 * 2
def baseEnd_5913557 : Nat := 3036497118760024914741553

theorem tailTrace_5913557 : CollatzResearch.WordTrace tailWord_5913557 prefixEnd_5913557 3036497118760024914741553 := by
  unfold tailWord_5913557
  simp only [CollatzResearch.WordTrace]
  refine ⟨215685143037200418974074925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143790095358133612649383283 215685143037200418974074925)
  ·
    refine ⟨80881928638950157115278097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215685143037200418974074925 80881928638950157115278097)
    ·
      refine ⟨60661446479212617836458573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80881928638950157115278097 60661446479212617836458573)
      ·
        refine ⟨22748042429704731688671965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60661446479212617836458573 22748042429704731688671965)
        ·
          refine ⟨8530515911139274383251987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22748042429704731688671965 8530515911139274383251987)
          ·
            refine ⟨12795773866708911574877981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8530515911139274383251987 12795773866708911574877981)
            ·
              refine ⟨4798415200015841840579243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12795773866708911574877981 4798415200015841840579243)
              ·
                refine ⟨7197622800023762760868865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798415200015841840579243 7197622800023762760868865)
                ·
                  refine ⟨5398217100017822070651649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7197622800023762760868865 5398217100017822070651649)
                  ·
                    refine ⟨4048662825013366552988737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398217100017822070651649 4048662825013366552988737)
                    ·
                      refine ⟨3036497118760024914741553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048662825013366552988737 3036497118760024914741553)
                      ·
                        rfl

theorem cell23_5913557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5913557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913557 prefixEnd_5913557 := by exact prefixLift 5913557
  have htrace : WordTrace (prefixWord ++ tailWord_5913557) baseStart_5913557 baseEnd_5913557 := by
    simpa [prefixWord, tailWord_5913557, baseEnd_5913557] using wordTrace_append hprefix tailTrace_5913557
  have hstable : (prefixWord ++ tailWord_5913557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913557).length < 2 ^ (prefixWord ++ tailWord_5913557).sum := by decide
  have hdescent : baseEnd_5913557 < baseStart_5913557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913596 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_5913596 : Nat := 118140960795 + 5913596 * 2 ^ 59
def prefixEnd_5913596 : Nat := 4983230072969 + 3 ^ 40 * 5913596 * 2
def baseEnd_5913596 : Nat := 3036517144505550262153873

theorem tailTrace_5913596 : CollatzResearch.WordTrace tailWord_5913596 prefixEnd_5913596 3036517144505550262153873 := by
  unfold tailWord_5913596
  simp only [CollatzResearch.WordTrace]
  refine ⟨107843282742029564317372321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143791043656039419089829761 107843282742029564317372321)
  ·
    refine ⟨80882462056522173238029241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107843282742029564317372321 80882462056522173238029241)
    ·
      refine ⟨60661846542391629928521931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80882462056522173238029241 60661846542391629928521931)
      ·
        refine ⟨90992769813587444892782897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60661846542391629928521931 90992769813587444892782897)
        ·
          refine ⟨68244577360190583669587173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90992769813587444892782897 68244577360190583669587173)
          ·
            refine ⟨12795858255035734438047595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68244577360190583669587173 12795858255035734438047595)
            ·
              refine ⟨19193787382553601657071393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12795858255035734438047595 19193787382553601657071393)
              ·
                refine ⟨14395340536915201242803545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19193787382553601657071393 14395340536915201242803545)
                ·
                  refine ⟨10796505402686400932102659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14395340536915201242803545 10796505402686400932102659)
                  ·
                    refine ⟨16194758104029601398153989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10796505402686400932102659 16194758104029601398153989)
                    ·
                      refine ⟨3036517144505550262153873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16194758104029601398153989 3036517144505550262153873)
                      ·
                        rfl

theorem cell23_5913596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_5913596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913596 prefixEnd_5913596 := by exact prefixLift 5913596
  have htrace : WordTrace (prefixWord ++ tailWord_5913596) baseStart_5913596 baseEnd_5913596 := by
    simpa [prefixWord, tailWord_5913596, baseEnd_5913596] using wordTrace_append hprefix tailTrace_5913596
  have hstable : (prefixWord ++ tailWord_5913596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913596).length < 2 ^ (prefixWord ++ tailWord_5913596).sum := by decide
  have hdescent : baseEnd_5913596 < baseStart_5913596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913633 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5913633 : Nat := 118140960795 + 5913633 * 2 ^ 59
def prefixEnd_5913633 : Nat := 4983230072969 + 3 ^ 40 * 5913633 * 2
def baseEnd_5913633 : Nat := 3036536143289766617391203

theorem tailTrace_5913633 : CollatzResearch.WordTrace tailWord_5913633 prefixEnd_5913633 3036536143289766617391203 := by
  unfold tailWord_5913633
  simp only [CollatzResearch.WordTrace]
  refine ⟨215687914984925083953841553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143791943323283389302561035 215687914984925083953841553)
  ·
    refine ⟨161765936238693812965381165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215687914984925083953841553 161765936238693812965381165)
    ·
      refine ⟨60662226089510179862017937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161765936238693812965381165 60662226089510179862017937)
      ·
        refine ⟨45496669567132634896513453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60662226089510179862017937 45496669567132634896513453)
        ·
          refine ⟨17061251087674738086192545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45496669567132634896513453 17061251087674738086192545)
          ·
            refine ⟨12795938315756053564644409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17061251087674738086192545 12795938315756053564644409)
            ·
              refine ⟨9596953736817040173483307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12795938315756053564644409 9596953736817040173483307)
              ·
                refine ⟨14395430605225560260224961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9596953736817040173483307 14395430605225560260224961)
                ·
                  refine ⟨10796572953919170195168721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14395430605225560260224961 10796572953919170195168721)
                  ·
                    refine ⟨8097429715439377646376541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10796572953919170195168721 8097429715439377646376541)
                    ·
                      refine ⟨3036536143289766617391203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097429715439377646376541 3036536143289766617391203)
                      ·
                        rfl

theorem cell23_5913633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5913633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913633 prefixEnd_5913633 := by exact prefixLift 5913633
  have htrace : WordTrace (prefixWord ++ tailWord_5913633) baseStart_5913633 baseEnd_5913633 := by
    simpa [prefixWord, tailWord_5913633, baseEnd_5913633] using wordTrace_append hprefix tailTrace_5913633
  have hstable : (prefixWord ++ tailWord_5913633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913633).length < 2 ^ (prefixWord ++ tailWord_5913633).sum := by decide
  have hdescent : baseEnd_5913633 < baseStart_5913633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913657 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 1, 4]
def baseStart_5913657 : Nat := 118140960795 + 5913657 * 2 ^ 59
def prefixEnd_5913657 : Nat := 4983230072969 + 3 ^ 40 * 5913657 * 2
def baseEnd_5913657 : Nat := 1012182822275158174497031

theorem tailTrace_5913657 : CollatzResearch.WordTrace tailWord_5913657 prefixEnd_5913657 1012182822275158174497031 := by
  unfold tailWord_5913657
  simp only [CollatzResearch.WordTrace]
  refine ⟨215688790336838136052715225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143792526891225424035143483 215688790336838136052715225)
  ·
    refine ⟨161766592752628602039536419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215688790336838136052715225 161766592752628602039536419)
    ·
      refine ⟨242649889128942903059304629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161766592752628602039536419 242649889128942903059304629)
      ·
        refine ⟨22748427105838397161809809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242649889128942903059304629 22748427105838397161809809)
        ·
          refine ⟨17061320329378797871357357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22748427105838397161809809 17061320329378797871357357)
          ·
            refine ⟨6397995123517049201759009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17061320329378797871357357 6397995123517049201759009)
            ·
              refine ⟨4798496342637786901319257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6397995123517049201759009 4798496342637786901319257)
              ·
                refine ⟨3598872256978340175989443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4798496342637786901319257 3598872256978340175989443)
                ·
                  refine ⟨5398308385467510263984165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598872256978340175989443 5398308385467510263984165)
                  ·
                    refine ⟨1012182822275158174497031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398308385467510263984165 1012182822275158174497031)
                    ·
                      rfl

theorem cell23_5913657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 1, 4].length) (baseStart_5913657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913657 prefixEnd_5913657 := by exact prefixLift 5913657
  have htrace : WordTrace (prefixWord ++ tailWord_5913657) baseStart_5913657 baseEnd_5913657 := by
    simpa [prefixWord, tailWord_5913657, baseEnd_5913657] using wordTrace_append hprefix tailTrace_5913657
  have hstable : (prefixWord ++ tailWord_5913657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913657).length < 2 ^ (prefixWord ++ tailWord_5913657).sum := by decide
  have hdescent : baseEnd_5913657 < baseStart_5913657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913689 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_5913689 : Nat := 118140960795 + 5913689 * 2 ^ 59
def prefixEnd_5913689 : Nat := 4983230072969 + 3 ^ 40 * 5913689 * 2
def baseEnd_5913689 : Nat := 3036564898206418398290945

theorem tailTrace_5913689 : CollatzResearch.WordTrace tailWord_5913689 prefixEnd_5913689 3036564898206418398290945 := by
  unfold tailWord_5913689
  simp only [CollatzResearch.WordTrace]
  refine ⟨215689957472722205517880121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143793304981814803678586747 215689957472722205517880121)
  ·
    refine ⟨161767468104541654138410091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215689957472722205517880121 161767468104541654138410091)
    ·
      refine ⟨242651202156812481207615137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161767468104541654138410091 242651202156812481207615137)
      ·
        refine ⟨181988401617609360905711353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242651202156812481207615137 181988401617609360905711353)
        ·
          refine ⟨136491301213207020679283515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181988401617609360905711353 136491301213207020679283515)
          ·
            refine ⟨204736951819810531018925273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136491301213207020679283515 204736951819810531018925273)
            ·
              refine ⟨153552713864857898264193955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204736951819810531018925273 153552713864857898264193955)
              ·
                refine ⟨230329070797286847396290933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153552713864857898264193955 230329070797286847396290933)
                ·
                  refine ⟨21593350387245641943402275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230329070797286847396290933 21593350387245641943402275)
                  ·
                    refine ⟨32390025580868462915103413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21593350387245641943402275 32390025580868462915103413)
                    ·
                      refine ⟨3036564898206418398290945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32390025580868462915103413 3036564898206418398290945)
                      ·
                        rfl

theorem cell23_5913689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_5913689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913689 prefixEnd_5913689 := by exact prefixLift 5913689
  have htrace : WordTrace (prefixWord ++ tailWord_5913689) baseStart_5913689 baseEnd_5913689 := by
    simpa [prefixWord, tailWord_5913689, baseEnd_5913689] using wordTrace_append hprefix tailTrace_5913689
  have hstable : (prefixWord ++ tailWord_5913689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913689).length < 2 ^ (prefixWord ++ tailWord_5913689).sum := by decide
  have hdescent : baseEnd_5913689 < baseStart_5913689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913696 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_5913696 : Nat := 118140960795 + 5913696 * 2 ^ 59
def prefixEnd_5913696 : Nat := 4983230072969 + 3 ^ 40 * 5913696 * 2
def baseEnd_5913696 : Nat := 1012189497523666623634471

theorem tailTrace_5913696 : CollatzResearch.WordTrace tailWord_5913696 prefixEnd_5913696 1012189497523666623634471 := by
  unfold tailWord_5913696
  simp only [CollatzResearch.WordTrace]
  refine ⟨107845106391848422856692471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143793475189131230475589961 107845106391848422856692471)
  ·
    refine ⟨161767659587772634285038707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107845106391848422856692471 161767659587772634285038707)
    ·
      refine ⟨242651489381658951427558061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161767659587772634285038707 242651489381658951427558061)
      ·
        refine ⟨90994308518122106785334273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242651489381658951427558061 90994308518122106785334273)
        ·
          refine ⟨68245731388591580089000705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90994308518122106785334273 68245731388591580089000705)
          ·
            refine ⟨51184298541443685066750529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68245731388591580089000705 51184298541443685066750529)
            ·
              refine ⟨38388223906082763800062897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51184298541443685066750529 38388223906082763800062897)
              ·
                refine ⟨28791167929562072850047173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38388223906082763800062897 28791167929562072850047173)
                ·
                  refine ⟨5398343986792888659383845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28791167929562072850047173 5398343986792888659383845)
                  ·
                    refine ⟨1012189497523666623634471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398343986792888659383845 1012189497523666623634471)
                    ·
                      rfl

theorem cell23_5913696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_5913696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913696 prefixEnd_5913696 := by exact prefixLift 5913696
  have htrace : WordTrace (prefixWord ++ tailWord_5913696) baseStart_5913696 baseEnd_5913696 := by
    simpa [prefixWord, tailWord_5913696, baseEnd_5913696] using wordTrace_append hprefix tailTrace_5913696
  have hstable : (prefixWord ++ tailWord_5913696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913696).length < 2 ^ (prefixWord ++ tailWord_5913696).sum := by decide
  have hdescent : baseEnd_5913696 < baseStart_5913696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913699 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5913699 : Nat := 118140960795 + 5913699 * 2 ^ 59
def prefixEnd_5913699 : Nat := 4983230072969 + 3 ^ 40 * 5913699 * 2
def baseEnd_5913699 : Nat := 3036570033012963359165899

theorem tailTrace_5913699 : CollatzResearch.WordTrace tailWord_5913699 prefixEnd_5913699 3036570033012963359165899 := by
  unfold tailWord_5913699
  simp only [CollatzResearch.WordTrace]
  refine ⟨215690322202685977225744151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143793548135123984817162767 215690322202685977225744151)
  ·
    refine ⟨323535483304028965838616227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215690322202685977225744151 323535483304028965838616227)
    ·
      refine ⟨485303224956043448757924341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323535483304028965838616227 485303224956043448757924341)
      ·
        refine ⟨45497177339629073321055407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 485303224956043448757924341 45497177339629073321055407)
        ·
          refine ⟨68245766009443609981583111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45497177339629073321055407 68245766009443609981583111)
          ·
            refine ⟨102368649014165414972374667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68245766009443609981583111 102368649014165414972374667)
            ·
              refine ⟨153552973521248122458562001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102368649014165414972374667 153552973521248122458562001)
              ·
                refine ⟨115164730140936091843921501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153552973521248122458562001 115164730140936091843921501)
                ·
                  refine ⟨43186773802851034441470563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115164730140936091843921501 43186773802851034441470563)
                  ·
                    refine ⟨64780160704276551662205845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43186773802851034441470563 64780160704276551662205845)
                    ·
                      refine ⟨3036570033012963359165899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64780160704276551662205845 3036570033012963359165899)
                      ·
                        rfl

theorem cell23_5913699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5913699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913699 prefixEnd_5913699 := by exact prefixLift 5913699
  have htrace : WordTrace (prefixWord ++ tailWord_5913699) baseStart_5913699 baseEnd_5913699 := by
    simpa [prefixWord, tailWord_5913699, baseEnd_5913699] using wordTrace_append hprefix tailTrace_5913699
  have hstable : (prefixWord ++ tailWord_5913699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913699).length < 2 ^ (prefixWord ++ tailWord_5913699).sum := by decide
  have hdescent : baseEnd_5913699 < baseStart_5913699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913703 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_5913703 : Nat := 118140960795 + 5913703 * 2 ^ 59
def prefixEnd_5913703 : Nat := 4983230072969 + 3 ^ 40 * 5913703 * 2
def baseEnd_5913703 : Nat := 3036572086935581343515881

theorem tailTrace_5913703 : CollatzResearch.WordTrace tailWord_5913703 prefixEnd_5913703 3036572086935581343515881 := by
  unfold tailWord_5913703
  simp only [CollatzResearch.WordTrace]
  refine ⟨215690468094671485908889763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143793645396447657272593175 215690468094671485908889763)
  ·
    refine ⟨323535702142007228863334645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215690468094671485908889763 323535702142007228863334645)
    ·
      refine ⟨30331472075813177705937623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323535702142007228863334645 30331472075813177705937623)
      ·
        refine ⟨45497208113719766558906435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30331472075813177705937623 45497208113719766558906435)
        ·
          refine ⟨68245812170579649838359653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45497208113719766558906435 68245812170579649838359653)
          ·
            refine ⟨12796089781983684344692435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68245812170579649838359653 12796089781983684344692435)
            ·
              refine ⟨19194134672975526517038653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12796089781983684344692435 19194134672975526517038653)
              ·
                refine ⟨7197800502365822443889495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19194134672975526517038653 7197800502365822443889495)
                ·
                  refine ⟨10796700753548733665834243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7197800502365822443889495 10796700753548733665834243)
                  ·
                    refine ⟨16195051130323100498751365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10796700753548733665834243 16195051130323100498751365)
                    ·
                      refine ⟨3036572086935581343515881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16195051130323100498751365 3036572086935581343515881)
                      ·
                        rfl

theorem cell23_5913703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_5913703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913703 prefixEnd_5913703 := by exact prefixLift 5913703
  have htrace : WordTrace (prefixWord ++ tailWord_5913703) baseStart_5913703 baseEnd_5913703 := by
    simpa [prefixWord, tailWord_5913703, baseEnd_5913703] using wordTrace_append hprefix tailTrace_5913703
  have hstable : (prefixWord ++ tailWord_5913703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913703).length < 2 ^ (prefixWord ++ tailWord_5913703).sum := by decide
  have hdescent : baseEnd_5913703 < baseStart_5913703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913739 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 2, 7]
def baseStart_5913739 : Nat := 118140960795 + 5913739 * 2 ^ 59
def prefixEnd_5913739 : Nat := 4983230072969 + 3 ^ 40 * 5913739 * 2
def baseEnd_5913739 : Nat := 1012196857413047734221905

theorem tailTrace_5913739 : CollatzResearch.WordTrace tailWord_5913739 prefixEnd_5913739 1012196857413047734221905 := by
  unfold tailWord_5913739
  simp only [CollatzResearch.WordTrace]
  refine ⟨215691781122541064057200271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143794520748360709371466847 215691781122541064057200271)
  ·
    refine ⟨323537671683811596085800407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215691781122541064057200271 323537671683811596085800407)
    ·
      refine ⟨485306507525717394128700611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323537671683811596085800407 485306507525717394128700611)
      ·
        refine ⟨727959761288576091193050917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485306507525717394128700611 727959761288576091193050917)
        ·
          refine ⟨136492455241608017098697047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 727959761288576091193050917 136492455241608017098697047)
          ·
            refine ⟨204738682862412025648045571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136492455241608017098697047 204738682862412025648045571)
            ·
              refine ⟨307108024293618038472068357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204738682862412025648045571 307108024293618038472068357)
              ·
                refine ⟨57582754555053382213512817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 307108024293618038472068357 57582754555053382213512817)
                ·
                  refine ⟨43187065916290036660134613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57582754555053382213512817 43187065916290036660134613)
                  ·
                    refine ⟨1012196857413047734221905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43187065916290036660134613 1012196857413047734221905)
                    ·
                      rfl

theorem cell23_5913739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_5913739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913739 prefixEnd_5913739 := by exact prefixLift 5913739
  have htrace : WordTrace (prefixWord ++ tailWord_5913739) baseStart_5913739 baseEnd_5913739 := by
    simpa [prefixWord, tailWord_5913739, baseEnd_5913739] using wordTrace_append hprefix tailTrace_5913739
  have hstable : (prefixWord ++ tailWord_5913739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913739).length < 2 ^ (prefixWord ++ tailWord_5913739).sum := by decide
  have hdescent : baseEnd_5913739 < baseStart_5913739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913754 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5913754 : Nat := 118140960795 + 5913754 * 2 ^ 59
def prefixEnd_5913754 : Nat := 4983230072969 + 3 ^ 40 * 5913754 * 2
def baseEnd_5913754 : Nat := 3036598274448960643978147

theorem tailTrace_5913754 : CollatzResearch.WordTrace tailWord_5913754 prefixEnd_5913754 3036598274448960643978147 := by
  unfold tailWord_5913754
  simp only [CollatzResearch.WordTrace]
  refine ⟨53923082054371680404749079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143794885478324481079330877 53923082054371680404749079)
  ·
    refine ⟨80884623081557520607123619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53923082054371680404749079 80884623081557520607123619)
    ·
      refine ⟨121326934622336280910685429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80884623081557520607123619 121326934622336280910685429)
      ·
        refine ⟨11374400120844026335376759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121326934622336280910685429 11374400120844026335376759)
        ·
          refine ⟨17061600181266039503065139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11374400120844026335376759 17061600181266039503065139)
          ·
            refine ⟨25592400271899059254597709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17061600181266039503065139 25592400271899059254597709)
            ·
              refine ⟨9597150101962147220474141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25592400271899059254597709 9597150101962147220474141)
              ·
                refine ⟨3598931288235805207677803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9597150101962147220474141 3598931288235805207677803)
                ·
                  refine ⟨5398396932353707811516705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598931288235805207677803 5398396932353707811516705)
                  ·
                    refine ⟨4048797699265280858637529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398396932353707811516705 4048797699265280858637529)
                    ·
                      refine ⟨3036598274448960643978147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048797699265280858637529 3036598274448960643978147)
                      ·
                        rfl

theorem cell23_5913754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5913754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913754 prefixEnd_5913754 := by exact prefixLift 5913754
  have htrace : WordTrace (prefixWord ++ tailWord_5913754) baseStart_5913754 baseEnd_5913754 := by
    simpa [prefixWord, tailWord_5913754, baseEnd_5913754] using wordTrace_append hprefix tailTrace_5913754
  have hstable : (prefixWord ++ tailWord_5913754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913754).length < 2 ^ (prefixWord ++ tailWord_5913754).sum := by decide
  have hdescent : baseEnd_5913754 < baseStart_5913754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913769 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_5913769 : Nat := 118140960795 + 5913769 * 2 ^ 59
def prefixEnd_5913769 : Nat := 4983230072969 + 3 ^ 40 * 5913769 * 2
def baseEnd_5913769 : Nat := 1012201992219592695096859

theorem tailTrace_5913769 : CollatzResearch.WordTrace tailWord_5913769 prefixEnd_5913769 1012201992219592695096859 := by
  unfold tailWord_5913769
  simp only [CollatzResearch.WordTrace]
  refine ⟨215692875312432379180792361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143795250208288252787194907 215692875312432379180792361)
  ·
    refine ⟨161769656484324284385594271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215692875312432379180792361 161769656484324284385594271)
    ·
      refine ⟨242654484726486426578391407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161769656484324284385594271 242654484726486426578391407)
      ·
        refine ⟨363981727089729639867587111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242654484726486426578391407 363981727089729639867587111)
        ·
          refine ⟨545972590634594459801380667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363981727089729639867587111 545972590634594459801380667)
          ·
            refine ⟨818958885951891689702071001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545972590634594459801380667 818958885951891689702071001)
            ·
              refine ⟨614219164463918767276553251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 818958885951891689702071001 614219164463918767276553251)
              ·
                refine ⟨921328746695878150914829877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614219164463918767276553251 921328746695878150914829877)
                ·
                  refine ⟨86374570002738576648265301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 921328746695878150914829877 86374570002738576648265301)
                  ·
                    refine ⟨1012201992219592695096859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86374570002738576648265301 1012201992219592695096859)
                    ·
                      rfl

theorem cell23_5913769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_5913769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913769 prefixEnd_5913769 := by exact prefixLift 5913769
  have htrace : WordTrace (prefixWord ++ tailWord_5913769) baseStart_5913769 baseEnd_5913769 := by
    simpa [prefixWord, tailWord_5913769, baseEnd_5913769] using wordTrace_append hprefix tailTrace_5913769
  have hstable : (prefixWord ++ tailWord_5913769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913769).length < 2 ^ (prefixWord ++ tailWord_5913769).sum := by decide
  have hdescent : baseEnd_5913769 < baseStart_5913769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913810 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_5913810 : Nat := 118140960795 + 5913810 * 2 ^ 59
def prefixEnd_5913810 : Nat := 4983230072969 + 3 ^ 40 * 5913810 * 2
def baseEnd_5913810 : Nat := 3036627029365612424877889

theorem tailTrace_5913810 : CollatzResearch.WordTrace tailWord_5913810 prefixEnd_5913810 3036627029365612424877889 := by
  unfold tailWord_5913810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53923592676320960795758721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143796247136855895455356589 53923592676320960795758721)
  ·
    refine ⟨40442694507240720596819041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53923592676320960795758721 40442694507240720596819041)
    ·
      refine ⟨30332020880430540447614281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40442694507240720596819041 30332020880430540447614281)
      ·
        refine ⟨22749015660322905335710711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30332020880430540447614281 22749015660322905335710711)
        ·
          refine ⟨34123523490484358003566067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22749015660322905335710711 34123523490484358003566067)
          ·
            refine ⟨51185285235726537005349101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34123523490484358003566067 51185285235726537005349101)
            ·
              refine ⟨19194481963397451377005913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51185285235726537005349101 19194481963397451377005913)
              ·
                refine ⟨14395861472548088532754435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19194481963397451377005913 14395861472548088532754435)
                ·
                  refine ⟨21593792208822132799131653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14395861472548088532754435 21593792208822132799131653)
                  ·
                    refine ⟨4048836039154149899837185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21593792208822132799131653 4048836039154149899837185)
                    ·
                      refine ⟨3036627029365612424877889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048836039154149899837185 3036627029365612424877889)
                      ·
                        rfl

theorem cell23_5913810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_5913810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913810 prefixEnd_5913810 := by exact prefixLift 5913810
  have htrace : WordTrace (prefixWord ++ tailWord_5913810) baseStart_5913810 baseEnd_5913810 := by
    simpa [prefixWord, tailWord_5913810, baseEnd_5913810] using wordTrace_append hprefix tailTrace_5913810
  have hstable : (prefixWord ++ tailWord_5913810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913810).length < 2 ^ (prefixWord ++ tailWord_5913810).sum := by decide
  have hdescent : baseEnd_5913810 < baseStart_5913810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913813 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5913813 : Nat := 118140960795 + 5913813 * 2 ^ 59
def prefixEnd_5913813 : Nat := 4983230072969 + 3 ^ 40 * 5913813 * 2
def baseEnd_5913813 : Nat := 3036628569807575913140375

theorem tailTrace_5913813 : CollatzResearch.WordTrace tailWord_5913813 prefixEnd_5913813 3036628569807575913140375 := by
  unfold tailWord_5913813
  simp only [CollatzResearch.WordTrace]
  refine ⟨215694480124272974695394093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143796320082848649796929395 215694480124272974695394093)
  ·
    refine ⟨80885430046602365510772785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215694480124272974695394093 80885430046602365510772785)
    ·
      refine ⟨60664072534951774133079589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80885430046602365510772785 60664072534951774133079589)
      ·
        refine ⟨11374513600303457649952423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60664072534951774133079589 11374513600303457649952423)
        ·
          refine ⟨17061770400455186474928635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11374513600303457649952423 17061770400455186474928635)
          ·
            refine ⟨25592655600682779712392953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17061770400455186474928635 25592655600682779712392953)
            ·
              refine ⟨19194491700512084784294715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25592655600682779712392953 19194491700512084784294715)
              ·
                refine ⟨28791737550768127176442073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19194491700512084784294715 28791737550768127176442073)
                ·
                  refine ⟨21593803163076095382331555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28791737550768127176442073 21593803163076095382331555)
                  ·
                    refine ⟨32390704744614143073497333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21593803163076095382331555 32390704744614143073497333)
                    ·
                      refine ⟨3036628569807575913140375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32390704744614143073497333 3036628569807575913140375)
                      ·
                        rfl

theorem cell23_5913813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5913813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913813 prefixEnd_5913813 := by exact prefixLift 5913813
  have htrace : WordTrace (prefixWord ++ tailWord_5913813) baseStart_5913813 baseEnd_5913813 := by
    simpa [prefixWord, tailWord_5913813, baseEnd_5913813] using wordTrace_append hprefix tailTrace_5913813
  have hstable : (prefixWord ++ tailWord_5913813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913813).length < 2 ^ (prefixWord ++ tailWord_5913813).sum := by decide
  have hdescent : baseEnd_5913813 < baseStart_5913813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913843 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3]
def baseStart_5913843 : Nat := 118140960795 + 5913843 * 2 ^ 59
def prefixEnd_5913843 : Nat := 4983230072969 + 3 ^ 40 * 5913843 * 2
def baseEnd_5913843 : Nat := 3036643974227210795765237

theorem tailTrace_5913843 : CollatzResearch.WordTrace tailWord_5913843 prefixEnd_5913843 3036643974227210795765237 := by
  unfold tailWord_5913843
  simp only [CollatzResearch.WordTrace]
  refine ⟨215695574314164289818986183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143797049542776193212657455 215695574314164289818986183)
  ·
    refine ⟨323543361471246434728479275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215695574314164289818986183 323543361471246434728479275)
    ·
      refine ⟨485315042206869652092718913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323543361471246434728479275 485315042206869652092718913)
      ·
        refine ⟨363986281655152239069539185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485315042206869652092718913 363986281655152239069539185)
        ·
          refine ⟨272989711241364179302154389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363986281655152239069539185 272989711241364179302154389)
          ·
            refine ⟨12796392714438945904788487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 272989711241364179302154389 12796392714438945904788487)
            ·
              refine ⟨19194589071658418857182731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12796392714438945904788487 19194589071658418857182731)
              ·
                refine ⟨28791883607487628285774097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19194589071658418857182731 28791883607487628285774097)
                ·
                  refine ⟨21593912705615721214330573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28791883607487628285774097 21593912705615721214330573)
                  ·
                    refine ⟨8097717264605895455373965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21593912705615721214330573 8097717264605895455373965)
                    ·
                      refine ⟨3036643974227210795765237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097717264605895455373965 3036643974227210795765237)
                      ·
                        rfl

theorem cell23_5913843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_5913843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913843 prefixEnd_5913843 := by exact prefixLift 5913843
  have htrace : WordTrace (prefixWord ++ tailWord_5913843) baseStart_5913843 baseEnd_5913843 := by
    simpa [prefixWord, tailWord_5913843, baseEnd_5913843] using wordTrace_append hprefix tailTrace_5913843
  have hstable : (prefixWord ++ tailWord_5913843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913843).length < 2 ^ (prefixWord ++ tailWord_5913843).sum := by decide
  have hdescent : baseEnd_5913843 < baseStart_5913843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913927 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 1, 4]
def baseStart_5913927 : Nat := 118140960795 + 5913927 * 2 ^ 59
def prefixEnd_5913927 : Nat := 4983230072969 + 3 ^ 40 * 5913927 * 2
def baseEnd_5913927 : Nat := 1012229035534062822371617

theorem tailTrace_5913927 : CollatzResearch.WordTrace tailWord_5913927 prefixEnd_5913927 1012229035534062822371617 := by
  unfold tailWord_5913927
  simp only [CollatzResearch.WordTrace]
  refine ⟨215698638045859972165044035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143799092030573314776696023 215698638045859972165044035)
  ·
    refine ⟨323547957068789958247566053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215698638045859972165044035 323547957068789958247566053)
    ·
      refine ⟨60665241950398117171418635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323547957068789958247566053 60665241950398117171418635)
      ·
        refine ⟨90997862925597175757127953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60665241950398117171418635 90997862925597175757127953)
        ·
          refine ⟨68248397194197881817845965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90997862925597175757127953 68248397194197881817845965)
          ·
            refine ⟨25593148947824205681692237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68248397194197881817845965 25593148947824205681692237)
            ·
              refine ⟨9597430855434077130634589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25593148947824205681692237 9597430855434077130634589)
              ·
                refine ⟨3599036570787778923987971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9597430855434077130634589 3599036570787778923987971)
                ·
                  refine ⟨5398554856181668385981957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599036570787778923987971 5398554856181668385981957)
                  ·
                    refine ⟨1012229035534062822371617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398554856181668385981957 1012229035534062822371617)
                    ·
                      rfl

theorem cell23_5913927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_5913927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913927 prefixEnd_5913927 := by exact prefixLift 5913927
  have htrace : WordTrace (prefixWord ++ tailWord_5913927) baseStart_5913927 baseEnd_5913927 := by
    simpa [prefixWord, tailWord_5913927, baseEnd_5913927] using wordTrace_append hprefix tailTrace_5913927
  have hstable : (prefixWord ++ tailWord_5913927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913927).length < 2 ^ (prefixWord ++ tailWord_5913927).sum := by decide
  have hdescent : baseEnd_5913927 < baseStart_5913927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5913987 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 1, 5]
def baseStart_5913987 : Nat := 118140960795 + 5913987 * 2 ^ 59
def prefixEnd_5913987 : Nat := 4983230072969 + 3 ^ 40 * 5913987 * 2
def baseEnd_5913987 : Nat := 1012239305147152744121525

theorem tailTrace_5913987 : CollatzResearch.WordTrace tailWord_5913987 prefixEnd_5913987 1012239305147152744121525 := by
  unfold tailWord_5913987
  simp only [CollatzResearch.WordTrace]
  refine ⟨215700826425642602412228215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143800550950428401608152143 215700826425642602412228215)
  ·
    refine ⟨323551239638463903618342323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215700826425642602412228215 323551239638463903618342323)
    ·
      refine ⟨485326859457695855427513485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323551239638463903618342323 485326859457695855427513485)
      ·
        refine ⟨181997572296635945785317557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485326859457695855427513485 181997572296635945785317557)
        ·
          refine ⟨17062272402809619917373521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 181997572296635945785317557 17062272402809619917373521)
          ·
            refine ⟨12796704302107214938030141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17062272402809619917373521 12796704302107214938030141)
            ·
              refine ⟨4798764113290205601761303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12796704302107214938030141 4798764113290205601761303)
              ·
                refine ⟨7198146169935308402641955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798764113290205601761303 7198146169935308402641955)
                ·
                  refine ⟨10797219254902962603962933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198146169935308402641955 10797219254902962603962933)
                  ·
                    refine ⟨1012239305147152744121525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10797219254902962603962933 1012239305147152744121525)
                    ·
                      rfl

theorem cell23_5913987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 5].length) (baseStart_5913987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5913987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5913987 prefixEnd_5913987 := by exact prefixLift 5913987
  have htrace : WordTrace (prefixWord ++ tailWord_5913987) baseStart_5913987 baseEnd_5913987 := by
    simpa [prefixWord, tailWord_5913987, baseEnd_5913987] using wordTrace_append hprefix tailTrace_5913987
  have hstable : (prefixWord ++ tailWord_5913987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5913987).length < 2 ^ (prefixWord ++ tailWord_5913987).sum := by decide
  have hdescent : baseEnd_5913987 < baseStart_5913987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5913987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914007 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_5914007 : Nat := 118140960795 + 5914007 * 2 ^ 59
def prefixEnd_5914007 : Nat := 4983230072969 + 3 ^ 40 * 5914007 * 2
def baseEnd_5914007 : Nat := 3036728185054548154114483

theorem tailTrace_5914007 : CollatzResearch.WordTrace tailWord_5914007 prefixEnd_5914007 3036728185054548154114483 := by
  unfold tailWord_5914007
  simp only [CollatzResearch.WordTrace]
  refine ⟨215701555885570145827956275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143801037257046763885304183 215701555885570145827956275)
  ·
    refine ⟨323552333828355218741934413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215701555885570145827956275 323552333828355218741934413)
    ·
      refine ⟨121332125185633207028225405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323552333828355218741934413 121332125185633207028225405)
      ·
        refine ⟨45499546944612452635584527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121332125185633207028225405 45499546944612452635584527)
        ·
          refine ⟨68249320416918678953376791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45499546944612452635584527 68249320416918678953376791)
          ·
            refine ⟨102373980625378018430065187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68249320416918678953376791 102373980625378018430065187)
            ·
              refine ⟨153560970938067027645097781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102373980625378018430065187 153560970938067027645097781)
              ·
                refine ⟨14396341025443783841727917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153560970938067027645097781 14396341025443783841727917)
                ·
                  refine ⟨5398627884541418940647969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14396341025443783841727917 5398627884541418940647969)
                  ·
                    refine ⟨4048970913406064205485977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398627884541418940647969 4048970913406064205485977)
                    ·
                      refine ⟨3036728185054548154114483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4048970913406064205485977 3036728185054548154114483)
                      ·
                        rfl

theorem cell23_5914007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_5914007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914007 prefixEnd_5914007 := by exact prefixLift 5914007
  have htrace : WordTrace (prefixWord ++ tailWord_5914007) baseStart_5914007 baseEnd_5914007 := by
    simpa [prefixWord, tailWord_5914007, baseEnd_5914007] using wordTrace_append hprefix tailTrace_5914007
  have hstable : (prefixWord ++ tailWord_5914007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914007).length < 2 ^ (prefixWord ++ tailWord_5914007).sum := by decide
  have hdescent : baseEnd_5914007 < baseStart_5914007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914010 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_5914010 : Nat := 118140960795 + 5914010 * 2 ^ 59
def prefixEnd_5914010 : Nat := 4983230072969 + 3 ^ 40 * 5914010 * 2
def baseEnd_5914010 : Nat := 3036729725496511642376969

theorem tailTrace_5914010 : CollatzResearch.WordTrace tailWord_5914010 prefixEnd_5914010 3036729725496511642376969 := by
  unfold tailWord_5914010
  simp only [CollatzResearch.WordTrace]
  refine ⟨53925416326139819335078871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143801110203039518226876989 53925416326139819335078871)
  ·
    refine ⟨80888124489209729002618307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53925416326139819335078871 80888124489209729002618307)
    ·
      refine ⟨121332186733814593503927461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80888124489209729002618307 121332186733814593503927461)
      ·
        refine ⟨22749785012590236281986399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121332186733814593503927461 22749785012590236281986399)
        ·
          refine ⟨34124677518885354422979599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22749785012590236281986399 34124677518885354422979599)
          ·
            refine ⟨51187016278328031634469399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34124677518885354422979599 51187016278328031634469399)
            ·
              refine ⟨76780524417492047451704099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51187016278328031634469399 76780524417492047451704099)
              ·
                refine ⟨115170786626238071177556149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76780524417492047451704099 115170786626238071177556149)
                ·
                  refine ⟨10797261246209819172895889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115170786626238071177556149 10797261246209819172895889)
                  ·
                    refine ⟨8097945934657364379671917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10797261246209819172895889 8097945934657364379671917)
                    ·
                      refine ⟨3036729725496511642376969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097945934657364379671917 3036729725496511642376969)
                      ·
                        rfl

theorem cell23_5914010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_5914010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914010 prefixEnd_5914010 := by exact prefixLift 5914010
  have htrace : WordTrace (prefixWord ++ tailWord_5914010) baseStart_5914010 baseEnd_5914010 := by
    simpa [prefixWord, tailWord_5914010, baseEnd_5914010] using wordTrace_append hprefix tailTrace_5914010
  have hstable : (prefixWord ++ tailWord_5914010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914010).length < 2 ^ (prefixWord ++ tailWord_5914010).sum := by decide
  have hdescent : baseEnd_5914010 < baseStart_5914010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914040 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_5914040 : Nat := 118140960795 + 5914040 * 2 ^ 59
def prefixEnd_5914040 : Nat := 4983230072969 + 3 ^ 40 * 5914040 * 2
def baseEnd_5914040 : Nat := 3036745129916146525001831

theorem tailTrace_5914040 : CollatzResearch.WordTrace tailWord_5914040 prefixEnd_5914040 3036745129916146525001831 := by
  unfold tailWord_5914040
  simp only [CollatzResearch.WordTrace]
  refine ⟨107851379747225296231953787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143801839662967061642605049 107851379747225296231953787)
  ·
    refine ⟨161777069620837944347930681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107851379747225296231953787 161777069620837944347930681)
    ·
      refine ⟨121332802215628458260948011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161777069620837944347930681 121332802215628458260948011)
      ·
        refine ⟨181999203323442687391422017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121332802215628458260948011 181999203323442687391422017)
        ·
          refine ⟨136499402492582015543566513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181999203323442687391422017 136499402492582015543566513)
          ·
            refine ⟨102374551869436511657674885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136499402492582015543566513 102374551869436511657674885)
            ·
              refine ⟨19195228475519345935814041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102374551869436511657674885 19195228475519345935814041)
              ·
                refine ⟨14396421356639509451860531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19195228475519345935814041 14396421356639509451860531)
                ·
                  refine ⟨21594632034959264177790797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14396421356639509451860531 21594632034959264177790797)
                  ·
                    refine ⟨8097987013109724066671549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21594632034959264177790797 8097987013109724066671549)
                    ·
                      refine ⟨3036745129916146525001831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097987013109724066671549 3036745129916146525001831)
                      ·
                        rfl

theorem cell23_5914040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_5914040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914040 prefixEnd_5914040 := by exact prefixLift 5914040
  have htrace : WordTrace (prefixWord ++ tailWord_5914040) baseStart_5914040 baseEnd_5914040 := by
    simpa [prefixWord, tailWord_5914040, baseEnd_5914040] using wordTrace_append hprefix tailTrace_5914040
  have hstable : (prefixWord ++ tailWord_5914040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914040).length < 2 ^ (prefixWord ++ tailWord_5914040).sum := by decide
  have hdescent : baseEnd_5914040 < baseStart_5914040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914041 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 1, 1, 4]
def baseStart_5914041 : Nat := 118140960795 + 5914041 * 2 ^ 59
def prefixEnd_5914041 : Nat := 4983230072969 + 3 ^ 40 * 5914041 * 2
def baseEnd_5914041 : Nat := 3036745643396801021089327

theorem tailTrace_5914041 : CollatzResearch.WordTrace tailWord_5914041 prefixEnd_5914041 3036745643396801021089327 := by
  unfold tailWord_5914041
  simp only [CollatzResearch.WordTrace]
  refine ⟨215702795967446969634693977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143801863978297979756462651 215702795967446969634693977)
  ·
    refine ⟨161777096975585227226020483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215702795967446969634693977 161777096975585227226020483)
    ·
      refine ⟨242665645463377840839030725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161777096975585227226020483 242665645463377840839030725)
      ·
        refine ⟨45499808524383345157318261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242665645463377840839030725 45499808524383345157318261)
        ·
          refine ⟨4265607049160938608498587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45499808524383345157318261 4265607049160938608498587)
          ·
            refine ⟨6398410573741407912747881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4265607049160938608498587 6398410573741407912747881)
            ·
              refine ⟨4798807930306055934560911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6398410573741407912747881 4798807930306055934560911)
              ·
                refine ⟨7198211895459083901841367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798807930306055934560911 7198211895459083901841367)
                ·
                  refine ⟨10797317843188625852762051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198211895459083901841367 10797317843188625852762051)
                  ·
                    refine ⟨16195976764782938779143077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10797317843188625852762051 16195976764782938779143077)
                    ·
                      refine ⟨3036745643396801021089327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16195976764782938779143077 3036745643396801021089327)
                      ·
                        rfl

theorem cell23_5914041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_5914041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914041 prefixEnd_5914041 := by exact prefixLift 5914041
  have htrace : WordTrace (prefixWord ++ tailWord_5914041) baseStart_5914041 baseEnd_5914041 := by
    simpa [prefixWord, tailWord_5914041, baseEnd_5914041] using wordTrace_append hprefix tailTrace_5914041
  have hstable : (prefixWord ++ tailWord_5914041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914041).length < 2 ^ (prefixWord ++ tailWord_5914041).sum := by decide
  have hdescent : baseEnd_5914041 < baseStart_5914041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914044 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5914044 : Nat := 118140960795 + 5914044 * 2 ^ 59
def prefixEnd_5914044 : Nat := 4983230072969 + 3 ^ 40 * 5914044 * 2
def baseEnd_5914044 : Nat := 3036747183838764509351813

theorem tailTrace_5914044 : CollatzResearch.WordTrace tailWord_5914044 prefixEnd_5914044 3036747183838764509351813 := by
  unfold tailWord_5914044
  simp only [CollatzResearch.WordTrace]
  refine ⟨107851452693218050573526593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143801936924290734098035457 107851452693218050573526593)
  ·
    refine ⟨80888589519913537930144945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107851452693218050573526593 80888589519913537930144945)
    ·
      refine ⟨60666442139935153447608709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80888589519913537930144945 60666442139935153447608709)
      ·
        refine ⟨11374957901237841271426633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60666442139935153447608709 11374957901237841271426633)
        ·
          refine ⟨8531218425928380953569975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11374957901237841271426633 8531218425928380953569975)
          ·
            refine ⟨12796827638892571430354963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8531218425928380953569975 12796827638892571430354963)
            ·
              refine ⟨19195241458338857145532445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12796827638892571430354963 19195241458338857145532445)
              ·
                refine ⟨7198215546877071429574667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19195241458338857145532445 7198215546877071429574667)
                ·
                  refine ⟨10797323320315607144362001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198215546877071429574667 10797323320315607144362001)
                  ·
                    refine ⟨8097992490236705358271501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10797323320315607144362001 8097992490236705358271501)
                    ·
                      refine ⟨3036747183838764509351813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8097992490236705358271501 3036747183838764509351813)
                      ·
                        rfl

theorem cell23_5914044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5914044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914044 prefixEnd_5914044 := by exact prefixLift 5914044
  have htrace : WordTrace (prefixWord ++ tailWord_5914044) baseStart_5914044 baseEnd_5914044 := by
    simpa [prefixWord, tailWord_5914044, baseEnd_5914044] using wordTrace_append hprefix tailTrace_5914044
  have hstable : (prefixWord ++ tailWord_5914044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914044).length < 2 ^ (prefixWord ++ tailWord_5914044).sum := by decide
  have hdescent : baseEnd_5914044 < baseStart_5914044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914063 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_5914063 : Nat := 118140960795 + 5914063 * 2 ^ 59
def prefixEnd_5914063 : Nat := 4983230072969 + 3 ^ 40 * 5914063 * 2
def baseEnd_5914063 : Nat := 3036756939971199935014225

theorem tailTrace_5914063 : CollatzResearch.WordTrace tailWord_5914063 prefixEnd_5914063 3036756939971199935014225 := by
  unfold tailWord_5914063
  simp only [CollatzResearch.WordTrace]
  refine ⟨215703598373367267391994843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143802398915578178261329895 215703598373367267391994843)
  ·
    refine ⟨323555397560050901087992265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215703598373367267391994843 323555397560050901087992265)
    ·
      refine ⟨242666548170038175815994199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323555397560050901087992265 242666548170038175815994199)
      ·
        refine ⟨363999822255057263723991299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242666548170038175815994199 363999822255057263723991299)
        ·
          refine ⟨545999733382585895585986949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363999822255057263723991299 545999733382585895585986949)
          ·
            refine ⟨102374950009234855422372553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 545999733382585895585986949 102374950009234855422372553)
            ·
              refine ⟨76781212506926141566779415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102374950009234855422372553 76781212506926141566779415)
              ·
                refine ⟨115171818760389212350169123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76781212506926141566779415 115171818760389212350169123)
                ·
                  refine ⟨172757728140583818525253685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115171818760389212350169123 172757728140583818525253685)
                  ·
                    refine ⟨16196037013179732986742533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 172757728140583818525253685 16196037013179732986742533)
                    ·
                      refine ⟨3036756939971199935014225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16196037013179732986742533 3036756939971199935014225)
                      ·
                        rfl

theorem cell23_5914063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_5914063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914063 prefixEnd_5914063 := by exact prefixLift 5914063
  have htrace : WordTrace (prefixWord ++ tailWord_5914063) baseStart_5914063 baseEnd_5914063 := by
    simpa [prefixWord, tailWord_5914063, baseEnd_5914063] using wordTrace_append hprefix tailTrace_5914063
  have hstable : (prefixWord ++ tailWord_5914063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914063).length < 2 ^ (prefixWord ++ tailWord_5914063).sum := by decide
  have hdescent : baseEnd_5914063 < baseStart_5914063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914101 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5914101 : Nat := 118140960795 + 5914101 * 2 ^ 59
def prefixEnd_5914101 : Nat := 4983230072969 + 3 ^ 40 * 5914101 * 2
def baseEnd_5914101 : Nat := 3036776452236070786339051

theorem tailTrace_5914101 : CollatzResearch.WordTrace tailWord_5914101 prefixEnd_5914101 3036776452236070786339051 := by
  unfold tailWord_5914101
  simp only [CollatzResearch.WordTrace]
  refine ⟨215704984347229599881878157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143803322898153066587918771 215704984347229599881878157)
  ·
    refine ⟨80889369130211099955704309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215704984347229599881878157 80889369130211099955704309)
    ·
      refine ⟨7583378355957290620847279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80889369130211099955704309 7583378355957290620847279)
      ·
        refine ⟨11375067533935935931270919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583378355957290620847279 11375067533935935931270919)
        ·
          refine ⟨17062601300903903896906379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375067533935935931270919 17062601300903903896906379)
          ·
            refine ⟨25593901951355855845359569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17062601300903903896906379 25593901951355855845359569)
            ·
              refine ⟨19195426463516891884019677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25593901951355855845359569 19195426463516891884019677)
              ·
                refine ⟨7198284923818834456507379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19195426463516891884019677 7198284923818834456507379)
                ·
                  refine ⟨10797427385728251684761069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7198284923818834456507379 10797427385728251684761069)
                  ·
                    refine ⟨4049035269648094381785401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10797427385728251684761069 4049035269648094381785401)
                    ·
                      refine ⟨3036776452236070786339051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049035269648094381785401 3036776452236070786339051)
                      ·
                        rfl

theorem cell23_5914101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5914101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914101 prefixEnd_5914101 := by exact prefixLift 5914101
  have htrace : WordTrace (prefixWord ++ tailWord_5914101) baseStart_5914101 baseEnd_5914101 := by
    simpa [prefixWord, tailWord_5914101, baseEnd_5914101] using wordTrace_append hprefix tailTrace_5914101
  have hstable : (prefixWord ++ tailWord_5914101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914101).length < 2 ^ (prefixWord ++ tailWord_5914101).sum := by decide
  have hdescent : baseEnd_5914101 < baseStart_5914101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914120 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 7]
def baseStart_5914120 : Nat := 118140960795 + 5914120 * 2 ^ 59
def prefixEnd_5914120 : Nat := 4983230072969 + 3 ^ 40 * 5914120 * 2
def baseEnd_5914120 : Nat := 337420689818722912444607

theorem tailTrace_5914120 : CollatzResearch.WordTrace tailWord_5914120 prefixEnd_5914120 337420689818722912444607 := by
  unfold tailWord_5914120
  simp only [CollatzResearch.WordTrace]
  refine ⟨107852838667080383063409907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143803784889440510751213209 107852838667080383063409907)
  ·
    refine ⟨161779258000620574595114861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107852838667080383063409907 161779258000620574595114861)
    ·
      refine ⟨60667221750232715473168073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161779258000620574595114861 60667221750232715473168073)
      ·
        refine ⟨45500416312674536604876055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60667221750232715473168073 45500416312674536604876055)
        ·
          refine ⟨68250624469011804907314083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45500416312674536604876055 68250624469011804907314083)
          ·
            refine ⟨102375936703517707360971125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68250624469011804907314083 102375936703517707360971125)
            ·
              refine ⟨9597744065954785065091043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102375936703517707360971125 9597744065954785065091043)
              ·
                refine ⟨14396616098932177597636565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9597744065954785065091043 14396616098932177597636565)
                ·
                  refine ⟨337420689818722912444607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14396616098932177597636565 337420689818722912444607)
                  ·
                    rfl

theorem cell23_5914120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_5914120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914120 prefixEnd_5914120 := by exact prefixLift 5914120
  have htrace : WordTrace (prefixWord ++ tailWord_5914120) baseStart_5914120 baseEnd_5914120 := by
    simpa [prefixWord, tailWord_5914120, baseEnd_5914120] using wordTrace_append hprefix tailTrace_5914120
  have hstable : (prefixWord ++ tailWord_5914120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914120).length < 2 ^ (prefixWord ++ tailWord_5914120).sum := by decide
  have hdescent : baseEnd_5914120 < baseStart_5914120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914131 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 2, 2, 2]
def baseStart_5914131 : Nat := 118140960795 + 5914131 * 2 ^ 59
def prefixEnd_5914131 : Nat := 4983230072969 + 3 ^ 40 * 5914131 * 2
def baseEnd_5914131 : Nat := 3036791856655705668963913

theorem tailTrace_5914131 : CollatzResearch.WordTrace tailWord_5914131 prefixEnd_5914131 3036791856655705668963913 := by
  unfold tailWord_5914131
  simp only [CollatzResearch.WordTrace]
  refine ⟨215706078537120915005470247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143804052358080610003646831 215706078537120915005470247)
  ·
    refine ⟨323559117805681372508205371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215706078537120915005470247 323559117805681372508205371)
    ·
      refine ⟨485338676708522058762308057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323559117805681372508205371 485338676708522058762308057)
      ·
        refine ⟨364004007531391544071731043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485338676708522058762308057 364004007531391544071731043)
        ·
          refine ⟨546006011297087316107596565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364004007531391544071731043 546006011297087316107596565)
          ·
            refine ⟨25594031779550967942543589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 546006011297087316107596565 25594031779550967942543589)
            ·
              refine ⟨4798880958665806489226923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25594031779550967942543589 4798880958665806489226923)
              ·
                refine ⟨7198321437998709733840385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4798880958665806489226923 7198321437998709733840385)
                ·
                  refine ⟨5398741078499032300380289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7198321437998709733840385 5398741078499032300380289)
                  ·
                    refine ⟨4049055808874274225285217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398741078499032300380289 4049055808874274225285217)
                    ·
                      refine ⟨3036791856655705668963913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049055808874274225285217 3036791856655705668963913)
                      ·
                        rfl

theorem cell23_5914131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 2, 2].length) (baseStart_5914131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914131 prefixEnd_5914131 := by exact prefixLift 5914131
  have htrace : WordTrace (prefixWord ++ tailWord_5914131) baseStart_5914131 baseEnd_5914131 := by
    simpa [prefixWord, tailWord_5914131, baseEnd_5914131] using wordTrace_append hprefix tailTrace_5914131
  have hstable : (prefixWord ++ tailWord_5914131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914131).length < 2 ^ (prefixWord ++ tailWord_5914131).sum := by decide
  have hdescent : baseEnd_5914131 < baseStart_5914131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914204 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5914204 : Nat := 118140960795 + 5914204 * 2 ^ 59
def prefixEnd_5914204 : Nat := 4983230072969 + 3 ^ 40 * 5914204 * 2
def baseEnd_5914204 : Nat := 3036829340743483883351077

theorem tailTrace_5914204 : CollatzResearch.WordTrace tailWord_5914204 prefixEnd_5914204 3036829340743483883351077 := by
  unfold tailWord_5914204
  simp only [CollatzResearch.WordTrace]
  refine ⟨107854370532928224236438833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143805827377237632315251777 107854370532928224236438833)
  ·
    refine ⟨80890777899696168177329125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107854370532928224236438833 80890777899696168177329125)
    ·
      refine ⟨15167020856193031533249211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80890777899696168177329125 15167020856193031533249211)
      ·
        refine ⟨22750531284289547299873817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15167020856193031533249211 22750531284289547299873817)
        ·
          refine ⟨17062898463217160474905363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22750531284289547299873817 17062898463217160474905363)
          ·
            refine ⟨25594347694825740712358045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17062898463217160474905363 25594347694825740712358045)
            ·
              refine ⟨9597880385559652767134267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25594347694825740712358045 9597880385559652767134267)
              ·
                refine ⟨14396820578339479150701401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9597880385559652767134267 14396820578339479150701401)
                ·
                  refine ⟨10797615433754609363026051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14396820578339479150701401 10797615433754609363026051)
                  ·
                    refine ⟨16196423150631914044539077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10797615433754609363026051 16196423150631914044539077)
                    ·
                      refine ⟨3036829340743483883351077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16196423150631914044539077 3036829340743483883351077)
                      ·
                        rfl

theorem cell23_5914204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5914204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914204 prefixEnd_5914204 := by exact prefixLift 5914204
  have htrace : WordTrace (prefixWord ++ tailWord_5914204) baseStart_5914204 baseEnd_5914204 := by
    simpa [prefixWord, tailWord_5914204, baseEnd_5914204] using wordTrace_append hprefix tailTrace_5914204
  have hstable : (prefixWord ++ tailWord_5914204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914204).length < 2 ^ (prefixWord ++ tailWord_5914204).sum := by decide
  have hdescent : baseEnd_5914204 < baseStart_5914204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914264 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_5914264 : Nat := 118140960795 + 5914264 * 2 ^ 59
def prefixEnd_5914264 : Nat := 4983230072969 + 3 ^ 40 * 5914264 * 2
def baseEnd_5914264 : Nat := 3036860149582753648600801

theorem tailTrace_5914264 : CollatzResearch.WordTrace tailWord_5914264 prefixEnd_5914264 3036860149582753648600801 := by
  unfold tailWord_5914264
  simp only [CollatzResearch.WordTrace]
  refine ⟨107855464722819539360030923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143807286297092719146707897 107855464722819539360030923)
  ·
    refine ⟨161783197084229309040046385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107855464722819539360030923 161783197084229309040046385)
    ·
      refine ⟨121337397813171981780034789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161783197084229309040046385 121337397813171981780034789)
      ·
        refine ⟨22750762089969746583756523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121337397813171981780034789 22750762089969746583756523)
        ·
          refine ⟨34126143134954619875634785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22750762089969746583756523 34126143134954619875634785)
          ·
            refine ⟨25594607351215964906726089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34126143134954619875634785 25594607351215964906726089)
            ·
              refine ⟨19195955513411973680044567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25594607351215964906726089 19195955513411973680044567)
              ·
                refine ⟨28793933270117960520066851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19195955513411973680044567 28793933270117960520066851)
                ·
                  refine ⟨43190899905176940780100277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28793933270117960520066851 43190899905176940780100277)
                  ·
                    refine ⟨4049146866110338198134401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43190899905176940780100277 4049146866110338198134401)
                    ·
                      refine ⟨3036860149582753648600801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049146866110338198134401 3036860149582753648600801)
                      ·
                        rfl

theorem cell23_5914264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_5914264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914264 prefixEnd_5914264 := by exact prefixLift 5914264
  have htrace : WordTrace (prefixWord ++ tailWord_5914264) baseStart_5914264 baseEnd_5914264 := by
    simpa [prefixWord, tailWord_5914264, baseEnd_5914264] using wordTrace_append hprefix tailTrace_5914264
  have hstable : (prefixWord ++ tailWord_5914264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914264).length < 2 ^ (prefixWord ++ tailWord_5914264).sum := by decide
  have hdescent : baseEnd_5914264 < baseStart_5914264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914287 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 4, 4]
def baseStart_5914287 : Nat := 118140960795 + 5914287 * 2 ^ 59
def prefixEnd_5914287 : Nat := 4983230072969 + 3 ^ 40 * 5914287 * 2
def baseEnd_5914287 : Nat := 1012290653212602352871065

theorem tailTrace_5914287 : CollatzResearch.WordTrace tailWord_5914287 prefixEnd_5914287 1012290653212602352871065 := by
  unfold tailWord_5914287
  simp only [CollatzResearch.WordTrace]
  refine ⟨215711768324555753648149115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143807845549703835765432743 215711768324555753648149115)
  ·
    refine ⟨323567652486833630472223673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215711768324555753648149115 323567652486833630472223673)
    ·
      refine ⟨242675739365125222854167755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323567652486833630472223673 242675739365125222854167755)
      ·
        refine ⟨364013609047687834281251633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242675739365125222854167755 364013609047687834281251633)
        ·
          refine ⟨273010206785765875710938725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364013609047687834281251633 273010206785765875710938725)
          ·
            refine ⟨51189413772331101695801011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273010206785765875710938725 51189413772331101695801011)
            ·
              refine ⟨76784120658496652543701517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51189413772331101695801011 76784120658496652543701517)
              ·
                refine ⟨28794045246936244703888069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76784120658496652543701517 28794045246936244703888069)
                ·
                  refine ⟨5398883483800545881979013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28794045246936244703888069 5398883483800545881979013)
                  ·
                    refine ⟨1012290653212602352871065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398883483800545881979013 1012290653212602352871065)
                    ·
                      rfl

theorem cell23_5914287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_5914287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914287 prefixEnd_5914287 := by exact prefixLift 5914287
  have htrace : WordTrace (prefixWord ++ tailWord_5914287) baseStart_5914287 baseEnd_5914287 := by
    simpa [prefixWord, tailWord_5914287, baseEnd_5914287] using wordTrace_append hprefix tailTrace_5914287
  have hstable : (prefixWord ++ tailWord_5914287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914287).length < 2 ^ (prefixWord ++ tailWord_5914287).sum := by decide
  have hdescent : baseEnd_5914287 < baseStart_5914287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914297 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5914297 : Nat := 118140960795 + 5914297 * 2 ^ 59
def prefixEnd_5914297 : Nat := 4983230072969 + 3 ^ 40 * 5914297 * 2
def baseEnd_5914297 : Nat := 3036877094444352019488149

theorem tailTrace_5914297 : CollatzResearch.WordTrace tailWord_5914297 prefixEnd_5914297 3036877094444352019488149 := by
  unfold tailWord_5914297
  simp only [CollatzResearch.WordTrace]
  refine ⟨215712133054519525356013145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143808088703013016904008763 215712133054519525356013145)
  ·
    refine ⟨161784099790889644017009859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215712133054519525356013145 161784099790889644017009859)
    ·
      refine ⟨242676149686334466025514789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161784099790889644017009859 242676149686334466025514789)
      ·
        refine ⟨45501778066187712379784023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 242676149686334466025514789 45501778066187712379784023)
        ·
          refine ⟨68252667099281568569676035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45501778066187712379784023 68252667099281568569676035)
          ·
            refine ⟨102379000648922352854514053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68252667099281568569676035 102379000648922352854514053)
            ·
              refine ⟨19196062621672941160221385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102379000648922352854514053 19196062621672941160221385)
              ·
                refine ⟨14397046966254705870166039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19196062621672941160221385 14397046966254705870166039)
                ·
                  refine ⟨21595570449382058805249059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14397046966254705870166039 21595570449382058805249059)
                  ·
                    refine ⟨32393355674073088207873589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21595570449382058805249059 32393355674073088207873589)
                    ·
                      refine ⟨3036877094444352019488149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32393355674073088207873589 3036877094444352019488149)
                      ·
                        rfl

theorem cell23_5914297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5914297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914297 prefixEnd_5914297 := by exact prefixLift 5914297
  have htrace : WordTrace (prefixWord ++ tailWord_5914297) baseStart_5914297 baseEnd_5914297 := by
    simpa [prefixWord, tailWord_5914297, baseEnd_5914297] using wordTrace_append hprefix tailTrace_5914297
  have hstable : (prefixWord ++ tailWord_5914297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914297).length < 2 ^ (prefixWord ++ tailWord_5914297).sum := by decide
  have hdescent : baseEnd_5914297 < baseStart_5914297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914304 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_5914304 : Nat := 118140960795 + 5914304 * 2 ^ 59
def prefixEnd_5914304 : Nat := 4983230072969 + 3 ^ 40 * 5914304 * 2
def baseEnd_5914304 : Nat := 1012293562936311164033539

theorem tailTrace_5914304 : CollatzResearch.WordTrace tailWord_5914304 prefixEnd_5914304 1012293562936311164033539 := by
  unfold tailWord_5914304
  simp only [CollatzResearch.WordTrace]
  refine ⟨107856194182747082775758983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143808258910329443701011977 107856194182747082775758983)
  ·
    refine ⟨161784291274120624163638475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107856194182747082775758983 161784291274120624163638475)
    ·
      refine ⟨242676436911180936245457713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161784291274120624163638475 242676436911180936245457713)
      ·
        refine ⟨182007327683385702184093285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242676436911180936245457713 182007327683385702184093285)
        ·
          refine ⟨34126373940634819159517491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182007327683385702184093285 34126373940634819159517491)
          ·
            refine ⟨51189560910952228739276237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34126373940634819159517491 51189560910952228739276237)
            ·
              refine ⟨19196085341607085777228589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51189560910952228739276237 19196085341607085777228589)
              ·
                refine ⟨7198532003102657166460721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19196085341607085777228589 7198532003102657166460721)
                ·
                  refine ⟨5398899002326992874845541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7198532003102657166460721 5398899002326992874845541)
                  ·
                    refine ⟨1012293562936311164033539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5398899002326992874845541 1012293562936311164033539)
                    ·
                      rfl

theorem cell23_5914304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_5914304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914304 prefixEnd_5914304 := by exact prefixLift 5914304
  have htrace : WordTrace (prefixWord ++ tailWord_5914304) baseStart_5914304 baseEnd_5914304 := by
    simpa [prefixWord, tailWord_5914304, baseEnd_5914304] using wordTrace_append hprefix tailTrace_5914304
  have hstable : (prefixWord ++ tailWord_5914304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914304).length < 2 ^ (prefixWord ++ tailWord_5914304).sum := by decide
  have hdescent : baseEnd_5914304 < baseStart_5914304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914324 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5914324 : Nat := 118140960795 + 5914324 * 2 ^ 59
def prefixEnd_5914324 : Nat := 4983230072969 + 3 ^ 40 * 5914324 * 2
def baseEnd_5914324 : Nat := 3036890958422023413850525

theorem tailTrace_5914324 : CollatzResearch.WordTrace tailWord_5914324 prefixEnd_5914324 3036890958422023413850525 := by
  unfold tailWord_5914324
  simp only [CollatzResearch.WordTrace]
  refine ⟨107856558912710854483623013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143808745216947805978164017 107856558912710854483623013)
  ·
    refine ⟨20223104796133285215679315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107856558912710854483623013 20223104796133285215679315)
    ·
      refine ⟨30334657194199927823518973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20223104796133285215679315 30334657194199927823518973)
      ·
        refine ⟨11375496447824972933819615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30334657194199927823518973 11375496447824972933819615)
        ·
          refine ⟨17063244671737459400729423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375496447824972933819615 17063244671737459400729423)
          ·
            refine ⟨25594867007606189101094135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17063244671737459400729423 25594867007606189101094135)
            ·
              refine ⟨38392300511409283651641203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25594867007606189101094135 38392300511409283651641203)
              ·
                refine ⟨57588450767113925477461805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38392300511409283651641203 57588450767113925477461805)
                ·
                  refine ⟨21595669037667722054048177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57588450767113925477461805 21595669037667722054048177)
                  ·
                    refine ⟨16196751778250791540536133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21595669037667722054048177 16196751778250791540536133)
                    ·
                      refine ⟨3036890958422023413850525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16196751778250791540536133 3036890958422023413850525)
                      ·
                        rfl

theorem cell23_5914324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5914324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914324 prefixEnd_5914324 := by exact prefixLift 5914324
  have htrace : WordTrace (prefixWord ++ tailWord_5914324) baseStart_5914324 baseEnd_5914324 := by
    simpa [prefixWord, tailWord_5914324, baseEnd_5914324] using wordTrace_append hprefix tailTrace_5914324
  have hstable : (prefixWord ++ tailWord_5914324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914324).length < 2 ^ (prefixWord ++ tailWord_5914324).sum := by decide
  have hdescent : baseEnd_5914324 < baseStart_5914324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914328 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 1, 2, 2]
def baseStart_5914328 : Nat := 118140960795 + 5914328 * 2 ^ 59
def prefixEnd_5914328 : Nat := 4983230072969 + 3 ^ 40 * 5914328 * 2
def baseEnd_5914328 : Nat := 3036893012344641398200507

theorem tailTrace_5914328 : CollatzResearch.WordTrace tailWord_5914328 prefixEnd_5914328 3036893012344641398200507 := by
  unfold tailWord_5914328
  simp only [CollatzResearch.WordTrace]
  refine ⟨107856631858703608825195819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143808842478271478433594425 107856631858703608825195819)
  ·
    refine ⟨161784947788055413237793729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107856631858703608825195819 161784947788055413237793729)
    ·
      refine ⟨121338710841041559928345297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161784947788055413237793729 121338710841041559928345297)
      ·
        refine ⟨91004033130781169946258973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121338710841041559928345297 91004033130781169946258973)
        ·
          refine ⟨34126512424042938729847115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91004033130781169946258973 34126512424042938729847115)
          ·
            refine ⟨51189768636064408094770673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34126512424042938729847115 51189768636064408094770673)
            ·
              refine ⟨38392326477048306071078005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51189768636064408094770673 38392326477048306071078005)
              ·
                refine ⟨3599280607223278694163563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38392326477048306071078005 3599280607223278694163563)
                ·
                  refine ⟨5398920910834918041245345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599280607223278694163563 5398920910834918041245345)
                  ·
                    refine ⟨4049190683126188530934009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5398920910834918041245345 4049190683126188530934009)
                    ·
                      refine ⟨3036893012344641398200507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049190683126188530934009 3036893012344641398200507)
                      ·
                        rfl

theorem cell23_5914328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_5914328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914328 prefixEnd_5914328 := by exact prefixLift 5914328
  have htrace : WordTrace (prefixWord ++ tailWord_5914328) baseStart_5914328 baseEnd_5914328 := by
    simpa [prefixWord, tailWord_5914328, baseEnd_5914328] using wordTrace_append hprefix tailTrace_5914328
  have hstable : (prefixWord ++ tailWord_5914328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914328).length < 2 ^ (prefixWord ++ tailWord_5914328).sum := by decide
  have hdescent : baseEnd_5914328 < baseStart_5914328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914387 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3]
def baseStart_5914387 : Nat := 118140960795 + 5914387 * 2 ^ 59
def prefixEnd_5914387 : Nat := 4983230072969 + 3 ^ 40 * 5914387 * 2
def baseEnd_5914387 : Nat := 3036923307703256667362735

theorem tailTrace_5914387 : CollatzResearch.WordTrace tailWord_5914387 prefixEnd_5914387 3036923307703256667362735 := by
  unfold tailWord_5914387
  simp only [CollatzResearch.WordTrace]
  refine ⟨215715415624193470726789415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143810277082795647151192943 215715415624193470726789415)
  ·
    refine ⟨323573123436290206090184123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215715415624193470726789415 323573123436290206090184123)
    ·
      refine ⟨485359685154435309135276185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323573123436290206090184123 485359685154435309135276185)
      ·
        refine ⟨364019763865826481851457139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485359685154435309135276185 364019763865826481851457139)
        ·
          refine ⟨546029645798739722777185709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364019763865826481851457139 546029645798739722777185709)
          ·
            refine ⟨204761117174527396041444641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546029645798739722777185709 204761117174527396041444641)
            ·
              refine ⟨153570837880895547031083481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204761117174527396041444641 153570837880895547031083481)
              ·
                refine ⟨115178128410671660273312611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153570837880895547031083481 115178128410671660273312611)
                ·
                  refine ⟨172767192616007490409968917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115178128410671660273312611 172767192616007490409968917)
                  ·
                    refine ⟨8098462153875351112967293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 172767192616007490409968917 8098462153875351112967293)
                    ·
                      refine ⟨3036923307703256667362735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8098462153875351112967293 3036923307703256667362735)
                      ·
                        rfl

theorem cell23_5914387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_5914387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914387 prefixEnd_5914387 := by exact prefixLift 5914387
  have htrace : WordTrace (prefixWord ++ tailWord_5914387) baseStart_5914387 baseEnd_5914387 := by
    simpa [prefixWord, tailWord_5914387, baseEnd_5914387] using wordTrace_append hprefix tailTrace_5914387
  have hstable : (prefixWord ++ tailWord_5914387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914387).length < 2 ^ (prefixWord ++ tailWord_5914387).sum := by decide
  have hdescent : baseEnd_5914387 < baseStart_5914387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914418 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_5914418 : Nat := 118140960795 + 5914418 * 2 ^ 59
def prefixEnd_5914418 : Nat := 4983230072969 + 3 ^ 40 * 5914418 * 2
def baseEnd_5914418 : Nat := 3036939225603546046075093

theorem tailTrace_5914418 : CollatzResearch.WordTrace tailWord_5914418 prefixEnd_5914418 3036939225603546046075093 := by
  unfold tailWord_5914418
  simp only [CollatzResearch.WordTrace]
  refine ⟨53929136571770290755291977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143811030858054108680778605 53929136571770290755291977)
  ·
    refine ⟨40446852428827718066468983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53929136571770290755291977 40446852428827718066468983)
    ·
      refine ⟨60670278643241577099703475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40446852428827718066468983 60670278643241577099703475)
      ·
        refine ⟨91005417964862365649555213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60670278643241577099703475 91005417964862365649555213)
        ·
          refine ⟨34127031736823387118583205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91005417964862365649555213 34127031736823387118583205)
          ·
            refine ⟨6398818450654385084734351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34127031736823387118583205 6398818450654385084734351)
            ·
              refine ⟨9598227675981577627101527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6398818450654385084734351 9598227675981577627101527)
              ·
                refine ⟨14397341513972366440652291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9598227675981577627101527 14397341513972366440652291)
                ·
                  refine ⟨21596012270958549660978437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14397341513972366440652291 21596012270958549660978437)
                  ·
                    refine ⟨4049252300804728061433457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21596012270958549660978437 4049252300804728061433457)
                    ·
                      refine ⟨3036939225603546046075093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049252300804728061433457 3036939225603546046075093)
                      ·
                        rfl

theorem cell23_5914418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_5914418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914418 prefixEnd_5914418 := by exact prefixLift 5914418
  have htrace : WordTrace (prefixWord ++ tailWord_5914418) baseStart_5914418 baseEnd_5914418 := by
    simpa [prefixWord, tailWord_5914418, baseEnd_5914418] using wordTrace_append hprefix tailTrace_5914418
  have hstable : (prefixWord ++ tailWord_5914418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914418).length < 2 ^ (prefixWord ++ tailWord_5914418).sum := by decide
  have hdescent : baseEnd_5914418 < baseStart_5914418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914437 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_5914437 : Nat := 118140960795 + 5914437 * 2 ^ 59
def prefixEnd_5914437 : Nat := 4983230072969 + 3 ^ 40 * 5914437 * 2
def baseEnd_5914437 : Nat := 1012316327245327157245835

theorem tailTrace_5914437 : CollatzResearch.WordTrace tailWord_5914437 prefixEnd_5914437 1012316327245327157245835 := by
  unfold tailWord_5914437
  simp only [CollatzResearch.WordTrace]
  refine ⟨215717239274012329266109565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143811492849341552844073043 215717239274012329266109565)
  ·
    refine ⟨80893964727754623474791087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215717239274012329266109565 80893964727754623474791087)
    ·
      refine ⟨121340947091631935212186631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80893964727754623474791087 121340947091631935212186631)
      ·
        refine ⟨182011420637447902818279947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121340947091631935212186631 182011420637447902818279947)
        ·
          refine ⟨273017130956171854227419921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182011420637447902818279947 273017130956171854227419921)
          ·
            refine ⟨204762848217128890670564941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273017130956171854227419921 204762848217128890670564941)
            ·
              refine ⟨76786068081423334001461853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204762848217128890670564941 76786068081423334001461853)
              ·
                refine ⟨28794775530533750250548195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76786068081423334001461853 28794775530533750250548195)
                ·
                  refine ⟨43192163295800625375822293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28794775530533750250548195 43192163295800625375822293)
                  ·
                    refine ⟨1012316327245327157245835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43192163295800625375822293 1012316327245327157245835)
                    ·
                      rfl

theorem cell23_5914437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_5914437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914437 prefixEnd_5914437 := by exact prefixLift 5914437
  have htrace : WordTrace (prefixWord ++ tailWord_5914437) baseStart_5914437 baseEnd_5914437 := by
    simpa [prefixWord, tailWord_5914437, baseEnd_5914437] using wordTrace_append hprefix tailTrace_5914437
  have hstable : (prefixWord ++ tailWord_5914437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914437).length < 2 ^ (prefixWord ++ tailWord_5914437).sum := by decide
  have hdescent : baseEnd_5914437 < baseStart_5914437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914438 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5914438 : Nat := 118140960795 + 5914438 * 2 ^ 59
def prefixEnd_5914438 : Nat := 4983230072969 + 3 ^ 40 * 5914438 * 2
def baseEnd_5914438 : Nat := 3036949495216635967825001

theorem tailTrace_5914438 : CollatzResearch.WordTrace tailWord_5914438 prefixEnd_5914438 3036949495216635967825001 := by
  unfold tailWord_5914438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741164867094022076152999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143811517164672470957930645 6741164867094022076152999)
  ·
    refine ⟨10111747300641033114229499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6741164867094022076152999 10111747300641033114229499)
    ·
      refine ⟨15167620950961549671344249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10111747300641033114229499 15167620950961549671344249)
      ·
        refine ⟨11375715713221162253508187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15167620950961549671344249 11375715713221162253508187)
        ·
          refine ⟨17063573569831743380262281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375715713221162253508187 17063573569831743380262281)
          ·
            refine ⟨12797680177373807535196711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17063573569831743380262281 12797680177373807535196711)
            ·
              refine ⟨19196520266060711302795067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12797680177373807535196711 19196520266060711302795067)
              ·
                refine ⟨28794780399091066954192601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19196520266060711302795067 28794780399091066954192601)
                ·
                  refine ⟨21596085299318300215644451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28794780399091066954192601 21596085299318300215644451)
                  ·
                    refine ⟨32394127948977450323466677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21596085299318300215644451 32394127948977450323466677)
                    ·
                      refine ⟨3036949495216635967825001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32394127948977450323466677 3036949495216635967825001)
                      ·
                        rfl

theorem cell23_5914438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5914438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914438 prefixEnd_5914438 := by exact prefixLift 5914438
  have htrace : WordTrace (prefixWord ++ tailWord_5914438) baseStart_5914438 baseEnd_5914438 := by
    simpa [prefixWord, tailWord_5914438, baseEnd_5914438] using wordTrace_append hprefix tailTrace_5914438
  have hstable : (prefixWord ++ tailWord_5914438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914438).length < 2 ^ (prefixWord ++ tailWord_5914438).sum := by decide
  have hdescent : baseEnd_5914438 < baseStart_5914438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914464 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_5914464 : Nat := 118140960795 + 5914464 * 2 ^ 59
def prefixEnd_5914464 : Nat := 4983230072969 + 3 ^ 40 * 5914464 * 2
def baseEnd_5914464 : Nat := 3036962845713652866099881

theorem tailTrace_5914464 : CollatzResearch.WordTrace tailWord_5914464 prefixEnd_5914464 3036962845713652866099881 := by
  unfold tailWord_5914464
  simp only [CollatzResearch.WordTrace]
  refine ⟨107859112022457256438671223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143812149363276341918228297 107859112022457256438671223)
  ·
    refine ⟨161788668033685884658006835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107859112022457256438671223 161788668033685884658006835)
    ·
      refine ⟨242683002050528826987010253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161788668033685884658006835 242683002050528826987010253)
      ·
        refine ⟨91006125768948310120128845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242683002050528826987010253 91006125768948310120128845)
        ·
          refine ⟨34127297163355616295048317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91006125768948310120128845 34127297163355616295048317)
          ·
            refine ⟨12797736436258356110643119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34127297163355616295048317 12797736436258356110643119)
            ·
              refine ⟨19196604654387534165964679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12797736436258356110643119 19196604654387534165964679)
              ·
                refine ⟨28794906981581301248947019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19196604654387534165964679 28794906981581301248947019)
                ·
                  refine ⟨43192360472371951873420529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28794906981581301248947019 43192360472371951873420529)
                  ·
                    refine ⟨32394270354278963905065397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43192360472371951873420529 32394270354278963905065397)
                    ·
                      refine ⟨3036962845713652866099881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32394270354278963905065397 3036962845713652866099881)
                      ·
                        rfl

theorem cell23_5914464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_5914464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914464 prefixEnd_5914464 := by exact prefixLift 5914464
  have htrace : WordTrace (prefixWord ++ tailWord_5914464) baseStart_5914464 baseEnd_5914464 := by
    simpa [prefixWord, tailWord_5914464, baseEnd_5914464] using wordTrace_append hprefix tailTrace_5914464
  have hstable : (prefixWord ++ tailWord_5914464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914464).length < 2 ^ (prefixWord ++ tailWord_5914464).sum := by decide
  have hdescent : baseEnd_5914464 < baseStart_5914464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914487 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_5914487 : Nat := 118140960795 + 5914487 * 2 ^ 59
def prefixEnd_5914487 : Nat := 4983230072969 + 3 ^ 40 * 5914487 * 2
def baseEnd_5914487 : Nat := 3036974655768706276112275

theorem tailTrace_5914487 : CollatzResearch.WordTrace tailWord_5914487 prefixEnd_5914487 3036974655768706276112275 := by
  unfold tailWord_5914487
  simp only [CollatzResearch.WordTrace]
  refine ⟨215719062923831187805429715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143812708615887458536953143 215719062923831187805429715)
  ·
    refine ⟨323578594385746781708144573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215719062923831187805429715 323578594385746781708144573)
    ·
      refine ⟨121341972894655043140554215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323578594385746781708144573 121341972894655043140554215)
      ·
        refine ⟨182012959341982564710831323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121341972894655043140554215 182012959341982564710831323)
        ·
          refine ⟨273019439012973847066246985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182012959341982564710831323 273019439012973847066246985)
          ·
            refine ⟨204764579259730385299685239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273019439012973847066246985 204764579259730385299685239)
            ·
              refine ⟨307146868889595577949527859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204764579259730385299685239 307146868889595577949527859)
              ·
                refine ⟨460720303334393366924291789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307146868889595577949527859 460720303334393366924291789)
                ·
                  refine ⟨172770113750397512596609421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460720303334393366924291789 172770113750397512596609421)
                  ·
                    refine ⟨64788792656399067223728533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 172770113750397512596609421 64788792656399067223728533)
                    ·
                      refine ⟨3036974655768706276112275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64788792656399067223728533 3036974655768706276112275)
                      ·
                        rfl

theorem cell23_5914487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_5914487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914487 prefixEnd_5914487 := by exact prefixLift 5914487
  have htrace : WordTrace (prefixWord ++ tailWord_5914487) baseStart_5914487 baseEnd_5914487 := by
    simpa [prefixWord, tailWord_5914487, baseEnd_5914487] using wordTrace_append hprefix tailTrace_5914487
  have hstable : (prefixWord ++ tailWord_5914487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914487).length < 2 ^ (prefixWord ++ tailWord_5914487).sum := by decide
  have hdescent : baseEnd_5914487 < baseStart_5914487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914591 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 1, 6]
def baseStart_5914591 : Nat := 118140960795 + 5914591 * 2 ^ 59
def prefixEnd_5914591 : Nat := 4983230072969 + 3 ^ 40 * 5914591 * 2
def baseEnd_5914591 : Nat := 1012342685918924623070599

theorem tailTrace_5914591 : CollatzResearch.WordTrace tailWord_5914591 prefixEnd_5914591 1012342685918924623070599 := by
  unfold tailWord_5914591
  simp only [CollatzResearch.WordTrace]
  refine ⟨215722856115454413567215627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143815237410302942378143751 215722856115454413567215627)
  ·
    refine ⟨323584284173181620350823441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215722856115454413567215627 323584284173181620350823441)
    ·
      refine ⟨242688213129886215263117581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323584284173181620350823441 242688213129886215263117581)
      ·
        refine ⟨91008079923707330723669093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242688213129886215263117581 91008079923707330723669093)
        ·
          refine ⟨17064014985695124510687955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91008079923707330723669093 17064014985695124510687955)
          ·
            refine ⟨25596022478542686766031933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17064014985695124510687955 25596022478542686766031933)
            ·
              refine ⟨9598508429453507537261975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25596022478542686766031933 9598508429453507537261975)
              ·
                refine ⟨14397762644180261305892963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9598508429453507537261975 14397762644180261305892963)
                ·
                  refine ⟨21596643966270391958839445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14397762644180261305892963 21596643966270391958839445)
                  ·
                    refine ⟨1012342685918924623070599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21596643966270391958839445 1012342685918924623070599)
                    ·
                      rfl

theorem cell23_5914591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_5914591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914591 prefixEnd_5914591 := by exact prefixLift 5914591
  have htrace : WordTrace (prefixWord ++ tailWord_5914591) baseStart_5914591 baseEnd_5914591 := by
    simpa [prefixWord, tailWord_5914591, baseEnd_5914591] using wordTrace_append hprefix tailTrace_5914591
  have hstable : (prefixWord ++ tailWord_5914591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914591).length < 2 ^ (prefixWord ++ tailWord_5914591).sum := by decide
  have hdescent : baseEnd_5914591 < baseStart_5914591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914609 : List Nat := [1, 2, 2, 2, 6, 1, 1, 3, 1, 1, 3]
def baseStart_5914609 : Nat := 118140960795 + 5914609 * 2 ^ 59
def prefixEnd_5914609 : Nat := 4983230072969 + 3 ^ 40 * 5914609 * 2
def baseEnd_5914609 : Nat := 3037037300408554798786715

theorem tailTrace_5914609 : CollatzResearch.WordTrace tailWord_5914609 prefixEnd_5914609 3037037300408554798786715 := by
  unfold tailWord_5914609
  simp only [CollatzResearch.WordTrace]
  refine ⟨215723512629389202641370881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143815675086259468427580587 215723512629389202641370881)
  ·
    refine ⟨161792634472041901981028161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215723512629389202641370881 161792634472041901981028161)
    ·
      refine ⟨121344475854031426485771121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161792634472041901981028161 121344475854031426485771121)
      ·
        refine ⟨91008356890523569864328341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121344475854031426485771121 91008356890523569864328341)
        ·
          refine ⟨4266016729243292337390391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91008356890523569864328341 4266016729243292337390391)
          ·
            refine ⟨6399025093864938506085587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266016729243292337390391 6399025093864938506085587)
            ·
              refine ⟨9598537640797407759128381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399025093864938506085587 9598537640797407759128381)
              ·
                refine ⟨3599451615299027909673143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9598537640797407759128381 3599451615299027909673143)
                ·
                  refine ⟨5399177422948541864509715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599451615299027909673143 5399177422948541864509715)
                  ·
                    refine ⟨8098766134422812796764573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5399177422948541864509715 8098766134422812796764573)
                    ·
                      refine ⟨3037037300408554798786715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8098766134422812796764573 3037037300408554798786715)
                      ·
                        rfl

theorem cell23_5914609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_5914609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914609 prefixEnd_5914609 := by exact prefixLift 5914609
  have htrace : WordTrace (prefixWord ++ tailWord_5914609) baseStart_5914609 baseEnd_5914609 := by
    simpa [prefixWord, tailWord_5914609, baseEnd_5914609] using wordTrace_append hprefix tailTrace_5914609
  have hstable : (prefixWord ++ tailWord_5914609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914609).length < 2 ^ (prefixWord ++ tailWord_5914609).sum := by decide
  have hdescent : baseEnd_5914609 < baseStart_5914609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914641 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_5914641 : Nat := 118140960795 + 5914641 * 2 ^ 59
def prefixEnd_5914641 : Nat := 4983230072969 + 3 ^ 40 * 5914641 * 2
def baseEnd_5914641 : Nat := 3037053731789498673586567

theorem tailTrace_5914641 : CollatzResearch.WordTrace tailWord_5914641 prefixEnd_5914641 3037053731789498673586567 := by
  unfold tailWord_5914641
  simp only [CollatzResearch.WordTrace]
  refine ⟨215724679765273272106535777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143816453176848848071023851 215724679765273272106535777)
  ·
    refine ⟨161793509823954954079901833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215724679765273272106535777 161793509823954954079901833)
    ·
      refine ⟨121345132367966215559926375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161793509823954954079901833 121345132367966215559926375)
      ·
        refine ⟨182017698551949323339889563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121345132367966215559926375 182017698551949323339889563)
        ·
          refine ⟨273026547827923985009834345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182017698551949323339889563 273026547827923985009834345)
          ·
            refine ⟨204769910870942988757375759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273026547827923985009834345 204769910870942988757375759)
            ·
              refine ⟨307154866306414483136063639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204769910870942988757375759 307154866306414483136063639)
              ·
                refine ⟨460732299459621724704095459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307154866306414483136063639 460732299459621724704095459)
                ·
                  refine ⟨691098449189432587056143189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460732299459621724704095459 691098449189432587056143189)
                  ·
                    refine ⟨4049404975719331564782089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 691098449189432587056143189 4049404975719331564782089)
                    ·
                      refine ⟨3037053731789498673586567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049404975719331564782089 3037053731789498673586567)
                      ·
                        rfl

theorem cell23_5914641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_5914641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914641 prefixEnd_5914641 := by exact prefixLift 5914641
  have htrace : WordTrace (prefixWord ++ tailWord_5914641) baseStart_5914641 baseEnd_5914641 := by
    simpa [prefixWord, tailWord_5914641, baseEnd_5914641] using wordTrace_append hprefix tailTrace_5914641
  have hstable : (prefixWord ++ tailWord_5914641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914641).length < 2 ^ (prefixWord ++ tailWord_5914641).sum := by decide
  have hdescent : baseEnd_5914641 < baseStart_5914641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914721 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_5914721 : Nat := 118140960795 + 5914721 * 2 ^ 59
def prefixEnd_5914721 : Nat := 4983230072969 + 3 ^ 40 * 5914721 * 2
def baseEnd_5914721 : Nat := 3037094810241858360586199

theorem tailTrace_5914721 : CollatzResearch.WordTrace tailWord_5914721 prefixEnd_5914721 3037094810241858360586199 := by
  unfold tailWord_5914721
  simp only [CollatzResearch.WordTrace]
  refine ⟨215727597604983445769448017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143818398403322297179632011 215727597604983445769448017)
  ·
    refine ⟨161795698203737584327086013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215727597604983445769448017 161795698203737584327086013)
    ·
      refine ⟨60673386826401594122657255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161795698203737584327086013 60673386826401594122657255)
      ·
        refine ⟨91010080239602391183985883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60673386826401594122657255 91010080239602391183985883)
        ·
          refine ⟨136515120359403586775978825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91010080239602391183985883 136515120359403586775978825)
          ·
            refine ⟨102386340269552690081984119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136515120359403586775978825 102386340269552690081984119)
            ·
              refine ⟨153579510404329035122976179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102386340269552690081984119 153579510404329035122976179)
              ·
                refine ⟨230369265606493552684464269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153579510404329035122976179 230369265606493552684464269)
                ·
                  refine ⟨86388474602435082256674101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230369265606493552684464269 86388474602435082256674101)
                  ·
                    refine ⟨8098919493978288961563197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86388474602435082256674101 8098919493978288961563197)
                    ·
                      refine ⟨3037094810241858360586199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8098919493978288961563197 3037094810241858360586199)
                      ·
                        rfl

theorem cell23_5914721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_5914721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914721 prefixEnd_5914721 := by exact prefixLift 5914721
  have htrace : WordTrace (prefixWord ++ tailWord_5914721) baseStart_5914721 baseEnd_5914721 := by
    simpa [prefixWord, tailWord_5914721, baseEnd_5914721] using wordTrace_append hprefix tailTrace_5914721
  have hstable : (prefixWord ++ tailWord_5914721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914721).length < 2 ^ (prefixWord ++ tailWord_5914721).sum := by decide
  have hdescent : baseEnd_5914721 < baseStart_5914721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914738 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_5914738 : Nat := 118140960795 + 5914738 * 2 ^ 59
def prefixEnd_5914738 : Nat := 4983230072969 + 3 ^ 40 * 5914738 * 2
def baseEnd_5914738 : Nat := 3037103539412984794073621

theorem tailTrace_5914738 : CollatzResearch.WordTrace tailWord_5914738 prefixEnd_5914738 3037103539412984794073621 := by
  unfold tailWord_5914738
  simp only [CollatzResearch.WordTrace]
  refine ⟨53932054411480464418204217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143818811763947905115211245 53932054411480464418204217)
  ·
    refine ⟨40449040808610348313653163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53932054411480464418204217 40449040808610348313653163)
    ·
      refine ⟨60673561212915522470479745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40449040808610348313653163 60673561212915522470479745)
      ·
        refine ⟨45505170909686641852859809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60673561212915522470479745 45505170909686641852859809)
        ·
          refine ⟨34128878182264981389644857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45505170909686641852859809 34128878182264981389644857)
          ·
            refine ⟨25596658636698736042233643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34128878182264981389644857 25596658636698736042233643)
            ·
              refine ⟨38394987955048104063350465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25596658636698736042233643 38394987955048104063350465)
              ·
                refine ⟨28796240966286078047512849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38394987955048104063350465 28796240966286078047512849)
                ·
                  refine ⟨21597180724714558535634637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28796240966286078047512849 21597180724714558535634637)
                  ·
                    refine ⟨8098942771767959450862989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21597180724714558535634637 8098942771767959450862989)
                    ·
                      refine ⟨3037103539412984794073621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8098942771767959450862989 3037103539412984794073621)
                      ·
                        rfl

theorem cell23_5914738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_5914738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914738 prefixEnd_5914738 := by exact prefixLift 5914738
  have htrace : WordTrace (prefixWord ++ tailWord_5914738) baseStart_5914738 baseEnd_5914738 := by
    simpa [prefixWord, tailWord_5914738, baseEnd_5914738] using wordTrace_append hprefix tailTrace_5914738
  have hstable : (prefixWord ++ tailWord_5914738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914738).length < 2 ^ (prefixWord ++ tailWord_5914738).sum := by decide
  have hdescent : baseEnd_5914738 < baseStart_5914738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914761 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_5914761 : Nat := 118140960795 + 5914761 * 2 ^ 59
def prefixEnd_5914761 : Nat := 4983230072969 + 3 ^ 40 * 5914761 * 2
def baseEnd_5914761 : Nat := 3037115349468038204086015

theorem tailTrace_5914761 : CollatzResearch.WordTrace tailWord_5914761 prefixEnd_5914761 3037115349468038204086015 := by
  unfold tailWord_5914761
  simp only [CollatzResearch.WordTrace]
  refine ⟨215729056524838532600904137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143819371016559021733936091 215729056524838532600904137)
  ·
    refine ⟨161796792393628899450678103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215729056524838532600904137 161796792393628899450678103)
    ·
      refine ⟨242695188590443349176017155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161796792393628899450678103 242695188590443349176017155)
      ·
        refine ⟨364042782885665023764025733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242695188590443349176017155 364042782885665023764025733)
        ·
          refine ⟨68258021791062191955754825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364042782885665023764025733 68258021791062191955754825)
          ·
            refine ⟨51193516343296643966816119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68258021791062191955754825 51193516343296643966816119)
            ·
              refine ⟨76790274514944965950224179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51193516343296643966816119 76790274514944965950224179)
              ·
                refine ⟨115185411772417448925336269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76790274514944965950224179 115185411772417448925336269)
                ·
                  refine ⟨43194529414656543347001101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115185411772417448925336269 43194529414656543347001101)
                  ·
                    refine ⟨16197948530496203755125413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43194529414656543347001101 16197948530496203755125413)
                    ·
                      refine ⟨3037115349468038204086015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16197948530496203755125413 3037115349468038204086015)
                      ·
                        rfl

theorem cell23_5914761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_5914761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914761 prefixEnd_5914761 := by exact prefixLift 5914761
  have htrace : WordTrace (prefixWord ++ tailWord_5914761) baseStart_5914761 baseEnd_5914761 := by
    simpa [prefixWord, tailWord_5914761, baseEnd_5914761] using wordTrace_append hprefix tailTrace_5914761
  have hstable : (prefixWord ++ tailWord_5914761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914761).length < 2 ^ (prefixWord ++ tailWord_5914761).sum := by decide
  have hdescent : baseEnd_5914761 < baseStart_5914761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914821 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_5914821 : Nat := 118140960795 + 5914821 * 2 ^ 59
def prefixEnd_5914821 : Nat := 4983230072969 + 3 ^ 40 * 5914821 * 2
def baseEnd_5914821 : Nat := 3037146158307307969335739

theorem tailTrace_5914821 : CollatzResearch.WordTrace tailWord_5914821 prefixEnd_5914821 3037146158307307969335739 := by
  unfold tailWord_5914821
  simp only [CollatzResearch.WordTrace]
  refine ⟨215731244904621162848088317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143820829936414108565392211 215731244904621162848088317)
  ·
    refine ⟨80899216839232936068033119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215731244904621162848088317 80899216839232936068033119)
    ·
      refine ⟨121348825258849404102049679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80899216839232936068033119 121348825258849404102049679)
      ·
        refine ⟨182023237888274106153074519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121348825258849404102049679 182023237888274106153074519)
        ·
          refine ⟨273034856832411159229611779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182023237888274106153074519 273034856832411159229611779)
          ·
            refine ⟨409552285248616738844417669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273034856832411159229611779 409552285248616738844417669)
            ·
              refine ⟨76791053484115638533328313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409552285248616738844417669 76791053484115638533328313)
              ·
                refine ⟨57593290113086728899996235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76791053484115638533328313 57593290113086728899996235)
                ·
                  refine ⟨86389935169630093349994353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57593290113086728899996235 86389935169630093349994353)
                  ·
                    refine ⟨64792451377222570012495765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86389935169630093349994353 64792451377222570012495765)
                    ·
                      refine ⟨3037146158307307969335739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64792451377222570012495765 3037146158307307969335739)
                      ·
                        rfl

theorem cell23_5914821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_5914821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914821 prefixEnd_5914821 := by exact prefixLift 5914821
  have htrace : WordTrace (prefixWord ++ tailWord_5914821) baseStart_5914821 baseEnd_5914821 := by
    simpa [prefixWord, tailWord_5914821, baseEnd_5914821] using wordTrace_append hprefix tailTrace_5914821
  have hstable : (prefixWord ++ tailWord_5914821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914821).length < 2 ^ (prefixWord ++ tailWord_5914821).sum := by decide
  have hdescent : baseEnd_5914821 < baseStart_5914821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914912 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_5914912 : Nat := 118140960795 + 5914912 * 2 ^ 59
def prefixEnd_5914912 : Nat := 4983230072969 + 3 ^ 40 * 5914912 * 2
def baseEnd_5914912 : Nat := 1012397628348955704432607

theorem tailTrace_5914912 : CollatzResearch.WordTrace tailWord_5914912 prefixEnd_5914912 1012397628348955704432607 := by
  unfold tailWord_5914912
  simp only [CollatzResearch.WordTrace]
  refine ⟨107867281973645742694825495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143823042631527656926433993 107867281973645742694825495)
  ·
    refine ⟨161800922960468614042238243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107867281973645742694825495 161800922960468614042238243)
    ·
      refine ⟨242701384440702921063357365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161800922960468614042238243 242701384440702921063357365)
      ·
        refine ⟨22753254791315898849689753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242701384440702921063357365 22753254791315898849689753)
        ·
          refine ⟨17064941093486924137267315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22753254791315898849689753 17064941093486924137267315)
          ·
            refine ⟨25597411640230386205900973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17064941093486924137267315 25597411640230386205900973)
            ·
              refine ⟨9599029365086394827212865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25597411640230386205900973 9599029365086394827212865)
              ·
                refine ⟨7199272023814796120409649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599029365086394827212865 7199272023814796120409649)
                ·
                  refine ⟨5399454017861097090307237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199272023814796120409649 5399454017861097090307237)
                  ·
                    refine ⟨1012397628348955704432607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399454017861097090307237 1012397628348955704432607)
                    ·
                      rfl

theorem cell23_5914912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_5914912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914912 prefixEnd_5914912 := by exact prefixLift 5914912
  have htrace : WordTrace (prefixWord ++ tailWord_5914912) baseStart_5914912 baseEnd_5914912 := by
    simpa [prefixWord, tailWord_5914912, baseEnd_5914912] using wordTrace_append hprefix tailTrace_5914912
  have hstable : (prefixWord ++ tailWord_5914912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914912).length < 2 ^ (prefixWord ++ tailWord_5914912).sum := by decide
  have hdescent : baseEnd_5914912 < baseStart_5914912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914922 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5914922 : Nat := 118140960795 + 5914922 * 2 ^ 59
def prefixEnd_5914922 : Nat := 4983230072969 + 3 ^ 40 * 5914922 * 2
def baseEnd_5914922 : Nat := 3037198019853412074172775

theorem tailTrace_5914922 : CollatzResearch.WordTrace tailWord_5914922 prefixEnd_5914922 3037198019853412074172775 := by
  unfold tailWord_5914922
  simp only [CollatzResearch.WordTrace]
  refine ⟨53933732169313814274378755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143823285784836838065010013 53933732169313814274378755)
  ·
    refine ⟨80900598253970721411568133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53933732169313814274378755 80900598253970721411568133)
    ·
      refine ⟨15168862172619510264669025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80900598253970721411568133 15168862172619510264669025)
      ·
        refine ⟨11376646629464632698501769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15168862172619510264669025 11376646629464632698501769)
        ·
          refine ⟨8532484972098474523876327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11376646629464632698501769 8532484972098474523876327)
          ·
            refine ⟨12798727458147711785814491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8532484972098474523876327 12798727458147711785814491)
            ·
              refine ⟨19198091187221567678721737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798727458147711785814491 19198091187221567678721737)
              ·
                refine ⟨14398568390416175759041303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19198091187221567678721737 14398568390416175759041303)
                ·
                  refine ⟨21597852585624263638561955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14398568390416175759041303 21597852585624263638561955)
                  ·
                    refine ⟨32396778878436395457842933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21597852585624263638561955 32396778878436395457842933)
                    ·
                      refine ⟨3037198019853412074172775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32396778878436395457842933 3037198019853412074172775)
                      ·
                        rfl

theorem cell23_5914922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5914922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914922 prefixEnd_5914922 := by exact prefixLift 5914922
  have htrace : WordTrace (prefixWord ++ tailWord_5914922) baseStart_5914922 baseEnd_5914922 := by
    simpa [prefixWord, tailWord_5914922, baseEnd_5914922] using wordTrace_append hprefix tailTrace_5914922
  have hstable : (prefixWord ++ tailWord_5914922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914922).length < 2 ^ (prefixWord ++ tailWord_5914922).sum := by decide
  have hdescent : baseEnd_5914922 < baseStart_5914922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914929 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 2, 4]
def baseStart_5914929 : Nat := 118140960795 + 5914929 * 2 ^ 59
def prefixEnd_5914929 : Nat := 4983230072969 + 3 ^ 40 * 5914929 * 2
def baseEnd_5914929 : Nat := 1012400538072664515595081

theorem tailTrace_5914929 : CollatzResearch.WordTrace tailWord_5914929 prefixEnd_5914929 1012400538072664515595081 := by
  unfold tailWord_5914929
  simp only [CollatzResearch.WordTrace]
  refine ⟨215735183988229897293019841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143823455992153264862013227 215735183988229897293019841)
  ·
    refine ⟨161801387991172422969764881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215735183988229897293019841 161801387991172422969764881)
    ·
      refine ⟨121351040993379317227323661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161801387991172422969764881 121351040993379317227323661)
      ·
        refine ⟨45506640372517243960246373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121351040993379317227323661 45506640372517243960246373)
        ·
          refine ⟨8532495069846983242546195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45506640372517243960246373 8532495069846983242546195)
          ·
            refine ⟨12798742604770474863819293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8532495069846983242546195 12798742604770474863819293)
            ·
              refine ⟨4799528476788928073932235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12798742604770474863819293 4799528476788928073932235)
              ·
                refine ⟨7199292715183392110898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799528476788928073932235 7199292715183392110898353)
                ·
                  refine ⟨5399469536387544083173765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199292715183392110898353 5399469536387544083173765)
                  ·
                    refine ⟨1012400538072664515595081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399469536387544083173765 1012400538072664515595081)
                    ·
                      rfl

theorem cell23_5914929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_5914929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914929 prefixEnd_5914929 := by exact prefixLift 5914929
  have htrace : WordTrace (prefixWord ++ tailWord_5914929) baseStart_5914929 baseEnd_5914929 := by
    simpa [prefixWord, tailWord_5914929, baseEnd_5914929] using wordTrace_append hprefix tailTrace_5914929
  have hstable : (prefixWord ++ tailWord_5914929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914929).length < 2 ^ (prefixWord ++ tailWord_5914929).sum := by decide
  have hdescent : baseEnd_5914929 < baseStart_5914929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914932 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_5914932 : Nat := 118140960795 + 5914932 * 2 ^ 59
def prefixEnd_5914932 : Nat := 4983230072969 + 3 ^ 40 * 5914932 * 2
def baseEnd_5914932 : Nat := 3037203154659957035047729

theorem tailTrace_5914932 : CollatzResearch.WordTrace tailWord_5914932 prefixEnd_5914932 3037203154659957035047729 := by
  unfold tailWord_5914932
  simp only [CollatzResearch.WordTrace]
  refine ⟨107867646703609514402689525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143823528938146019203586033 107867646703609514402689525)
  ·
    refine ⟨10112591878463391975252143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107867646703609514402689525 10112591878463391975252143)
    ·
      refine ⟨15168887817695087962878215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10112591878463391975252143 15168887817695087962878215)
      ·
        refine ⟨22753331726542631944317323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15168887817695087962878215 22753331726542631944317323)
        ·
          refine ⟨34129997589813947916475985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22753331726542631944317323 34129997589813947916475985)
          ·
            refine ⟨25597498192360460937356989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34129997589813947916475985 25597498192360460937356989)
            ·
              refine ⟨9599061822135172851508871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25597498192360460937356989 9599061822135172851508871)
              ·
                refine ⟨14398592733202759277263307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9599061822135172851508871 14398592733202759277263307)
                ·
                  refine ⟨21597889099804138915894961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14398592733202759277263307 21597889099804138915894961)
                  ·
                    refine ⟨16198416824853104186921221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21597889099804138915894961 16198416824853104186921221)
                    ·
                      refine ⟨3037203154659957035047729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16198416824853104186921221 3037203154659957035047729)
                      ·
                        rfl

theorem cell23_5914932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_5914932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914932 prefixEnd_5914932 := by exact prefixLift 5914932
  have htrace : WordTrace (prefixWord ++ tailWord_5914932) baseStart_5914932 baseEnd_5914932 := by
    simpa [prefixWord, tailWord_5914932, baseEnd_5914932] using wordTrace_append hprefix tailTrace_5914932
  have hstable : (prefixWord ++ tailWord_5914932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914932).length < 2 ^ (prefixWord ++ tailWord_5914932).sum := by decide
  have hdescent : baseEnd_5914932 < baseStart_5914932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914942 : List Nat := [4, 2, 1, 2, 1, 4, 2, 7]
def baseStart_5914942 : Nat := 118140960795 + 5914942 * 2 ^ 59
def prefixEnd_5914942 : Nat := 4983230072969 + 3 ^ 40 * 5914942 * 2
def baseEnd_5914942 : Nat := 112489195906166740589729

theorem tailTrace_5914942 : CollatzResearch.WordTrace tailWord_5914942 prefixEnd_5914942 112489195906166740589729 := by
  unfold tailWord_5914942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26966957267147850064155385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143823772091455200342162053 26966957267147850064155385)
  ·
    refine ⟨20225217950360887548116539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26966957267147850064155385 20225217950360887548116539)
    ·
      refine ⟨30337826925541331322174809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20225217950360887548116539 30337826925541331322174809)
      ·
        refine ⟨22753370194155998491631107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30337826925541331322174809 22753370194155998491631107)
        ·
          refine ⟨34130055291233997737446661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22753370194155998491631107 34130055291233997737446661)
          ·
            refine ⟨6399385367106374575771249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34130055291233997737446661 6399385367106374575771249)
            ·
              refine ⟨4799539025329780931828437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399385367106374575771249 4799539025329780931828437)
              ·
                refine ⟨112489195906166740589729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4799539025329780931828437 112489195906166740589729)
                ·
                  rfl

theorem cell23_5914942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_5914942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914942 prefixEnd_5914942 := by exact prefixLift 5914942
  have htrace : WordTrace (prefixWord ++ tailWord_5914942) baseStart_5914942 baseEnd_5914942 := by
    simpa [prefixWord, tailWord_5914942, baseEnd_5914942] using wordTrace_append hprefix tailTrace_5914942
  have hstable : (prefixWord ++ tailWord_5914942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914942).length < 2 ^ (prefixWord ++ tailWord_5914942).sum := by decide
  have hdescent : baseEnd_5914942 < baseStart_5914942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914968 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_5914968 : Nat := 118140960795 + 5914968 * 2 ^ 59
def prefixEnd_5914968 : Nat := 4983230072969 + 3 ^ 40 * 5914968 * 2
def baseEnd_5914968 : Nat := 1012407213321172964732521

theorem tailTrace_5914968 : CollatzResearch.WordTrace tailWord_5914968 prefixEnd_5914968 1012407213321172964732521 := by
  unfold tailWord_5914968
  simp only [CollatzResearch.WordTrace]
  refine ⟨107868303217544303476844779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143824404290059071302459705 107868303217544303476844779)
  ·
    refine ⟨161802454826316455215267169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107868303217544303476844779 161802454826316455215267169)
    ·
      refine ⟨121351841119737341411450377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161802454826316455215267169 121351841119737341411450377)
      ·
        refine ⟨91013880839803006058587783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121351841119737341411450377 91013880839803006058587783)
        ·
          refine ⟨136520821259704509087881675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91013880839803006058587783 136520821259704509087881675)
          ·
            refine ⟨204781231889556763631822513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136520821259704509087881675 204781231889556763631822513)
            ·
              refine ⟨153585923917167572723866885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204781231889556763631822513 153585923917167572723866885)
              ·
                refine ⟨28797360734468919885725041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153585923917167572723866885 28797360734468919885725041)
                ·
                  refine ⟨21598020550851689914293781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28797360734468919885725041 21598020550851689914293781)
                  ·
                    refine ⟨1012407213321172964732521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21598020550851689914293781 1012407213321172964732521)
                    ·
                      rfl

theorem cell23_5914968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_5914968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914968 prefixEnd_5914968 := by exact prefixLift 5914968
  have htrace : WordTrace (prefixWord ++ tailWord_5914968) baseStart_5914968 baseEnd_5914968 := by
    simpa [prefixWord, tailWord_5914968, baseEnd_5914968] using wordTrace_append hprefix tailTrace_5914968
  have hstable : (prefixWord ++ tailWord_5914968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914968).length < 2 ^ (prefixWord ++ tailWord_5914968).sum := by decide
  have hdescent : baseEnd_5914968 < baseStart_5914968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5914986 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5914986 : Nat := 118140960795 + 5914986 * 2 ^ 59
def prefixEnd_5914986 : Nat := 4983230072969 + 3 ^ 40 * 5914986 * 2
def baseEnd_5914986 : Nat := 3037230882615299823772481

theorem tailTrace_5914986 : CollatzResearch.WordTrace tailWord_5914986 prefixEnd_5914986 3037230882615299823772481 := by
  unfold tailWord_5914986
  simp only [CollatzResearch.WordTrace]
  refine ⟨53934315737255849006961203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143824841966015597351896541 53934315737255849006961203)
  ·
    refine ⟨80901473605883773510441805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53934315737255849006961203 80901473605883773510441805)
    ·
      refine ⟨30338052602206415066415677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80901473605883773510441805 30338052602206415066415677)
      ·
        refine ⟨11376769725827405649905879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30338052602206415066415677 11376769725827405649905879)
        ·
          refine ⟨17065154588741108474858819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376769725827405649905879 17065154588741108474858819)
          ·
            refine ⟨25597731883111662712288229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065154588741108474858819 25597731883111662712288229)
            ·
              refine ⟨4799574728083436758554043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25597731883111662712288229 4799574728083436758554043)
              ·
                refine ⟨7199362092125155137831065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799574728083436758554043 7199362092125155137831065)
                ·
                  refine ⟨5399521569093866353373299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199362092125155137831065 5399521569093866353373299)
                  ·
                    refine ⟨8099282353640799530059949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5399521569093866353373299 8099282353640799530059949)
                    ·
                      refine ⟨3037230882615299823772481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8099282353640799530059949 3037230882615299823772481)
                      ·
                        rfl

theorem cell23_5914986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5914986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5914986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5914986 prefixEnd_5914986 := by exact prefixLift 5914986
  have htrace : WordTrace (prefixWord ++ tailWord_5914986) baseStart_5914986 baseEnd_5914986 := by
    simpa [prefixWord, tailWord_5914986, baseEnd_5914986] using wordTrace_append hprefix tailTrace_5914986
  have hstable : (prefixWord ++ tailWord_5914986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5914986).length < 2 ^ (prefixWord ++ tailWord_5914986).sum := by decide
  have hdescent : baseEnd_5914986 < baseStart_5914986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5914986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915009 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5915009 : Nat := 118140960795 + 5915009 * 2 ^ 59
def prefixEnd_5915009 : Nat := 4983230072969 + 3 ^ 40 * 5915009 * 2
def baseEnd_5915009 : Nat := 3037242692670353233784875

theorem tailTrace_5915009 : CollatzResearch.WordTrace tailWord_5915009 prefixEnd_5915009 3037242692670353233784875 := by
  unfold tailWord_5915009
  simp only [CollatzResearch.WordTrace]
  refine ⟨215738101827940070955932081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143825401218626713970621387 215738101827940070955932081)
  ·
    refine ⟨161803576370955053216949061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215738101827940070955932081 161803576370955053216949061)
    ·
      refine ⟨30338170569554072478177949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161803576370955053216949061 30338170569554072478177949)
      ·
        refine ⟨11376813963582777179316731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30338170569554072478177949 11376813963582777179316731)
        ·
          refine ⟨17065220945374165768975097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11376813963582777179316731 17065220945374165768975097)
          ·
            refine ⟨12798915709030624326731323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17065220945374165768975097 12798915709030624326731323)
            ·
              refine ⟨19198373563545936490096985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12798915709030624326731323 19198373563545936490096985)
              ·
                refine ⟨14398780172659452367572739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19198373563545936490096985 14398780172659452367572739)
                ·
                  refine ⟨21598170258989178551359109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14398780172659452367572739 21598170258989178551359109)
                  ·
                    refine ⟨4049656923560470978379833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21598170258989178551359109 4049656923560470978379833)
                    ·
                      refine ⟨3037242692670353233784875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049656923560470978379833 3037242692670353233784875)
                      ·
                        rfl

theorem cell23_5915009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5915009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915009 prefixEnd_5915009 := by exact prefixLift 5915009
  have htrace : WordTrace (prefixWord ++ tailWord_5915009) baseStart_5915009 baseEnd_5915009 := by
    simpa [prefixWord, tailWord_5915009, baseEnd_5915009] using wordTrace_append hprefix tailTrace_5915009
  have hstable : (prefixWord ++ tailWord_5915009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915009).length < 2 ^ (prefixWord ++ tailWord_5915009).sum := by decide
  have hdescent : baseEnd_5915009 < baseStart_5915009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915042 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5915042 : Nat := 118140960795 + 5915042 * 2 ^ 59
def prefixEnd_5915042 : Nat := 4983230072969 + 3 ^ 40 * 5915042 * 2
def baseEnd_5915042 : Nat := 3037259637531951604672223

theorem tailTrace_5915042 : CollatzResearch.WordTrace tailWord_5915042 prefixEnd_5915042 3037259637531951604672223 := by
  unfold tailWord_5915042
  simp only [CollatzResearch.WordTrace]
  refine ⟨53934826359205129397970845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143826203624547011727922253 53934826359205129397970845)
  ·
    refine ⟨20225559884701923524239067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53934826359205129397970845 20225559884701923524239067)
    ·
      refine ⟨30338339827052885286358601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20225559884701923524239067 30338339827052885286358601)
      ·
        refine ⟨22753754870289663964768951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30338339827052885286358601 22753754870289663964768951)
        ·
          refine ⟨34130632305434495947153427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22753754870289663964768951 34130632305434495947153427)
          ·
            refine ⟨51195948458151743920730141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34130632305434495947153427 51195948458151743920730141)
            ·
              refine ⟨19198480671806903970273803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51195948458151743920730141 19198480671806903970273803)
              ·
                refine ⟨28797721007710355955410705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19198480671806903970273803 28797721007710355955410705)
                ·
                  refine ⟨21598290755782766966558029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28797721007710355955410705 21598290755782766966558029)
                  ·
                    refine ⟨8099359033418537612459261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21598290755782766966558029 8099359033418537612459261)
                    ·
                      refine ⟨3037259637531951604672223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8099359033418537612459261 3037259637531951604672223)
                      ·
                        rfl

theorem cell23_5915042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5915042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915042 prefixEnd_5915042 := by exact prefixLift 5915042
  have htrace : WordTrace (prefixWord ++ tailWord_5915042) baseStart_5915042 baseEnd_5915042 := by
    simpa [prefixWord, tailWord_5915042, baseEnd_5915042] using wordTrace_append hprefix tailTrace_5915042
  have hstable : (prefixWord ++ tailWord_5915042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915042).length < 2 ^ (prefixWord ++ tailWord_5915042).sum := by decide
  have hdescent : baseEnd_5915042 < baseStart_5915042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915075 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 7, 4]
def baseStart_5915075 : Nat := 118140960795 + 5915075 * 2 ^ 59
def prefixEnd_5915075 : Nat := 4983230072969 + 3 ^ 40 * 5915075 * 2
def baseEnd_5915075 : Nat := 1012425527464516658519857

theorem tailTrace_5915075 : CollatzResearch.WordTrace tailWord_5915075 prefixEnd_5915075 1012425527464516658519857 := by
  unfold tailWord_5915075
  simp only [CollatzResearch.WordTrace]
  refine ⟨215740509045700964227834679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143827006030467309485223119 215740509045700964227834679)
  ·
    refine ⟨323610763568551446341752019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215740509045700964227834679 323610763568551446341752019)
    ·
      refine ⟨485416145352827169512628029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323610763568551446341752019 485416145352827169512628029)
      ·
        refine ⟨182031054507310188567235511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485416145352827169512628029 182031054507310188567235511)
        ·
          refine ⟨273046581760965282850853267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182031054507310188567235511 273046581760965282850853267)
          ·
            refine ⟨409569872641447924276279901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273046581760965282850853267 409569872641447924276279901)
            ·
              refine ⟨153588702240542971603604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409569872641447924276279901 153588702240542971603604963)
              ·
                refine ⟨230383053360814457405407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153588702240542971603604963 230383053360814457405407445)
                ·
                  refine ⟨5399602813144088845439237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 230383053360814457405407445 5399602813144088845439237)
                  ·
                    refine ⟨1012425527464516658519857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399602813144088845439237 1012425527464516658519857)
                    ·
                      rfl

theorem cell23_5915075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 4].length) (baseStart_5915075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915075 prefixEnd_5915075 := by exact prefixLift 5915075
  have htrace : WordTrace (prefixWord ++ tailWord_5915075) baseStart_5915075 baseEnd_5915075 := by
    simpa [prefixWord, tailWord_5915075, baseEnd_5915075] using wordTrace_append hprefix tailTrace_5915075
  have hstable : (prefixWord ++ tailWord_5915075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915075).length < 2 ^ (prefixWord ++ tailWord_5915075).sum := by decide
  have hdescent : baseEnd_5915075 < baseStart_5915075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915082 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2]
def baseStart_5915082 : Nat := 118140960795 + 5915082 * 2 ^ 59
def prefixEnd_5915082 : Nat := 4983230072969 + 3 ^ 40 * 5915082 * 2
def baseEnd_5915082 : Nat := 3037280176758131448172039

theorem tailTrace_5915082 : CollatzResearch.WordTrace tailWord_5915082 prefixEnd_5915082 3037280176758131448172039 := by
  unfold tailWord_5915082
  simp only [CollatzResearch.WordTrace]
  refine ⟨53935191089168901105834875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143827176237783736282226333 53935191089168901105834875)
  ·
    refine ⟨80902786633753351658752313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53935191089168901105834875 80902786633753351658752313)
    ·
      refine ⟨60677089975315013744064235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80902786633753351658752313 60677089975315013744064235)
      ·
        refine ⟨91015634962972520616096353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60677089975315013744064235 91015634962972520616096353)
        ·
          refine ⟨68261726222229390462072265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91015634962972520616096353 68261726222229390462072265)
          ·
            refine ⟨51196294666672042846554199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68261726222229390462072265 51196294666672042846554199)
            ·
              refine ⟨76794442000008064269831299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51196294666672042846554199 76794442000008064269831299)
              ·
                refine ⟨115191663000012096404746949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76794442000008064269831299 115191663000012096404746949)
                ·
                  refine ⟨21598436812502268075890053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115191663000012096404746949 21598436812502268075890053)
                  ·
                    refine ⟨4049706902344175264229385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21598436812502268075890053 4049706902344175264229385)
                    ·
                      refine ⟨3037280176758131448172039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049706902344175264229385 3037280176758131448172039)
                      ·
                        rfl

theorem cell23_5915082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_5915082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915082 prefixEnd_5915082 := by exact prefixLift 5915082
  have htrace : WordTrace (prefixWord ++ tailWord_5915082) baseStart_5915082 baseEnd_5915082 := by
    simpa [prefixWord, tailWord_5915082, baseEnd_5915082] using wordTrace_append hprefix tailTrace_5915082
  have hstable : (prefixWord ++ tailWord_5915082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915082).length < 2 ^ (prefixWord ++ tailWord_5915082).sum := by decide
  have hdescent : baseEnd_5915082 < baseStart_5915082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915115 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3]
def baseStart_5915115 : Nat := 118140960795 + 5915115 * 2 ^ 59
def prefixEnd_5915115 : Nat := 4983230072969 + 3 ^ 40 * 5915115 * 2
def baseEnd_5915115 : Nat := 3037297121619729819059387

theorem tailTrace_5915115 : CollatzResearch.WordTrace tailWord_5915115 prefixEnd_5915115 3037297121619729819059387 := by
  unfold tailWord_5915115
  simp only [CollatzResearch.WordTrace]
  refine ⟨215741967965556051059290799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143827978643704034039527199 215741967965556051059290799)
  ·
    refine ⟨323612951948334076588936199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215741967965556051059290799 323612951948334076588936199)
    ·
      refine ⟨485419427922501114883404299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323612951948334076588936199 485419427922501114883404299)
      ·
        refine ⟨728129141883751672325106449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485419427922501114883404299 728129141883751672325106449)
        ·
          refine ⟨546096856412813754243829837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728129141883751672325106449 546096856412813754243829837)
          ·
            refine ⟨204786321154805157841436189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546096856412813754243829837 204786321154805157841436189)
            ·
              refine ⟨76794870433051934190538571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204786321154805157841436189 76794870433051934190538571)
              ·
                refine ⟨115192305649577901285807857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76794870433051934190538571 115192305649577901285807857)
                ·
                  refine ⟨86394229237183425964355893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115192305649577901285807857 86394229237183425964355893)
                  ·
                    refine ⟨8099458990985946184158365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86394229237183425964355893 8099458990985946184158365)
                    ·
                      refine ⟨3037297121619729819059387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8099458990985946184158365 3037297121619729819059387)
                      ·
                        rfl

theorem cell23_5915115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3].length) (baseStart_5915115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915115 prefixEnd_5915115 := by exact prefixLift 5915115
  have htrace : WordTrace (prefixWord ++ tailWord_5915115) baseStart_5915115 baseEnd_5915115 := by
    simpa [prefixWord, tailWord_5915115, baseEnd_5915115] using wordTrace_append hprefix tailTrace_5915115
  have hstable : (prefixWord ++ tailWord_5915115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915115).length < 2 ^ (prefixWord ++ tailWord_5915115).sum := by decide
  have hdescent : baseEnd_5915115 < baseStart_5915115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915143 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 1, 4]
def baseStart_5915143 : Nat := 118140960795 + 5915143 * 2 ^ 59
def prefixEnd_5915143 : Nat := 4983230072969 + 3 ^ 40 * 5915143 * 2
def baseEnd_5915143 : Nat := 1012437166359351903169753

theorem tailTrace_5915143 : CollatzResearch.WordTrace tailWord_5915143 prefixEnd_5915143 1012437166359351903169753 := by
  unfold tailWord_5915143
  simp only [CollatzResearch.WordTrace]
  refine ⟨215742989209454611841310083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143828659472969741227540055 215742989209454611841310083)
  ·
    refine ⟨323614483814181917761965125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215742989209454611841310083 323614483814181917761965125)
    ·
      refine ⟨60677715715159109580368461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 323614483814181917761965125 60677715715159109580368461)
      ·
        refine ⟨22754143393184666092638173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60677715715159109580368461 22754143393184666092638173)
        ·
          refine ⟨8532803772444249784739315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22754143393184666092638173 8532803772444249784739315)
          ·
            refine ⟨12799205658666374677108973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8532803772444249784739315 12799205658666374677108973)
            ·
              refine ⟨4799702121999890503915865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12799205658666374677108973 4799702121999890503915865)
              ·
                refine ⟨3599776591499917877936899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4799702121999890503915865 3599776591499917877936899)
                ·
                  refine ⟨5399664887249876816905349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599776591499917877936899 5399664887249876816905349)
                  ·
                    refine ⟨1012437166359351903169753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399664887249876816905349 1012437166359351903169753)
                    ·
                      rfl

theorem cell23_5915143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_5915143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915143 prefixEnd_5915143 := by exact prefixLift 5915143
  have htrace : WordTrace (prefixWord ++ tailWord_5915143) baseStart_5915143 baseEnd_5915143 := by
    simpa [prefixWord, tailWord_5915143, baseEnd_5915143] using wordTrace_append hprefix tailTrace_5915143
  have hstable : (prefixWord ++ tailWord_5915143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915143).length < 2 ^ (prefixWord ++ tailWord_5915143).sum := by decide
  have hdescent : baseEnd_5915143 < baseStart_5915143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915156 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 6]
def baseStart_5915156 : Nat := 118140960795 + 5915156 * 2 ^ 59
def prefixEnd_5915156 : Nat := 4983230072969 + 3 ^ 40 * 5915156 * 2
def baseEnd_5915156 : Nat := 337479797147396017627411

theorem tailTrace_5915156 : CollatzResearch.WordTrace tailWord_5915156 prefixEnd_5915156 337479797147396017627411 := by
  unfold tailWord_5915156
  simp only [CollatzResearch.WordTrace]
  refine ⟨107871731679203757530766661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143828975572271676707688881 107871731679203757530766661)
  ·
    refine ⟨20225949689850704537018749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107871731679203757530766661 20225949689850704537018749)
    ·
      refine ⟨7584731133694014201382031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20225949689850704537018749 7584731133694014201382031)
      ·
        refine ⟨11377096700541021302073047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584731133694014201382031 11377096700541021302073047)
        ·
          refine ⟨17065645050811531953109571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377096700541021302073047 17065645050811531953109571)
          ·
            refine ⟨25598467576217297929664357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065645050811531953109571 25598467576217297929664357)
            ·
              refine ⟨4799712670540743361812067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25598467576217297929664357 4799712670540743361812067)
              ·
                refine ⟨7199569005811115042718101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799712670540743361812067 7199569005811115042718101)
                ·
                  refine ⟨337479797147396017627411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7199569005811115042718101 337479797147396017627411)
                  ·
                    rfl

theorem cell23_5915156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_5915156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915156 prefixEnd_5915156 := by exact prefixLift 5915156
  have htrace : WordTrace (prefixWord ++ tailWord_5915156) baseStart_5915156 baseEnd_5915156 := by
    simpa [prefixWord, tailWord_5915156, baseEnd_5915156] using wordTrace_append hprefix tailTrace_5915156
  have hstable : (prefixWord ++ tailWord_5915156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915156).length < 2 ^ (prefixWord ++ tailWord_5915156).sum := by decide
  have hdescent : baseEnd_5915156 < baseStart_5915156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915176 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5915176 : Nat := 118140960795 + 5915176 * 2 ^ 59
def prefixEnd_5915176 : Nat := 4983230072969 + 3 ^ 40 * 5915176 * 2
def baseEnd_5915176 : Nat := 3037328443939654080396607

theorem tailTrace_5915176 : CollatzResearch.WordTrace tailWord_5915176 prefixEnd_5915176 3037328443939654080396607 := by
  unfold tailWord_5915176
  simp only [CollatzResearch.WordTrace]
  refine ⟨107872096409167529238630691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143829461878890038984840921 107872096409167529238630691)
  ·
    refine ⟨161808144613751293857946037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107872096409167529238630691 161808144613751293857946037)
    ·
      refine ⟨15169513557539183799182441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161808144613751293857946037 15169513557539183799182441)
      ·
        refine ⟨11377135168154387849386831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15169513557539183799182441 11377135168154387849386831)
        ·
          refine ⟨17065702752231581774080247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377135168154387849386831 17065702752231581774080247)
          ·
            refine ⟨25598554128347372661120371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065702752231581774080247 25598554128347372661120371)
            ·
              refine ⟨38397831192521058991680557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25598554128347372661120371 38397831192521058991680557)
              ·
                refine ⟨14399186697195397121880209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38397831192521058991680557 14399186697195397121880209)
                ·
                  refine ⟨10799390022896547841410157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14399186697195397121880209 10799390022896547841410157)
                  ·
                    refine ⟨4049771258586205440528809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10799390022896547841410157 4049771258586205440528809)
                    ·
                      refine ⟨3037328443939654080396607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049771258586205440528809 3037328443939654080396607)
                      ·
                        rfl

theorem cell23_5915176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5915176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915176 prefixEnd_5915176 := by exact prefixLift 5915176
  have htrace : WordTrace (prefixWord ++ tailWord_5915176) baseStart_5915176 baseEnd_5915176 := by
    simpa [prefixWord, tailWord_5915176, baseEnd_5915176] using wordTrace_append hprefix tailTrace_5915176
  have hstable : (prefixWord ++ tailWord_5915176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915176).length < 2 ^ (prefixWord ++ tailWord_5915176).sum := by decide
  have hdescent : baseEnd_5915176 < baseStart_5915176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915199 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 2, 4]
def baseStart_5915199 : Nat := 118140960795 + 5915199 * 2 ^ 59
def prefixEnd_5915199 : Nat := 4983230072969 + 3 ^ 40 * 5915199 * 2
def baseEnd_5915199 : Nat := 1012446751331569163469667

theorem tailTrace_5915199 : CollatzResearch.WordTrace tailWord_5915199 prefixEnd_5915199 1012446751331569163469667 := by
  unfold tailWord_5915199
  simp only [CollatzResearch.WordTrace]
  refine ⟨215745031697251733405348651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143830021131501155603565767 215745031697251733405348651)
  ·
    refine ⟨323617547545877600108022977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215745031697251733405348651 323617547545877600108022977)
    ·
      refine ⟨242713160659408200081017233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323617547545877600108022977 242713160659408200081017233)
      ·
        refine ⟨182034870494556150060762925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242713160659408200081017233 182034870494556150060762925)
        ·
          refine ⟨68263076435458556272786097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182034870494556150060762925 68263076435458556272786097)
          ·
            refine ⟨51197307326593917204589573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68263076435458556272786097 51197307326593917204589573)
            ·
              refine ⟨9599495123736359475860545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51197307326593917204589573 9599495123736359475860545)
              ·
                refine ⟨7199621342802269606895409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599495123736359475860545 7199621342802269606895409)
                ·
                  refine ⟨5399716007101702205171557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7199621342802269606895409 5399716007101702205171557)
                  ·
                    refine ⟨1012446751331569163469667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399716007101702205171557 1012446751331569163469667)
                    ·
                      rfl

theorem cell23_5915199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_5915199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915199 prefixEnd_5915199 := by exact prefixLift 5915199
  have htrace : WordTrace (prefixWord ++ tailWord_5915199) baseStart_5915199 baseEnd_5915199 := by
    simpa [prefixWord, tailWord_5915199, baseEnd_5915199] using wordTrace_append hprefix tailTrace_5915199
  have hstable : (prefixWord ++ tailWord_5915199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915199).length < 2 ^ (prefixWord ++ tailWord_5915199).sum := by decide
  have hdescent : baseEnd_5915199 < baseStart_5915199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915206 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5915206 : Nat := 118140960795 + 5915206 * 2 ^ 59
def prefixEnd_5915206 : Nat := 4983230072969 + 3 ^ 40 * 5915206 * 2
def baseEnd_5915206 : Nat := 3037343848359288963021469

theorem tailTrace_5915206 : CollatzResearch.WordTrace tailWord_5915206 prefixEnd_5915206 3037343848359288963021469 := by
  unfold tailWord_5915206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742040219007074175026671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143830191338817582400568981 6742040219007074175026671)
  ·
    refine ⟨10113060328510611262540007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742040219007074175026671 10113060328510611262540007)
    ·
      refine ⟨15169590492765916893810011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10113060328510611262540007 15169590492765916893810011)
      ·
        refine ⟨22754385739148875340715017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15169590492765916893810011 22754385739148875340715017)
        ·
          refine ⟨17065789304361656505536263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22754385739148875340715017 17065789304361656505536263)
          ·
            refine ⟨25598683956542484758304395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17065789304361656505536263 25598683956542484758304395)
            ·
              refine ⟨38398025934813727137456593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25598683956542484758304395 38398025934813727137456593)
              ·
                refine ⟨28798519451110295353092445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38398025934813727137456593 28798519451110295353092445)
                ·
                  refine ⟨10799444794166360757409667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28798519451110295353092445 10799444794166360757409667)
                  ·
                    refine ⟨16199167191249541136114501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10799444794166360757409667 16199167191249541136114501)
                    ·
                      refine ⟨3037343848359288963021469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16199167191249541136114501 3037343848359288963021469)
                      ·
                        rfl

theorem cell23_5915206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5915206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915206 prefixEnd_5915206 := by exact prefixLift 5915206
  have htrace : WordTrace (prefixWord ++ tailWord_5915206) baseStart_5915206 baseEnd_5915206 := by
    simpa [prefixWord, tailWord_5915206, baseEnd_5915206] using wordTrace_append hprefix tailTrace_5915206
  have hstable : (prefixWord ++ tailWord_5915206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915206).length < 2 ^ (prefixWord ++ tailWord_5915206).sum := by decide
  have hdescent : baseEnd_5915206 < baseStart_5915206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915215 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_5915215 : Nat := 118140960795 + 5915215 * 2 ^ 59
def prefixEnd_5915215 : Nat := 4983230072969 + 3 ^ 40 * 5915215 * 2
def baseEnd_5915215 : Nat := 3037348469685179427808927

theorem tailTrace_5915215 : CollatzResearch.WordTrace tailWord_5915215 prefixEnd_5915215 3037348469685179427808927 := by
  unfold tailWord_5915215
  simp only [CollatzResearch.WordTrace]
  refine ⟨215745615265193768137931099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143830410176795845425287399 215745615265193768137931099)
  ·
    refine ⟨323618422897790652206896649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215745615265193768137931099 323618422897790652206896649)
    ·
      refine ⟨242713817173342989155172487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323618422897790652206896649 242713817173342989155172487)
      ·
        refine ⟨364070725760014483732758731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242713817173342989155172487 364070725760014483732758731)
        ·
          refine ⟨546106088640021725599138097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364070725760014483732758731 546106088640021725599138097)
          ·
            refine ⟨409579566480016294199353573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546106088640021725599138097 409579566480016294199353573)
            ·
              refine ⟨76796168715003055162378795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409579566480016294199353573 76796168715003055162378795)
              ·
                refine ⟨115194253072504582743568193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76796168715003055162378795 115194253072504582743568193)
                ·
                  refine ⟨86395689804378437057676145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115194253072504582743568193 86395689804378437057676145)
                  ·
                    refine ⟨64796767353283827793257109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86395689804378437057676145 64796767353283827793257109)
                    ·
                      refine ⟨3037348469685179427808927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64796767353283827793257109 3037348469685179427808927)
                      ·
                        rfl

theorem cell23_5915215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_5915215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915215 prefixEnd_5915215 := by exact prefixLift 5915215
  have htrace : WordTrace (prefixWord ++ tailWord_5915215) baseStart_5915215 baseEnd_5915215 := by
    simpa [prefixWord, tailWord_5915215, baseEnd_5915215] using wordTrace_append hprefix tailTrace_5915215
  have hstable : (prefixWord ++ tailWord_5915215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915215).length < 2 ^ (prefixWord ++ tailWord_5915215).sum := by decide
  have hdescent : baseEnd_5915215 < baseStart_5915215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915239 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_5915239 : Nat := 118140960795 + 5915239 * 2 ^ 59
def prefixEnd_5915239 : Nat := 4983230072969 + 3 ^ 40 * 5915239 * 2
def baseEnd_5915239 : Nat := 3037360793220887333908817

theorem tailTrace_5915239 : CollatzResearch.WordTrace tailWord_5915239 prefixEnd_5915239 3037360793220887333908817 := by
  unfold tailWord_5915239
  simp only [CollatzResearch.WordTrace]
  refine ⟨215746490617106820236804771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143830993744737880157869847 215746490617106820236804771)
  ·
    refine ⟨323619735925660230355207157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215746490617106820236804771 323619735925660230355207157)
    ·
      refine ⟨30339350243030646595800671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 323619735925660230355207157 30339350243030646595800671)
      ·
        refine ⟨45509025364545969893701007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30339350243030646595800671 45509025364545969893701007)
        ·
          refine ⟨68263538046818954840551511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45509025364545969893701007 68263538046818954840551511)
          ·
            refine ⟨102395307070228432260827267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68263538046818954840551511 102395307070228432260827267)
            ·
              refine ⟨153592960605342648391240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102395307070228432260827267 153592960605342648391240901)
              ·
                refine ⟨28798680113501746573357669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153592960605342648391240901 28798680113501746573357669)
                ·
                  refine ⟨5399752521281577482504563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28798680113501746573357669 5399752521281577482504563)
                  ·
                    refine ⟨8099628781922366223756845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5399752521281577482504563 8099628781922366223756845)
                    ·
                      refine ⟨3037360793220887333908817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8099628781922366223756845 3037360793220887333908817)
                      ·
                        rfl

theorem cell23_5915239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_5915239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915239 prefixEnd_5915239 := by exact prefixLift 5915239
  have htrace : WordTrace (prefixWord ++ tailWord_5915239) baseStart_5915239 baseEnd_5915239 := by
    simpa [prefixWord, tailWord_5915239, baseEnd_5915239] using wordTrace_append hprefix tailTrace_5915239
  have hstable : (prefixWord ++ tailWord_5915239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915239).length < 2 ^ (prefixWord ++ tailWord_5915239).sum := by decide
  have hdescent : baseEnd_5915239 < baseStart_5915239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915240 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5915240 : Nat := 118140960795 + 5915240 * 2 ^ 59
def prefixEnd_5915240 : Nat := 4983230072969 + 3 ^ 40 * 5915240 * 2
def baseEnd_5915240 : Nat := 3037361306701541829996313

theorem tailTrace_5915240 : CollatzResearch.WordTrace tailWord_5915240 prefixEnd_5915240 3037361306701541829996313 := by
  unfold tailWord_5915240
  simp only [CollatzResearch.WordTrace]
  refine ⟨107873263545051598703795587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143831018060068798271727449 107873263545051598703795587)
  ·
    refine ⟨161809895317577398055693381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107873263545051598703795587 161809895317577398055693381)
    ·
      refine ⟨30339355372045762135442509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161809895317577398055693381 30339355372045762135442509)
      ·
        refine ⟨11377258264517160800790941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30339355372045762135442509 11377258264517160800790941)
        ·
          refine ⟨4266471849193935300296603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11377258264517160800790941 4266471849193935300296603)
          ·
            refine ⟨6399707773790902950444905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266471849193935300296603 6399707773790902950444905)
            ·
              refine ⟨4799780830343177212833679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399707773790902950444905 4799780830343177212833679)
              ·
                refine ⟨7199671245514765819250519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799780830343177212833679 7199671245514765819250519)
                ·
                  refine ⟨10799506868272148728875779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199671245514765819250519 10799506868272148728875779)
                  ·
                    refine ⟨16199260302408223093313669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10799506868272148728875779 16199260302408223093313669)
                    ·
                      refine ⟨3037361306701541829996313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16199260302408223093313669 3037361306701541829996313)
                      ·
                        rfl

theorem cell23_5915240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5915240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915240 prefixEnd_5915240 := by exact prefixLift 5915240
  have htrace : WordTrace (prefixWord ++ tailWord_5915240) baseStart_5915240 baseEnd_5915240 := by
    simpa [prefixWord, tailWord_5915240, baseEnd_5915240] using wordTrace_append hprefix tailTrace_5915240
  have hstable : (prefixWord ++ tailWord_5915240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915240).length < 2 ^ (prefixWord ++ tailWord_5915240).sum := by decide
  have hdescent : baseEnd_5915240 < baseStart_5915240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915334 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5915334 : Nat := 118140960795 + 5915334 * 2 ^ 59
def prefixEnd_5915334 : Nat := 4983230072969 + 3 ^ 40 * 5915334 * 2
def baseEnd_5915334 : Nat := 3037409573883064462220881

theorem tailTrace_5915334 : CollatzResearch.WordTrace tailWord_5915334 prefixEnd_5915334 3037409573883064462220881 := by
  unfold tailWord_5915334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742186110992582858172283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 143833303701175100974342037 6742186110992582858172283)
  ·
    refine ⟨10113279166488874287258425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742186110992582858172283 10113279166488874287258425)
    ·
      refine ⟨7584959374866655715443819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113279166488874287258425 7584959374866655715443819)
      ·
        refine ⟨11377439062299983573165729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7584959374866655715443819 11377439062299983573165729)
        ·
          refine ⟨8533079296724987679874297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11377439062299983573165729 8533079296724987679874297)
          ·
            refine ⟨6399809472543740759905723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8533079296724987679874297 6399809472543740759905723)
            ·
              refine ⟨9599714208815611139858585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399809472543740759905723 9599714208815611139858585)
              ·
                refine ⟨7199785656611708354893939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599714208815611139858585 7199785656611708354893939)
                ·
                  refine ⟨10799678484917562532340909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199785656611708354893939 10799678484917562532340909)
                  ·
                    refine ⟨4049879431844085949627841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10799678484917562532340909 4049879431844085949627841)
                    ·
                      refine ⟨3037409573883064462220881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4049879431844085949627841 3037409573883064462220881)
                      ·
                        rfl

theorem cell23_5915334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5915334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915334 prefixEnd_5915334 := by exact prefixLift 5915334
  have htrace : WordTrace (prefixWord ++ tailWord_5915334) baseStart_5915334 baseEnd_5915334 := by
    simpa [prefixWord, tailWord_5915334, baseEnd_5915334] using wordTrace_append hprefix tailTrace_5915334
  have hstable : (prefixWord ++ tailWord_5915334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915334).length < 2 ^ (prefixWord ++ tailWord_5915334).sum := by decide
  have hdescent : baseEnd_5915334 < baseStart_5915334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915369 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_5915369 : Nat := 118140960795 + 5915369 * 2 ^ 59
def prefixEnd_5915369 : Nat := 4983230072969 + 3 ^ 40 * 5915369 * 2
def baseEnd_5915369 : Nat := 3037427545705971825283219

theorem tailTrace_5915369 : CollatzResearch.WordTrace tailWord_5915369 prefixEnd_5915369 3037427545705971825283219 := by
  unfold tailWord_5915369
  simp only [CollatzResearch.WordTrace]
  refine ⟨215751232106635852439037161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143834154737757234959358107 215751232106635852439037161)
  ·
    refine ⟨161813424079976889329277871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215751232106635852439037161 161813424079976889329277871)
    ·
      refine ⟨242720136119965333993916807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161813424079976889329277871 242720136119965333993916807)
      ·
        refine ⟨364080204179948000990875211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242720136119965333993916807 364080204179948000990875211)
        ·
          refine ⟨546120306269922001486312817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364080204179948000990875211 546120306269922001486312817)
          ·
            refine ⟨409590229702441501114734613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546120306269922001486312817 409590229702441501114734613)
            ·
              refine ⟨19199542017301945364753185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 409590229702441501114734613 19199542017301945364753185)
              ·
                refine ⟨14399656512976459023564889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19199542017301945364753185 14399656512976459023564889)
                ·
                  refine ⟨10799742384732344267673667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14399656512976459023564889 10799742384732344267673667)
                  ·
                    refine ⟨16199613577098516401510501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10799742384732344267673667 16199613577098516401510501)
                    ·
                      refine ⟨3037427545705971825283219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16199613577098516401510501 3037427545705971825283219)
                      ·
                        rfl

theorem cell23_5915369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_5915369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915369 prefixEnd_5915369 := by exact prefixLift 5915369
  have htrace : WordTrace (prefixWord ++ tailWord_5915369) baseStart_5915369 baseEnd_5915369 := by
    simpa [prefixWord, tailWord_5915369, baseEnd_5915369] using wordTrace_append hprefix tailTrace_5915369
  have hstable : (prefixWord ++ tailWord_5915369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915369).length < 2 ^ (prefixWord ++ tailWord_5915369).sum := by decide
  have hdescent : baseEnd_5915369 < baseStart_5915369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915372 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_5915372 : Nat := 118140960795 + 5915372 * 2 ^ 59
def prefixEnd_5915372 : Nat := 4983230072969 + 3 ^ 40 * 5915372 * 2
def baseEnd_5915372 : Nat := 3037429086147935313545705

theorem tailTrace_5915372 : CollatzResearch.WordTrace tailWord_5915372 prefixEnd_5915372 3037429086147935313545705 := by
  unfold tailWord_5915372
  simp only [CollatzResearch.WordTrace]
  refine ⟨107875670762812491975698185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143834227683749989300930913 107875670762812491975698185)
  ·
    refine ⟨80906753072109368981773639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107875670762812491975698185 80906753072109368981773639)
    ·
      refine ⟨121360129608164053472660459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80906753072109368981773639 121360129608164053472660459)
      ·
        refine ⟨182040194412246080208990689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121360129608164053472660459 182040194412246080208990689)
        ·
          refine ⟨136530145809184560156743017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182040194412246080208990689 136530145809184560156743017)
          ·
            refine ⟨102397609356888420117557263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136530145809184560156743017 102397609356888420117557263)
            ·
              refine ⟨153596414035332630176335895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102397609356888420117557263 153596414035332630176335895)
              ·
                refine ⟨230394621052998945264503843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153596414035332630176335895 230394621052998945264503843)
                ·
                  refine ⟨345591931579498417896755765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230394621052998945264503843 345591931579498417896755765)
                  ·
                    refine ⟨32399243585577976677820853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 345591931579498417896755765 32399243585577976677820853)
                    ·
                      refine ⟨3037429086147935313545705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32399243585577976677820853 3037429086147935313545705)
                      ·
                        rfl

theorem cell23_5915372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_5915372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915372 prefixEnd_5915372 := by exact prefixLift 5915372
  have htrace : WordTrace (prefixWord ++ tailWord_5915372) baseStart_5915372 baseEnd_5915372 := by
    simpa [prefixWord, tailWord_5915372, baseEnd_5915372] using wordTrace_append hprefix tailTrace_5915372
  have hstable : (prefixWord ++ tailWord_5915372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915372).length < 2 ^ (prefixWord ++ tailWord_5915372).sum := by decide
  have hdescent : baseEnd_5915372 < baseStart_5915372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915379 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 3, 4]
def baseStart_5915379 : Nat := 118140960795 + 5915379 * 2 ^ 59
def prefixEnd_5915379 : Nat := 4983230072969 + 3 ^ 40 * 5915379 * 2
def baseEnd_5915379 : Nat := 1012477560170838928719391

theorem tailTrace_5915379 : CollatzResearch.WordTrace tailWord_5915379 prefixEnd_5915379 1012477560170838928719391 := by
  unfold tailWord_5915379
  simp only [CollatzResearch.WordTrace]
  refine ⟨215751596836599624146901191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143834397891066416097934127 215751596836599624146901191)
  ·
    refine ⟨323627395254899436220351787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215751596836599624146901191 323627395254899436220351787)
    ·
      refine ⟨485441092882349154330527681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323627395254899436220351787 485441092882349154330527681)
      ·
        refine ⟨364080819661761865747895761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485441092882349154330527681 364080819661761865747895761)
        ·
          refine ⟨273060614746321399310921821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364080819661761865747895761 273060614746321399310921821)
          ·
            refine ⟨102397730529870524741595683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273060614746321399310921821 102397730529870524741595683)
            ·
              refine ⟨153596595794805787112393525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102397730529870524741595683 153596595794805787112393525)
              ·
                refine ⟨14399680855763042541786893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 153596595794805787112393525 14399680855763042541786893)
                ·
                  refine ⟨5399880320911140953170085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14399680855763042541786893 5399880320911140953170085)
                  ·
                    refine ⟨1012477560170838928719391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399880320911140953170085 1012477560170838928719391)
                    ·
                      rfl

theorem cell23_5915379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 4].length) (baseStart_5915379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915379 prefixEnd_5915379 := by exact prefixLift 5915379
  have htrace : WordTrace (prefixWord ++ tailWord_5915379) baseStart_5915379 baseEnd_5915379 := by
    simpa [prefixWord, tailWord_5915379, baseEnd_5915379] using wordTrace_append hprefix tailTrace_5915379
  have hstable : (prefixWord ++ tailWord_5915379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915379).length < 2 ^ (prefixWord ++ tailWord_5915379).sum := by decide
  have hdescent : baseEnd_5915379 < baseStart_5915379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915380 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5915380 : Nat := 118140960795 + 5915380 * 2 ^ 59
def prefixEnd_5915380 : Nat := 4983230072969 + 3 ^ 40 * 5915380 * 2
def baseEnd_5915380 : Nat := 3037433193993171282245669

theorem tailTrace_5915380 : CollatzResearch.WordTrace tailWord_5915380 prefixEnd_5915380 3037433193993171282245669 := by
  unfold tailWord_5915380
  simp only [CollatzResearch.WordTrace]
  refine ⟨107875816654798000658843797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143834422206397334211791729 107875816654798000658843797)
  ·
    refine ⟨5056678905693656280883303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107875816654798000658843797 5056678905693656280883303)
    ·
      refine ⟨7585018358540484421324955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5056678905693656280883303 7585018358540484421324955)
      ·
        refine ⟨11377527537810726631987433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585018358540484421324955 11377527537810726631987433)
        ·
          refine ⟨8533145653358044973990575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11377527537810726631987433 8533145653358044973990575)
          ·
            refine ⟨12799718480037067460985863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8533145653358044973990575 12799718480037067460985863)
            ·
              refine ⟨19199577720055601191478795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12799718480037067460985863 19199577720055601191478795)
              ·
                refine ⟨28799366580083401787218193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19199577720055601191478795 28799366580083401787218193)
                ·
                  refine ⟨21599524935062551340413645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28799366580083401787218193 21599524935062551340413645)
                  ·
                    refine ⟨8099821850648456752655117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21599524935062551340413645 8099821850648456752655117)
                    ·
                      refine ⟨3037433193993171282245669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8099821850648456752655117 3037433193993171282245669)
                      ·
                        rfl

theorem cell23_5915380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5915380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915380 prefixEnd_5915380 := by exact prefixLift 5915380
  have htrace : WordTrace (prefixWord ++ tailWord_5915380) baseStart_5915380 baseEnd_5915380 := by
    simpa [prefixWord, tailWord_5915380, baseEnd_5915380] using wordTrace_append hprefix tailTrace_5915380
  have hstable : (prefixWord ++ tailWord_5915380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915380).length < 2 ^ (prefixWord ++ tailWord_5915380).sum := by decide
  have hdescent : baseEnd_5915380 < baseStart_5915380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915389 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_5915389 : Nat := 118140960795 + 5915389 * 2 ^ 59
def prefixEnd_5915389 : Nat := 4983230072969 + 3 ^ 40 * 5915389 * 2
def baseEnd_5915389 : Nat := 3037437815319061747033127

theorem tailTrace_5915389 : CollatzResearch.WordTrace tailWord_5915389 prefixEnd_5915389 3037437815319061747033127 := by
  unfold tailWord_5915389
  simp only [CollatzResearch.WordTrace]
  refine ⟨215751961566563395854765221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143834641044375597236510147 215751961566563395854765221)
  ·
    refine ⟨40453492793730636722768479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215751961566563395854765221 40453492793730636722768479)
    ·
      refine ⟨60680239190595955084152719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40453492793730636722768479 60680239190595955084152719)
      ·
        refine ⟨91020358785893932626229079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60680239190595955084152719 91020358785893932626229079)
        ·
          refine ⟨136530538178840898939343619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91020358785893932626229079 136530538178840898939343619)
          ·
            refine ⟨204795807268261348409015429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136530538178840898939343619 204795807268261348409015429)
            ·
              refine ⟨38399213862799002826690393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204795807268261348409015429 38399213862799002826690393)
              ·
                refine ⟨28799410397099252120017795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38399213862799002826690393 28799410397099252120017795)
                ·
                  refine ⟨43199115595648878180026693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28799410397099252120017795 43199115595648878180026693)
                  ·
                    refine ⟨8099834174184164658755005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43199115595648878180026693 8099834174184164658755005)
                    ·
                      refine ⟨3037437815319061747033127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8099834174184164658755005 3037437815319061747033127)
                      ·
                        rfl

theorem cell23_5915389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_5915389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915389 prefixEnd_5915389 := by exact prefixLift 5915389
  have htrace : WordTrace (prefixWord ++ tailWord_5915389) baseStart_5915389 baseEnd_5915389 := by
    simpa [prefixWord, tailWord_5915389, baseEnd_5915389] using wordTrace_append hprefix tailTrace_5915389
  have hstable : (prefixWord ++ tailWord_5915389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915389).length < 2 ^ (prefixWord ++ tailWord_5915389).sum := by decide
  have hdescent : baseEnd_5915389 < baseStart_5915389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915396 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5915396 : Nat := 118140960795 + 5915396 * 2 ^ 59
def prefixEnd_5915396 : Nat := 4983230072969 + 3 ^ 40 * 5915396 * 2
def baseEnd_5915396 : Nat := 1012480469894547739881865

theorem tailTrace_5915396 : CollatzResearch.WordTrace tailWord_5915396 prefixEnd_5915396 1012480469894547739881865 := by
  unfold tailWord_5915396
  simp only [CollatzResearch.WordTrace]
  refine ⟨107876108438769018025135021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143834811251692024033513361 107876108438769018025135021)
  ·
    refine ⟨40453540664538381759425633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107876108438769018025135021 40453540664538381759425633)
    ·
      refine ⟨30340155498403786319569225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40453540664538381759425633 30340155498403786319569225)
      ·
        refine ⟨22755116623802839739676919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30340155498403786319569225 22755116623802839739676919)
        ·
          refine ⟨34132674935704259609515379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22755116623802839739676919 34132674935704259609515379)
          ·
            refine ⟨51199012403556389414273069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34132674935704259609515379 51199012403556389414273069)
            ·
              refine ⟨19199629651333646030352401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51199012403556389414273069 19199629651333646030352401)
              ·
                refine ⟨14399722238500234522764301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19199629651333646030352401 14399722238500234522764301)
                ·
                  refine ⟨5399895839437587946036613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14399722238500234522764301 5399895839437587946036613)
                  ·
                    refine ⟨1012480469894547739881865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399895839437587946036613 1012480469894547739881865)
                    ·
                      rfl

theorem cell23_5915396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5915396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915396 prefixEnd_5915396 := by exact prefixLift 5915396
  have htrace : WordTrace (prefixWord ++ tailWord_5915396) baseStart_5915396 baseEnd_5915396 := by
    simpa [prefixWord, tailWord_5915396, baseEnd_5915396] using wordTrace_append hprefix tailTrace_5915396
  have hstable : (prefixWord ++ tailWord_5915396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915396).length < 2 ^ (prefixWord ++ tailWord_5915396).sum := by decide
  have hdescent : baseEnd_5915396 < baseStart_5915396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915413 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_5915413 : Nat := 118140960795 + 5915413 * 2 ^ 59
def prefixEnd_5915413 : Nat := 4983230072969 + 3 ^ 40 * 5915413 * 2
def baseEnd_5915413 : Nat := 1012483379618256551044339

theorem tailTrace_5915413 : CollatzResearch.WordTrace tailWord_5915413 prefixEnd_5915413 1012483379618256551044339 := by
  unfold tailWord_5915413
  simp only [CollatzResearch.WordTrace]
  refine ⟨215752836918476447953638893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143835224612317631969092595 215752836918476447953638893)
  ·
    refine ⟨80907313844428667982614585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215752836918476447953638893 80907313844428667982614585)
    ·
      refine ⟨60680485383321500986960939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80907313844428667982614585 60680485383321500986960939)
      ·
        refine ⟨91020728074982251480441409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60680485383321500986960939 91020728074982251480441409)
        ·
          refine ⟨68265546056236688610331057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91020728074982251480441409 68265546056236688610331057)
          ·
            refine ⟨51199159542177516457748293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68265546056236688610331057 51199159542177516457748293)
            ·
              refine ⟨9599842414158284335827805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51199159542177516457748293 9599842414158284335827805)
              ·
                refine ⟨3599940905309356625935427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9599842414158284335827805 3599940905309356625935427)
                ·
                  refine ⟨5399911357964034938903141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599940905309356625935427 5399911357964034938903141)
                  ·
                    refine ⟨1012483379618256551044339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5399911357964034938903141 1012483379618256551044339)
                    ·
                      rfl

theorem cell23_5915413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_5915413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915413 prefixEnd_5915413 := by exact prefixLift 5915413
  have htrace : WordTrace (prefixWord ++ tailWord_5915413) baseStart_5915413 baseEnd_5915413 := by
    simpa [prefixWord, tailWord_5915413, baseEnd_5915413] using wordTrace_append hprefix tailTrace_5915413
  have hstable : (prefixWord ++ tailWord_5915413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915413).length < 2 ^ (prefixWord ++ tailWord_5915413).sum := by decide
  have hdescent : baseEnd_5915413 < baseStart_5915413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915426 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_5915426 : Nat := 118140960795 + 5915426 * 2 ^ 59
def prefixEnd_5915426 : Nat := 4983230072969 + 3 ^ 40 * 5915426 * 2
def baseEnd_5915426 : Nat := 337495201567030900252273

theorem tailTrace_5915426 : CollatzResearch.WordTrace tailWord_5915426 prefixEnd_5915426 337495201567030900252273 := by
  unfold tailWord_5915426
  simp only [CollatzResearch.WordTrace]
  refine ⟨53938327766857337793465533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143835540711619567449241421 53938327766857337793465533)
  ·
    refine ⟨20226872912571501672549575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53938327766857337793465533 20226872912571501672549575)
    ·
      refine ⟨30340309368857252508824363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20226872912571501672549575 30340309368857252508824363)
      ·
        refine ⟨45510464053285878763236545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30340309368857252508824363 45510464053285878763236545)
        ·
          refine ⟨34132848039964409072427409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45510464053285878763236545 34132848039964409072427409)
          ·
            refine ⟨25599636029973306804320557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34132848039964409072427409 25599636029973306804320557)
            ·
              refine ⟨9599863511239990051620209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25599636029973306804320557 9599863511239990051620209)
              ·
                refine ⟨7199897633429992538715157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599863511239990051620209 7199897633429992538715157)
                ·
                  refine ⟨337495201567030900252273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7199897633429992538715157 337495201567030900252273)
                  ·
                    rfl

theorem cell23_5915426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_5915426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915426 prefixEnd_5915426 := by exact prefixLift 5915426
  have htrace : WordTrace (prefixWord ++ tailWord_5915426) baseStart_5915426 baseEnd_5915426 := by
    simpa [prefixWord, tailWord_5915426, baseEnd_5915426] using wordTrace_append hprefix tailTrace_5915426
  have hstable : (prefixWord ++ tailWord_5915426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915426).length < 2 ^ (prefixWord ++ tailWord_5915426).sum := by decide
  have hdescent : baseEnd_5915426 < baseStart_5915426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915489 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5915489 : Nat := 118140960795 + 5915489 * 2 ^ 59
def prefixEnd_5915489 : Nat := 4983230072969 + 3 ^ 40 * 5915489 * 2
def baseEnd_5915489 : Nat := 3037489163384511355782667

theorem tailTrace_5915489 : CollatzResearch.WordTrace tailWord_5915489 prefixEnd_5915489 3037489163384511355782667 := by
  unfold tailWord_5915489
  simp only [CollatzResearch.WordTrace]
  refine ⟨215755608866201112933405521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143837072577467408622270347 215755608866201112933405521)
  ·
    refine ⟨161816706649650834700054141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215755608866201112933405521 161816706649650834700054141)
    ·
      refine ⟨60681264993619063012520303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161816706649650834700054141 60681264993619063012520303)
      ·
        refine ⟨91021897490428594518780455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60681264993619063012520303 91021897490428594518780455)
        ·
          refine ⟨136532846235642891778170683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91021897490428594518780455 136532846235642891778170683)
          ·
            refine ⟨204799269353464337667256025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136532846235642891778170683 204799269353464337667256025)
            ·
              refine ⟨153599452015098253250442019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204799269353464337667256025 153599452015098253250442019)
              ·
                refine ⟨230399178022647379875663029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153599452015098253250442019 230399178022647379875663029)
                ·
                  refine ⟨21599922939623191863343409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230399178022647379875663029 21599922939623191863343409)
                  ·
                    refine ⟨16199942204717393897507557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21599922939623191863343409 16199942204717393897507557)
                    ·
                      refine ⟨3037489163384511355782667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16199942204717393897507557 3037489163384511355782667)
                      ·
                        rfl

theorem cell23_5915489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5915489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915489 prefixEnd_5915489 := by exact prefixLift 5915489
  have htrace : WordTrace (prefixWord ++ tailWord_5915489) baseStart_5915489 baseEnd_5915489 := by
    simpa [prefixWord, tailWord_5915489, baseEnd_5915489] using wordTrace_append hprefix tailTrace_5915489
  have hstable : (prefixWord ++ tailWord_5915489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915489).length < 2 ^ (prefixWord ++ tailWord_5915489).sum := by decide
  have hdescent : baseEnd_5915489 < baseStart_5915489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915496 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5915496 : Nat := 118140960795 + 5915496 * 2 ^ 59
def prefixEnd_5915496 : Nat := 4983230072969 + 3 ^ 40 * 5915496 * 2
def baseEnd_5915496 : Nat := 3037492757749092828395135

theorem tailTrace_5915496 : CollatzResearch.WordTrace tailWord_5915496 prefixEnd_5915496 3037492757749092828395135 := by
  unfold tailWord_5915496
  simp only [CollatzResearch.WordTrace]
  refine ⟨107877932088587876564455171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143837242784783835419273561 107877932088587876564455171)
  ·
    refine ⟨161816898132881814846682757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107877932088587876564455171 161816898132881814846682757)
    ·
      refine ⟨30340668399915340283753017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161816898132881814846682757 30340668399915340283753017)
      ·
        refine ⟨22755501299936505212814763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30340668399915340283753017 22755501299936505212814763)
        ·
          refine ⟨34133251949904757819222145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22755501299936505212814763 34133251949904757819222145)
          ·
            refine ⟨25599938962428568364416609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34133251949904757819222145 25599938962428568364416609)
            ·
              refine ⟨19199954221821426273312457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25599938962428568364416609 19199954221821426273312457)
              ·
                refine ⟨14399965666366069704984343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19199954221821426273312457 14399965666366069704984343)
                ·
                  refine ⟨21599948499549104557476515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14399965666366069704984343 21599948499549104557476515)
                  ·
                    refine ⟨32399922749323656836214773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21599948499549104557476515 32399922749323656836214773)
                    ·
                      refine ⟨3037492757749092828395135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32399922749323656836214773 3037492757749092828395135)
                      ·
                        rfl

theorem cell23_5915496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5915496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915496 prefixEnd_5915496 := by exact prefixLift 5915496
  have htrace : WordTrace (prefixWord ++ tailWord_5915496) baseStart_5915496 baseEnd_5915496 := by
    simpa [prefixWord, tailWord_5915496, baseEnd_5915496] using wordTrace_append hprefix tailTrace_5915496
  have hstable : (prefixWord ++ tailWord_5915496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915496).length < 2 ^ (prefixWord ++ tailWord_5915496).sum := by decide
  have hdescent : baseEnd_5915496 < baseStart_5915496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915510 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5915510 : Nat := 118140960795 + 5915510 * 2 ^ 59
def prefixEnd_5915510 : Nat := 4983230072969 + 3 ^ 40 * 5915510 * 2
def baseEnd_5915510 : Nat := 3037499946478255773620071

theorem tailTrace_5915510 : CollatzResearch.WordTrace tailWord_5915510 prefixEnd_5915510 3037499946478255773620071 := by
  unfold tailWord_5915510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13484773424945314594994999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143837583199416689013279989 13484773424945314594994999)
  ·
    refine ⟨20227160137417971892492499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13484773424945314594994999 20227160137417971892492499)
    ·
      refine ⟨30340740206126957838738749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20227160137417971892492499 30340740206126957838738749)
      ·
        refine ⟨11377777577297609189527031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30340740206126957838738749 11377777577297609189527031)
        ·
          refine ⟨17066666365946413784290547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377777577297609189527031 17066666365946413784290547)
          ·
            refine ⟨25599999548919620676435821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17066666365946413784290547 25599999548919620676435821)
            ·
              refine ⟨9599999830844857753663433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25599999548919620676435821 9599999830844857753663433)
              ·
                refine ⟨7199999873133643315247575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599999830844857753663433 7199999873133643315247575)
                ·
                  refine ⟨10799999809700464972871363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199999873133643315247575 10799999809700464972871363)
                  ·
                    refine ⟨16199999714550697459307045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10799999809700464972871363 16199999714550697459307045)
                    ·
                      refine ⟨3037499946478255773620071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16199999714550697459307045 3037499946478255773620071)
                      ·
                        rfl

theorem cell23_5915510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5915510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915510 prefixEnd_5915510 := by exact prefixLift 5915510
  have htrace : WordTrace (prefixWord ++ tailWord_5915510) baseStart_5915510 baseEnd_5915510 := by
    simpa [prefixWord, tailWord_5915510, baseEnd_5915510] using wordTrace_append hprefix tailTrace_5915510
  have hstable : (prefixWord ++ tailWord_5915510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915510).length < 2 ^ (prefixWord ++ tailWord_5915510).sum := by decide
  have hdescent : baseEnd_5915510 < baseStart_5915510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915513 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_5915513 : Nat := 118140960795 + 5915513 * 2 ^ 59
def prefixEnd_5915513 : Nat := 4983230072969 + 3 ^ 40 * 5915513 * 2
def baseEnd_5915513 : Nat := 3037501486920219261882557

theorem tailTrace_5915513 : CollatzResearch.WordTrace tailWord_5915513 prefixEnd_5915513 3037501486920219261882557 := by
  unfold tailWord_5915513
  simp only [CollatzResearch.WordTrace]
  refine ⟨215756484218114165032279193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143837656145409443354852795 215756484218114165032279193)
  ·
    refine ⟨161817363163585623774209395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215756484218114165032279193 161817363163585623774209395)
    ·
      refine ⟨242726044745378435661314093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161817363163585623774209395 242726044745378435661314093)
      ·
        refine ⟨91022266779516913372992785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242726044745378435661314093 91022266779516913372992785)
        ·
          refine ⟨68266700084637685029744589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91022266779516913372992785 68266700084637685029744589)
          ·
            refine ⟨25600012531739131886154221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68266700084637685029744589 25600012531739131886154221)
            ·
              refine ⟨9600004699402174457307833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25600012531739131886154221 9600004699402174457307833)
              ·
                refine ⟨7200003524551630842980875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9600004699402174457307833 7200003524551630842980875)
                ·
                  refine ⟨10800005286827446264471313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200003524551630842980875 10800005286827446264471313)
                  ·
                    refine ⟨8100003965120584698353485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10800005286827446264471313 8100003965120584698353485)
                    ·
                      refine ⟨3037501486920219261882557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8100003965120584698353485 3037501486920219261882557)
                      ·
                        rfl

theorem cell23_5915513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_5915513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915513 prefixEnd_5915513 := by exact prefixLift 5915513
  have htrace : WordTrace (prefixWord ++ tailWord_5915513) baseStart_5915513 baseEnd_5915513 := by
    simpa [prefixWord, tailWord_5915513, baseEnd_5915513] using wordTrace_append hprefix tailTrace_5915513
  have hstable : (prefixWord ++ tailWord_5915513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915513).length < 2 ^ (prefixWord ++ tailWord_5915513).sum := by decide
  have hdescent : baseEnd_5915513 < baseStart_5915513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915596 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_5915596 : Nat := 118140960795 + 5915596 * 2 ^ 59
def prefixEnd_5915596 : Nat := 4983230072969 + 3 ^ 40 * 5915596 * 2
def baseEnd_5915596 : Nat := 3037544105814542437144675

theorem tailTrace_5915596 : CollatzResearch.WordTrace tailWord_5915596 prefixEnd_5915596 3037544105814542437144675 := by
  unfold tailWord_5915596
  simp only [CollatzResearch.WordTrace]
  refine ⟨107879755738406735103775321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143839674317875646805033761 107879755738406735103775321)
  ·
    refine ⟨80909816803805051327831491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107879755738406735103775321 80909816803805051327831491)
    ·
      refine ⟨121364725205707576991747237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80909816803805051327831491 121364725205707576991747237)
      ·
        refine ⟨22755885976070170685952607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121364725205707576991747237 22755885976070170685952607)
        ·
          refine ⟨34133828964105256028928911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22755885976070170685952607 34133828964105256028928911)
          ·
            refine ⟨51200743446157884043393367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34133828964105256028928911 51200743446157884043393367)
            ·
              refine ⟨76801115169236826065090051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51200743446157884043393367 76801115169236826065090051)
              ·
                refine ⟨115201672753855239097635077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76801115169236826065090051 115201672753855239097635077)
                ·
                  refine ⟨21600313641347857330806577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115201672753855239097635077 21600313641347857330806577)
                  ·
                    refine ⟨16200235231010892998104933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21600313641347857330806577 16200235231010892998104933)
                    ·
                      refine ⟨3037544105814542437144675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16200235231010892998104933 3037544105814542437144675)
                      ·
                        rfl

theorem cell23_5915596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_5915596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915596 prefixEnd_5915596 := by exact prefixLift 5915596
  have htrace : WordTrace (prefixWord ++ tailWord_5915596) baseStart_5915596 baseEnd_5915596 := by
    simpa [prefixWord, tailWord_5915596, baseEnd_5915596] using wordTrace_append hprefix tailTrace_5915596
  have hstable : (prefixWord ++ tailWord_5915596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915596).length < 2 ^ (prefixWord ++ tailWord_5915596).sum := by decide
  have hdescent : baseEnd_5915596 < baseStart_5915596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915613 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5915613 : Nat := 118140960795 + 5915613 * 2 ^ 59
def prefixEnd_5915613 : Nat := 4983230072969 + 3 ^ 40 * 5915613 * 2
def baseEnd_5915613 : Nat := 3037552834985668870632097

theorem tailTrace_5915613 : CollatzResearch.WordTrace tailWord_5915613 prefixEnd_5915613 3037552834985668870632097 := by
  unfold tailWord_5915613
  simp only [CollatzResearch.WordTrace]
  refine ⟨215760131517751882110919493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143840087678501254740612995 215760131517751882110919493)
  ·
    refine ⟨40455024659578477895797405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 215760131517751882110919493 40455024659578477895797405)
    ·
      refine ⟨15170634247341929210924027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40455024659578477895797405 15170634247341929210924027)
      ·
        refine ⟨22755951371012893816386041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15170634247341929210924027 22755951371012893816386041)
        ·
          refine ⟨17066963528259670362289531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22755951371012893816386041 17066963528259670362289531)
          ·
            refine ⟨25600445292389505543434297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17066963528259670362289531 25600445292389505543434297)
            ·
              refine ⟨19200333969292129157575723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25600445292389505543434297 19200333969292129157575723)
              ·
                refine ⟨28800500953938193736363585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19200333969292129157575723 28800500953938193736363585)
                ·
                  refine ⟨21600375715453645302272689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28800500953938193736363585 21600375715453645302272689)
                  ·
                    refine ⟨16200281786590233976704517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21600375715453645302272689 16200281786590233976704517)
                    ·
                      refine ⟨3037552834985668870632097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16200281786590233976704517 3037552834985668870632097)
                      ·
                        rfl

theorem cell23_5915613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5915613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915613 prefixEnd_5915613 := by exact prefixLift 5915613
  have htrace : WordTrace (prefixWord ++ tailWord_5915613) baseStart_5915613 baseEnd_5915613 := by
    simpa [prefixWord, tailWord_5915613, baseEnd_5915613] using wordTrace_append hprefix tailTrace_5915613
  have hstable : (prefixWord ++ tailWord_5915613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915613).length < 2 ^ (prefixWord ++ tailWord_5915613).sum := by decide
  have hdescent : baseEnd_5915613 < baseStart_5915613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915673 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 2, 4, 2]
def baseStart_5915673 : Nat := 118140960795 + 5915673 * 2 ^ 59
def prefixEnd_5915673 : Nat := 4983230072969 + 3 ^ 40 * 5915673 * 2
def baseEnd_5915673 : Nat := 3037583643824938635881821

theorem tailTrace_5915673 : CollatzResearch.WordTrace tailWord_5915673 prefixEnd_5915673 3037583643824938635881821 := by
  unfold tailWord_5915673
  simp only [CollatzResearch.WordTrace]
  refine ⟨215762319897534512358103673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143841546598356341572069115 215762319897534512358103673)
  ·
    refine ⟨161821739923150884268577755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215762319897534512358103673 161821739923150884268577755)
    ·
      refine ⟨242732609884726326402866633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161821739923150884268577755 242732609884726326402866633)
      ·
        refine ⟨182049457413544744802149975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242732609884726326402866633 182049457413544744802149975)
        ·
          refine ⟨273074186120317117203224963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182049457413544744802149975 273074186120317117203224963)
          ·
            refine ⟨409611279180475675804837445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273074186120317117203224963 409611279180475675804837445)
            ·
              refine ⟨76802114846339189213407021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 409611279180475675804837445 76802114846339189213407021)
              ·
                refine ⟨28800793067377195955027633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76802114846339189213407021 28800793067377195955027633)
                ·
                  refine ⟨21600594800532896966270725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28800793067377195955027633 21600594800532896966270725)
                  ·
                    refine ⟨4050111525099918181175761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21600594800532896966270725 4050111525099918181175761)
                    ·
                      refine ⟨3037583643824938635881821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050111525099918181175761 3037583643824938635881821)
                      ·
                        rfl

theorem cell23_5915673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_5915673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915673 prefixEnd_5915673 := by exact prefixLift 5915673
  have htrace : WordTrace (prefixWord ++ tailWord_5915673) baseStart_5915673 baseEnd_5915673 := by
    simpa [prefixWord, tailWord_5915673, baseEnd_5915673] using wordTrace_append hprefix tailTrace_5915673
  have hstable : (prefixWord ++ tailWord_5915673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915673).length < 2 ^ (prefixWord ++ tailWord_5915673).sum := by decide
  have hdescent : baseEnd_5915673 < baseStart_5915673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915717 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_5915717 : Nat := 118140960795 + 5915717 * 2 ^ 59
def prefixEnd_5915717 : Nat := 4983230072969 + 3 ^ 40 * 5915717 * 2
def baseEnd_5915717 : Nat := 1012535412324578821243873

theorem tailTrace_5915717 : CollatzResearch.WordTrace tailWord_5915717 prefixEnd_5915717 1012535412324578821243873 := by
  unfold tailWord_5915717
  simp only [CollatzResearch.WordTrace]
  refine ⟨215763924709375107872705405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143842616472916738581803603 215763924709375107872705405)
  ·
    refine ⟨80911471766015665452264527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 215763924709375107872705405 80911471766015665452264527)
    ·
      refine ⟨121367207649023498178396791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80911471766015665452264527 121367207649023498178396791)
      ·
        refine ⟨182050811473535247267595187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121367207649023498178396791 182050811473535247267595187)
        ·
          refine ⟨273076217210302870901392781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182050811473535247267595187 273076217210302870901392781)
          ·
            refine ⟨102403581453863576588022293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273076217210302870901392781 102403581453863576588022293)
            ·
              refine ⟨4800167880649855152563545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102403581453863576588022293 4800167880649855152563545)
              ·
                refine ⟨3600125910487391364422659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800167880649855152563545 3600125910487391364422659)
                ·
                  refine ⟨5400188865731087046633989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600125910487391364422659 5400188865731087046633989)
                  ·
                    refine ⟨1012535412324578821243873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400188865731087046633989 1012535412324578821243873)
                    ·
                      rfl

theorem cell23_5915717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_5915717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915717 prefixEnd_5915717 := by exact prefixLift 5915717
  have htrace : WordTrace (prefixWord ++ tailWord_5915717) baseStart_5915717 baseEnd_5915717 := by
    simpa [prefixWord, tailWord_5915717, baseEnd_5915717] using wordTrace_append hprefix tailTrace_5915717
  have hstable : (prefixWord ++ tailWord_5915717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915717).length < 2 ^ (prefixWord ++ tailWord_5915717).sum := by decide
  have hdescent : baseEnd_5915717 < baseStart_5915717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915734 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5915734 : Nat := 118140960795 + 5915734 * 2 ^ 59
def prefixEnd_5915734 : Nat := 4983230072969 + 3 ^ 40 * 5915734 * 2
def baseEnd_5915734 : Nat := 1012538322048287632406347

theorem tailTrace_5915734 : CollatzResearch.WordTrace tailWord_5915734 prefixEnd_5915734 1012538322048287632406347 := by
  unfold tailWord_5915734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485284046894594986004641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 143843029833542346517382837 13485284046894594986004641)
  ·
    refine ⟨10113963035170946239503481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13485284046894594986004641 10113963035170946239503481)
    ·
      refine ⟨7585472276378209679627611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113963035170946239503481 7585472276378209679627611)
      ·
        refine ⟨11378208414567314519441417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585472276378209679627611 11378208414567314519441417)
        ·
          refine ⟨8533656310925485889581063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11378208414567314519441417 8533656310925485889581063)
          ·
            refine ⟨12800484466388228834371595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8533656310925485889581063 12800484466388228834371595)
            ·
              refine ⟨19200726699582343251557393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12800484466388228834371595 19200726699582343251557393)
              ·
                refine ⟨14400545024686757438668045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19200726699582343251557393 14400545024686757438668045)
                ·
                  refine ⟨5400204384257534039500517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14400545024686757438668045 5400204384257534039500517)
                  ·
                    refine ⟨1012538322048287632406347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400204384257534039500517 1012538322048287632406347)
                    ·
                      rfl

theorem cell23_5915734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5915734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915734 prefixEnd_5915734 := by exact prefixLift 5915734
  have htrace : WordTrace (prefixWord ++ tailWord_5915734) baseStart_5915734 baseEnd_5915734 := by
    simpa [prefixWord, tailWord_5915734, baseEnd_5915734] using wordTrace_append hprefix tailTrace_5915734
  have hstable : (prefixWord ++ tailWord_5915734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915734).length < 2 ^ (prefixWord ++ tailWord_5915734).sum := by decide
  have hdescent : baseEnd_5915734 < baseStart_5915734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915736 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_5915736 : Nat := 118140960795 + 5915736 * 2 ^ 59
def prefixEnd_5915736 : Nat := 4983230072969 + 3 ^ 40 * 5915736 * 2
def baseEnd_5915736 : Nat := 3037615993106171889394031

theorem tailTrace_5915736 : CollatzResearch.WordTrace tailWord_5915736 prefixEnd_5915736 3037615993106171889394031 := by
  unfold tailWord_5915736
  simp only [CollatzResearch.WordTrace]
  refine ⟨107882308848153137058823531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143843078464204182745098041 107882308848153137058823531)
  ·
    refine ⟨161823463272229705588235297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107882308848153137058823531 161823463272229705588235297)
    ·
      refine ⟨121367597454172279191176473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161823463272229705588235297 121367597454172279191176473)
      ·
        refine ⟨91025698090629209393382355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121367597454172279191176473 91025698090629209393382355)
        ·
          refine ⟨136538547135943814090073533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91025698090629209393382355 136538547135943814090073533)
          ·
            refine ⟨51201955175978930283777575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136538547135943814090073533 51201955175978930283777575)
            ·
              refine ⟨76802932763968395425666363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51201955175978930283777575 76802932763968395425666363)
              ·
                refine ⟨115204399145952593138499545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76802932763968395425666363 115204399145952593138499545)
                ·
                  refine ⟨86403299359464444853874659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115204399145952593138499545 86403299359464444853874659)
                  ·
                    refine ⟨129604949039196667280811989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86403299359464444853874659 129604949039196667280811989)
                    ·
                      refine ⟨3037615993106171889394031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129604949039196667280811989 3037615993106171889394031)
                      ·
                        rfl

theorem cell23_5915736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_5915736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915736 prefixEnd_5915736 := by exact prefixLift 5915736
  have htrace : WordTrace (prefixWord ++ tailWord_5915736) baseStart_5915736 baseEnd_5915736 := by
    simpa [prefixWord, tailWord_5915736, baseEnd_5915736] using wordTrace_append hprefix tailTrace_5915736
  have hstable : (prefixWord ++ tailWord_5915736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915736).length < 2 ^ (prefixWord ++ tailWord_5915736).sum := by decide
  have hdescent : baseEnd_5915736 < baseStart_5915736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915743 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 1, 5]
def baseStart_5915743 : Nat := 118140960795 + 5915743 * 2 ^ 59
def prefixEnd_5915743 : Nat := 4983230072969 + 3 ^ 40 * 5915743 * 2
def baseEnd_5915743 : Nat := 1012539862490251120668833

theorem tailTrace_5915743 : CollatzResearch.WordTrace tailWord_5915743 prefixEnd_5915743 1012539862490251120668833 := by
  unfold tailWord_5915743
  simp only [CollatzResearch.WordTrace]
  refine ⟨215764873007280914313151883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143843248671520609542101255 215764873007280914313151883)
  ·
    refine ⟨323647309510921371469727825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215764873007280914313151883 323647309510921371469727825)
    ·
      refine ⟨242735482133191028602295869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 323647309510921371469727825 242735482133191028602295869)
      ·
        refine ⟨91025805799946635725860951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242735482133191028602295869 91025805799946635725860951)
        ·
          refine ⟨136538708699919953588791427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91025805799946635725860951 136538708699919953588791427)
          ·
            refine ⟨204808063049879930383187141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136538708699919953588791427 204808063049879930383187141)
            ·
              refine ⟨38401511821852486946847589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204808063049879930383187141 38401511821852486946847589)
              ·
                refine ⟨7200283466597341302533923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38401511821852486946847589 7200283466597341302533923)
                ·
                  refine ⟨10800425199896011953800885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7200283466597341302533923 10800425199896011953800885)
                  ·
                    refine ⟨1012539862490251120668833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10800425199896011953800885 1012539862490251120668833)
                    ·
                      rfl

theorem cell23_5915743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_5915743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915743 prefixEnd_5915743 := by exact prefixLift 5915743
  have htrace : WordTrace (prefixWord ++ tailWord_5915743) baseStart_5915743 baseEnd_5915743 := by
    simpa [prefixWord, tailWord_5915743, baseEnd_5915743] using wordTrace_append hprefix tailTrace_5915743
  have hstable : (prefixWord ++ tailWord_5915743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915743).length < 2 ^ (prefixWord ++ tailWord_5915743).sum := by decide
  have hdescent : baseEnd_5915743 < baseStart_5915743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915763 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 8, 2]
def baseStart_5915763 : Nat := 118140960795 + 5915763 * 2 ^ 59
def prefixEnd_5915763 : Nat := 4983230072969 + 3 ^ 40 * 5915763 * 2
def baseEnd_5915763 : Nat := 3037629857083843283756407

theorem tailTrace_5915763 : CollatzResearch.WordTrace tailWord_5915763 prefixEnd_5915763 3037629857083843283756407 := by
  unfold tailWord_5915763
  simp only [CollatzResearch.WordTrace]
  refine ⟨215765602467208457728879943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143843734978138971819253295 215765602467208457728879943)
  ·
    refine ⟨323648403700812686593319915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215765602467208457728879943 323648403700812686593319915)
    ·
      refine ⟨485472605551219029889979873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323648403700812686593319915 485472605551219029889979873)
      ·
        refine ⟨364104454163414272417484905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485472605551219029889979873 364104454163414272417484905)
        ·
          refine ⟨273078340622560704313113679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364104454163414272417484905 273078340622560704313113679)
          ·
            refine ⟨409617510933841056469670519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273078340622560704313113679 409617510933841056469670519)
            ·
              refine ⟨614426266400761584704505779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409617510933841056469670519 614426266400761584704505779)
              ·
                refine ⟨921639399601142377056758669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614426266400761584704505779 921639399601142377056758669)
                ·
                  refine ⟨345614774850428391396284501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 921639399601142377056758669 345614774850428391396284501)
                  ·
                    refine ⟨4050173142778457711675209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 345614774850428391396284501 4050173142778457711675209)
                    ·
                      refine ⟨3037629857083843283756407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050173142778457711675209 3037629857083843283756407)
                      ·
                        rfl

theorem cell23_5915763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 8, 2].length) (baseStart_5915763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915763 prefixEnd_5915763 := by exact prefixLift 5915763
  have htrace : WordTrace (prefixWord ++ tailWord_5915763) baseStart_5915763 baseEnd_5915763 := by
    simpa [prefixWord, tailWord_5915763, baseEnd_5915763] using wordTrace_append hprefix tailTrace_5915763
  have hstable : (prefixWord ++ tailWord_5915763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915763).length < 2 ^ (prefixWord ++ tailWord_5915763).sum := by decide
  have hdescent : baseEnd_5915763 < baseStart_5915763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915790 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_5915790 : Nat := 118140960795 + 5915790 * 2 ^ 59
def prefixEnd_5915790 : Nat := 4983230072969 + 3 ^ 40 * 5915790 * 2
def baseEnd_5915790 : Nat := 1012547907020504892706261

theorem tailTrace_5915790 : CollatzResearch.WordTrace tailWord_5915790 prefixEnd_5915790 1012547907020504892706261 := by
  unfold tailWord_5915790
  simp only [CollatzResearch.WordTrace]
  refine ⟨26970823404763830167514103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 143844391492073760893408549 26970823404763830167514103)
  ·
    refine ⟨40456235107145745251271155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26970823404763830167514103 40456235107145745251271155)
    ·
      refine ⟨60684352660718617876906733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40456235107145745251271155 60684352660718617876906733)
      ·
        refine ⟨22756632247769481703840025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60684352660718617876906733 22756632247769481703840025)
        ·
          refine ⟨17067474185827111277880019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22756632247769481703840025 17067474185827111277880019)
          ·
            refine ⟨25601211278740666916820029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17067474185827111277880019 25601211278740666916820029)
            ·
              refine ⟨9600454229527750093807511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25601211278740666916820029 9600454229527750093807511)
              ·
                refine ⟨14400681344291625140711267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9600454229527750093807511 14400681344291625140711267)
                ·
                  refine ⟨21601022016437437711066901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14400681344291625140711267 21601022016437437711066901)
                  ·
                    refine ⟨1012547907020504892706261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21601022016437437711066901 1012547907020504892706261)
                    ·
                      rfl

theorem cell23_5915790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_5915790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915790 prefixEnd_5915790 := by exact prefixLift 5915790
  have htrace : WordTrace (prefixWord ++ tailWord_5915790) baseStart_5915790 baseEnd_5915790 := by
    simpa [prefixWord, tailWord_5915790, baseEnd_5915790] using wordTrace_append hprefix tailTrace_5915790
  have hstable : (prefixWord ++ tailWord_5915790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915790).length < 2 ^ (prefixWord ++ tailWord_5915790).sum := by decide
  have hdescent : baseEnd_5915790 < baseStart_5915790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915831 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 1, 2, 2]
def baseStart_5915831 : Nat := 118140960795 + 5915831 * 2 ^ 59
def prefixEnd_5915831 : Nat := 4983230072969 + 3 ^ 40 * 5915831 * 2
def baseEnd_5915831 : Nat := 3037664773768349017706095

theorem tailTrace_5915831 : CollatzResearch.WordTrace tailWord_5915831 prefixEnd_5915831 3037664773768349017706095 := by
  unfold tailWord_5915831
  simp only [CollatzResearch.WordTrace]
  refine ⟨215768082630962105342355347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143845388420641403561570231 215768082630962105342355347)
  ·
    refine ⟨323652123946443158013533021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215768082630962105342355347 323652123946443158013533021)
    ·
      refine ⟨121369546479916184255074883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323652123946443158013533021 121369546479916184255074883)
      ·
        refine ⟨182054319719874276382612325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121369546479916184255074883 182054319719874276382612325)
        ·
          refine ⟨34135184947476426821739811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182054319719874276382612325 34135184947476426821739811)
          ·
            refine ⟨51202777421214640232609717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34135184947476426821739811 51202777421214640232609717)
            ·
              refine ⟨4800260383238872521807161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51202777421214640232609717 4800260383238872521807161)
              ·
                refine ⟨3600195287429154391355371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800260383238872521807161 3600195287429154391355371)
                ·
                  refine ⟨5400292931143731587033057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600195287429154391355371 5400292931143731587033057)
                  ·
                    refine ⟨4050219698357798690274793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400292931143731587033057 4050219698357798690274793)
                    ·
                      refine ⟨3037664773768349017706095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050219698357798690274793 3037664773768349017706095)
                      ·
                        rfl

theorem cell23_5915831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_5915831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915831 prefixEnd_5915831 := by exact prefixLift 5915831
  have htrace : WordTrace (prefixWord ++ tailWord_5915831) baseStart_5915831 baseEnd_5915831 := by
    simpa [prefixWord, tailWord_5915831, baseEnd_5915831] using wordTrace_append hprefix tailTrace_5915831
  have hstable : (prefixWord ++ tailWord_5915831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915831).length < 2 ^ (prefixWord ++ tailWord_5915831).sum := by decide
  have hdescent : baseEnd_5915831 < baseStart_5915831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915841 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5915841 : Nat := 118140960795 + 5915841 * 2 ^ 59
def prefixEnd_5915841 : Nat := 4983230072969 + 3 ^ 40 * 5915841 * 2
def baseEnd_5915841 : Nat := 1012556636191631326193683

theorem tailTrace_5915841 : CollatzResearch.WordTrace tailWord_5915841 prefixEnd_5915841 1012556636191631326193683 := by
  unfold tailWord_5915841
  simp only [CollatzResearch.WordTrace]
  refine ⟨215768447360925877050219377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143845631573950584700146251 215768447360925877050219377)
  ·
    refine ⟨161826335520694407787664533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215768447360925877050219377 161826335520694407787664533)
    ·
      refine ⟨7585609477532550365046775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161826335520694407787664533 7585609477532550365046775)
      ·
        refine ⟨11378414216298825547570163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585609477532550365046775 11378414216298825547570163)
        ·
          refine ⟨17067621324448238321355245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378414216298825547570163 17067621324448238321355245)
          ·
            refine ⟨6400357996668089370508217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17067621324448238321355245 6400357996668089370508217)
            ·
              refine ⟨4800268497501067027881163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6400357996668089370508217 4800268497501067027881163)
              ·
                refine ⟨7200402746251600541821745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800268497501067027881163 7200402746251600541821745)
                ·
                  refine ⟨5400302059688700406366309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200402746251600541821745 5400302059688700406366309)
                  ·
                    refine ⟨1012556636191631326193683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5400302059688700406366309 1012556636191631326193683)
                    ·
                      rfl

theorem cell23_5915841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5915841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915841 prefixEnd_5915841 := by exact prefixLift 5915841
  have htrace : WordTrace (prefixWord ++ tailWord_5915841) baseStart_5915841 baseEnd_5915841 := by
    simpa [prefixWord, tailWord_5915841, baseEnd_5915841] using wordTrace_append hprefix tailTrace_5915841
  have hstable : (prefixWord ++ tailWord_5915841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915841).length < 2 ^ (prefixWord ++ tailWord_5915841).sum := by decide
  have hdescent : baseEnd_5915841 < baseStart_5915841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915927 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 5]
def baseStart_5915927 : Nat := 118140960795 + 5915927 * 2 ^ 59
def prefixEnd_5915927 : Nat := 4983230072969 + 3 ^ 40 * 5915927 * 2
def baseEnd_5915927 : Nat := 337523785323464515789517

theorem tailTrace_5915927 : CollatzResearch.WordTrace tailWord_5915927 prefixEnd_5915927 337523785323464515789517 := by
  unfold tailWord_5915927
  simp only [CollatzResearch.WordTrace]
  refine ⟨215771584038614313737850035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143847722692409542491900023 215771584038614313737850035)
  ·
    refine ⟨323657376057921470606775053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215771584038614313737850035 323657376057921470606775053)
    ·
      refine ⟨121371516021720551477540645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 323657376057921470606775053 121371516021720551477540645)
      ·
        refine ⟨22757159254072603402038871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121371516021720551477540645 22757159254072603402038871)
        ·
          refine ⟨34135738881108905103058307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22757159254072603402038871 34135738881108905103058307)
          ·
            refine ⟨51203608321663357654587461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34135738881108905103058307 51203608321663357654587461)
            ·
              refine ⟨9600676560311879560235149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51203608321663357654587461 9600676560311879560235149)
              ·
                refine ⟨3600253710116954835088181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9600676560311879560235149 3600253710116954835088181)
                ·
                  refine ⟨337523785323464515789517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600253710116954835088181 337523785323464515789517)
                  ·
                    rfl

theorem cell23_5915927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 5].length) (baseStart_5915927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915927 prefixEnd_5915927 := by exact prefixLift 5915927
  have htrace : WordTrace (prefixWord ++ tailWord_5915927) baseStart_5915927 baseEnd_5915927 := by
    simpa [prefixWord, tailWord_5915927, baseEnd_5915927] using wordTrace_append hprefix tailTrace_5915927
  have hstable : (prefixWord ++ tailWord_5915927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915927).length < 2 ^ (prefixWord ++ tailWord_5915927).sum := by decide
  have hdescent : baseEnd_5915927 < baseStart_5915927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915938 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 2, 2, 2]
def baseStart_5915938 : Nat := 118140960795 + 5915938 * 2 ^ 59
def prefixEnd_5915938 : Nat := 4983230072969 + 3 ^ 40 * 5915938 * 2
def baseEnd_5915938 : Nat := 3037719716198380099068103

theorem tailTrace_5915938 : CollatzResearch.WordTrace tailWord_5915938 prefixEnd_5915938 3037719716198380099068103 := by
  unfold tailWord_5915938
  simp only [CollatzResearch.WordTrace]
  refine ⟨53942996310393615654125117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 143847990161049641744333645 53942996310393615654125117)
  ·
    refine ⟨20228623616397605870296919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53942996310393615654125117 20228623616397605870296919)
    ·
      refine ⟨30342935424596408805445379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20228623616397605870296919 30342935424596408805445379)
      ·
        refine ⟨45514403136894613208168069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30342935424596408805445379 45514403136894613208168069)
        ·
          refine ⟨8533950588167739976531513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45514403136894613208168069 8533950588167739976531513)
          ·
            refine ⟨6400462941125804982398635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8533950588167739976531513 6400462941125804982398635)
            ·
              refine ⟨9600694411688707473597953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400462941125804982398635 9600694411688707473597953)
              ·
                refine ⟨7200520808766530605198465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9600694411688707473597953 7200520808766530605198465)
                ·
                  refine ⟨5400390606574897953898849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200520808766530605198465 5400390606574897953898849)
                  ·
                    refine ⟨4050292954931173465424137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400390606574897953898849 4050292954931173465424137)
                    ·
                      refine ⟨3037719716198380099068103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4050292954931173465424137 3037719716198380099068103)
                      ·
                        rfl

theorem cell23_5915938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_5915938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915938 prefixEnd_5915938 := by exact prefixLift 5915938
  have htrace : WordTrace (prefixWord ++ tailWord_5915938) baseStart_5915938 baseEnd_5915938 := by
    simpa [prefixWord, tailWord_5915938, baseEnd_5915938] using wordTrace_append hprefix tailTrace_5915938
  have hstable : (prefixWord ++ tailWord_5915938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915938).length < 2 ^ (prefixWord ++ tailWord_5915938).sum := by decide
  have hdescent : baseEnd_5915938 < baseStart_5915938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915940 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_5915940 : Nat := 118140960795 + 5915940 * 2 ^ 59
def prefixEnd_5915940 : Nat := 4983230072969 + 3 ^ 40 * 5915940 * 2
def baseEnd_5915940 : Nat := 1012573581053229697081031

theorem tailTrace_5915940 : CollatzResearch.WordTrace tailWord_5915940 prefixEnd_5915940 1012573581053229697081031 := by
  unfold tailWord_5915940
  simp only [CollatzResearch.WordTrace]
  refine ⟨107886029093783608479036637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 143848038791711477972048849 107886029093783608479036637)
  ·
    refine ⟨40457260910168853179638739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107886029093783608479036637 40457260910168853179638739)
    ·
      refine ⟨60685891365253279769458109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40457260910168853179638739 60685891365253279769458109)
      ·
        refine ⟨22757209261969979913546791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60685891365253279769458109 22757209261969979913546791)
        ·
          refine ⟨34135813892954969870320187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22757209261969979913546791 34135813892954969870320187)
          ·
            refine ⟨51203720839432454805480281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34135813892954969870320187 51203720839432454805480281)
            ·
              refine ⟨38402790629574341104110211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51203720839432454805480281 38402790629574341104110211)
              ·
                refine ⟨57604185944361511656165317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38402790629574341104110211 57604185944361511656165317)
                ·
                  refine ⟨10800784864567783435530997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57604185944361511656165317 10800784864567783435530997)
                  ·
                    refine ⟨1012573581053229697081031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10800784864567783435530997 1012573581053229697081031)
                    ·
                      rfl

theorem cell23_5915940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_5915940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915940 prefixEnd_5915940 := by exact prefixLift 5915940
  have htrace : WordTrace (prefixWord ++ tailWord_5915940) baseStart_5915940 baseEnd_5915940 := by
    simpa [prefixWord, tailWord_5915940, baseEnd_5915940] using wordTrace_append hprefix tailTrace_5915940
  have hstable : (prefixWord ++ tailWord_5915940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915940).length < 2 ^ (prefixWord ++ tailWord_5915940).sum := by decide
  have hdescent : baseEnd_5915940 < baseStart_5915940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5915963 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_5915963 : Nat := 118140960795 + 5915963 * 2 ^ 59
def prefixEnd_5915963 : Nat := 4983230072969 + 3 ^ 40 * 5915963 * 2
def baseEnd_5915963 : Nat := 3037732553214742501255487

theorem tailTrace_5915963 : CollatzResearch.WordTrace tailWord_5915963 prefixEnd_5915963 3037732553214742501255487 := by
  unfold tailWord_5915963
  simp only [CollatzResearch.WordTrace]
  refine ⟨215772897066483891886160543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 143848598044322594590773695 215772897066483891886160543)
  ·
    refine ⟨323659345599725837829240815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 215772897066483891886160543 323659345599725837829240815)
    ·
      refine ⟨485489018399588756743861223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323659345599725837829240815 485489018399588756743861223)
      ·
        refine ⟨728233527599383135115791835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 485489018399588756743861223 728233527599383135115791835)
        ·
          refine ⟨1092350291399074702673687753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728233527599383135115791835 1092350291399074702673687753)
          ·
            refine ⟨819262718549306027005265815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1092350291399074702673687753 819262718549306027005265815)
            ·
              refine ⟨1228894077823959040507898723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 819262718549306027005265815 1228894077823959040507898723)
              ·
                refine ⟨1843341116735938560761848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228894077823959040507898723 1843341116735938560761848085)
                ·
                  refine ⟨86406614846997120035711629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1843341116735938560761848085 86406614846997120035711629)
                  ·
                    refine ⟨32402480567623920013391861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 86406614846997120035711629 32402480567623920013391861)
                    ·
                      refine ⟨3037732553214742501255487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32402480567623920013391861 3037732553214742501255487)
                      ·
                        rfl

theorem cell23_5915963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_5915963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5915963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5915963 prefixEnd_5915963 := by exact prefixLift 5915963
  have htrace : WordTrace (prefixWord ++ tailWord_5915963) baseStart_5915963 baseEnd_5915963 := by
    simpa [prefixWord, tailWord_5915963, baseEnd_5915963] using wordTrace_append hprefix tailTrace_5915963
  have hstable : (prefixWord ++ tailWord_5915963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5915963).length < 2 ^ (prefixWord ++ tailWord_5915963).sum := by decide
  have hdescent : baseEnd_5915963 < baseStart_5915963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5915963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
