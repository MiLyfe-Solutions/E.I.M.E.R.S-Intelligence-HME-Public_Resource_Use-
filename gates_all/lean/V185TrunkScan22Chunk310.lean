import V185TrunkScan22Chunk309

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2766219 : List Nat := [1, 1, 1, 1, 4, 3, 3, 4, 1, 3]
def baseStart_2766219 : Nat := 118140960795 + 2766219 * 2 ^ 59
def prefixEnd_2766219 : Nat := 4983230072969 + 3 ^ 40 * 2766219 * 2
def baseEnd_2766219 : Nat := 946933295066411926093931

theorem tailTrace_2766219 : CollatzResearch.WordTrace tailWord_2766219 prefixEnd_2766219 946933295066411926093931 := by
  unfold tailWord_2766219
  simp only [CollatzResearch.WordTrace]
  refine ⟨100892295565468470438029711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67261530376978980292019807 100892295565468470438029711)
  ·
    refine ⟨151338443348202705657044567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100892295565468470438029711 151338443348202705657044567)
    ·
      refine ⟨227007665022304058485566851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151338443348202705657044567 227007665022304058485566851)
      ·
        refine ⟨340511497533456087728350277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227007665022304058485566851 340511497533456087728350277)
        ·
          refine ⟨63845905787523016449065677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340511497533456087728350277 63845905787523016449065677)
          ·
            refine ⟨23942214670321131168399629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63845905787523016449065677 23942214670321131168399629)
            ·
              refine ⟨8978330501370424188149861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23942214670321131168399629 8978330501370424188149861)
              ·
                refine ⟨1683436969006954535278099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8978330501370424188149861 1683436969006954535278099)
                ·
                  refine ⟨2525155453510431802917149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683436969006954535278099 2525155453510431802917149)
                  ·
                    refine ⟨946933295066411926093931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525155453510431802917149 946933295066411926093931)
                    ·
                      rfl

theorem cell22_2766219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 3].length) (baseStart_2766219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766219 prefixEnd_2766219 := by exact prefixLift 2766219
  have htrace : WordTrace (prefixWord ++ tailWord_2766219) baseStart_2766219 baseEnd_2766219 := by
    simpa [prefixWord, tailWord_2766219, baseEnd_2766219] using wordTrace_append hprefix tailTrace_2766219
  have hstable : (prefixWord ++ tailWord_2766219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766219).length < 2 ^ (prefixWord ++ tailWord_2766219).sum := by decide
  have hdescent : baseEnd_2766219 < baseStart_2766219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766236 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_2766236 : Nat := 118140960795 + 2766236 * 2 ^ 59
def prefixEnd_2766236 : Nat := 4983230072969 + 3 ^ 40 * 2766236 * 2
def baseEnd_2766236 : Nat := 946939114513829548418879

theorem tailTrace_2766236 : CollatzResearch.WordTrace tailWord_2766236 prefixEnd_2766236 946939114513829548418879 := by
  unfold tailWord_2766236
  simp only [CollatzResearch.WordTrace]
  refine ⟨50446457803203441170699281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67261943737604588227599041 50446457803203441170699281)
  ·
    refine ⟨37834843352402580878024461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50446457803203441170699281 37834843352402580878024461)
    ·
      refine ⟨14188066257150967829259173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37834843352402580878024461 14188066257150967829259173)
      ·
        refine ⟨2660262423215806467986095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14188066257150967829259173 2660262423215806467986095)
        ·
          refine ⟨3990393634823709701979143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660262423215806467986095 3990393634823709701979143)
          ·
            refine ⟨5985590452235564552968715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990393634823709701979143 5985590452235564552968715)
            ·
              refine ⟨8978385678353346829453073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985590452235564552968715 8978385678353346829453073)
              ·
                refine ⟨6733789258765010122089805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978385678353346829453073 6733789258765010122089805)
                ·
                  refine ⟨2525170972036878795783677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6733789258765010122089805 2525170972036878795783677)
                  ·
                    refine ⟨946939114513829548418879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525170972036878795783677 946939114513829548418879)
                    ·
                      rfl

theorem cell22_2766236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_2766236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766236 prefixEnd_2766236 := by exact prefixLift 2766236
  have htrace : WordTrace (prefixWord ++ tailWord_2766236) baseStart_2766236 baseEnd_2766236 := by
    simpa [prefixWord, tailWord_2766236, baseEnd_2766236] using wordTrace_append hprefix tailTrace_2766236
  have hstable : (prefixWord ++ tailWord_2766236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766236).length < 2 ^ (prefixWord ++ tailWord_2766236).sum := by decide
  have hdescent : baseEnd_2766236 < baseStart_2766236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766253 : List Nat := [1, 5, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2766253 : Nat := 118140960795 + 2766253 * 2 ^ 59
def prefixEnd_2766253 : Nat := 4983230072969 + 3 ^ 40 * 2766253 * 2
def baseEnd_2766253 : Nat := 946944933961247170743827

theorem tailTrace_2766253 : CollatzResearch.WordTrace tailWord_2766253 prefixEnd_2766253 946944933961247170743827 := by
  unfold tailWord_2766253
  simp only [CollatzResearch.WordTrace]
  refine ⟨100893535647345294244767413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67262357098230196163178275 100893535647345294244767413)
  ·
    refine ⟨9458768966938621335446945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100893535647345294244767413 9458768966938621335446945)
    ·
      refine ⟨7094076725203966001585209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9458768966938621335446945 7094076725203966001585209)
      ·
        refine ⟨5320557543902974501188907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7094076725203966001585209 5320557543902974501188907)
        ·
          refine ⟨7980836315854461751783361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320557543902974501188907 7980836315854461751783361)
          ·
            refine ⟨5985627236890846313837521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980836315854461751783361 5985627236890846313837521)
            ·
              refine ⟨4489220427668134735378141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5985627236890846313837521 4489220427668134735378141)
              ·
                refine ⟨1683457660375550525766803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4489220427668134735378141 1683457660375550525766803)
                ·
                  refine ⟨2525186490563325788650205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683457660375550525766803 2525186490563325788650205)
                  ·
                    refine ⟨946944933961247170743827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525186490563325788650205 946944933961247170743827)
                    ·
                      rfl

theorem cell22_2766253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2766253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766253 prefixEnd_2766253 := by exact prefixLift 2766253
  have htrace : WordTrace (prefixWord ++ tailWord_2766253) baseStart_2766253 baseEnd_2766253 := by
    simpa [prefixWord, tailWord_2766253, baseEnd_2766253] using wordTrace_append hprefix tailTrace_2766253
  have hstable : (prefixWord ++ tailWord_2766253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766253).length < 2 ^ (prefixWord ++ tailWord_2766253).sum := by decide
  have hdescent : baseEnd_2766253 < baseStart_2766253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766275 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 3, 5]
def baseStart_2766275 : Nat := 118140960795 + 2766275 * 2 ^ 59
def prefixEnd_2766275 : Nat := 4983230072969 + 3 ^ 40 * 2766275 * 2
def baseEnd_2766275 : Nat := 946952465010846446693759

theorem tailTrace_2766275 : CollatzResearch.WordTrace tailWord_2766275 prefixEnd_2766275 946952465010846446693759 := by
  unfold tailWord_2766275
  simp only [CollatzResearch.WordTrace]
  refine ⟨100894338053265592002068279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67262892035510394668045519 100894338053265592002068279)
  ·
    refine ⟨151341507079898388003102419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100894338053265592002068279 151341507079898388003102419)
    ·
      refine ⟨227012260619847582004653629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151341507079898388003102419 227012260619847582004653629)
      ·
        refine ⟨85129597732442843251745111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227012260619847582004653629 85129597732442843251745111)
        ·
          refine ⟨127694396598664264877617667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85129597732442843251745111 127694396598664264877617667)
          ·
            refine ⟨191541594897996397316426501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127694396598664264877617667 191541594897996397316426501)
            ·
              refine ⟨35914049043374324496829969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191541594897996397316426501 35914049043374324496829969)
              ·
                refine ⟨26935536782530743372622477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35914049043374324496829969 26935536782530743372622477)
                ·
                  refine ⟨10100826293449028764733429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26935536782530743372622477 10100826293449028764733429)
                  ·
                    refine ⟨946952465010846446693759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10100826293449028764733429 946952465010846446693759)
                    ·
                      rfl

theorem cell22_2766275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_2766275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766275 prefixEnd_2766275 := by exact prefixLift 2766275
  have htrace : WordTrace (prefixWord ++ tailWord_2766275) baseStart_2766275 baseEnd_2766275 := by
    simpa [prefixWord, tailWord_2766275, baseEnd_2766275] using wordTrace_append hprefix tailTrace_2766275
  have hstable : (prefixWord ++ tailWord_2766275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766275).length < 2 ^ (prefixWord ++ tailWord_2766275).sum := by decide
  have hdescent : baseEnd_2766275 < baseStart_2766275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766294 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2766294 : Nat := 118140960795 + 2766294 * 2 ^ 59
def prefixEnd_2766294 : Nat := 4983230072969 + 3 ^ 40 * 2766294 * 2
def baseEnd_2766294 : Nat := 315652989699712243489567

theorem tailTrace_2766294 : CollatzResearch.WordTrace tailWord_2766294 prefixEnd_2766294 315652989699712243489567 := by
  unfold tailWord_2766294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305939440012297390438121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67263354026797838831339957 6305939440012297390438121)
  ·
    refine ⟨4729454580009223042828591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6305939440012297390438121 4729454580009223042828591)
    ·
      refine ⟨7094181870013834564242887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4729454580009223042828591 7094181870013834564242887)
      ·
        refine ⟨10641272805020751846364331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7094181870013834564242887 10641272805020751846364331)
        ·
          refine ⟨15961909207531127769546497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641272805020751846364331 15961909207531127769546497)
          ·
            refine ⟨11971431905648345827159873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15961909207531127769546497 11971431905648345827159873)
            ·
              refine ⟨8978573929236259370369905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11971431905648345827159873 8978573929236259370369905)
              ·
                refine ⟨6733930446927194527777429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978573929236259370369905 6733930446927194527777429)
                ·
                  refine ⟨315652989699712243489567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6733930446927194527777429 315652989699712243489567)
                  ·
                    rfl

theorem cell22_2766294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2766294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766294 prefixEnd_2766294 := by exact prefixLift 2766294
  have htrace : WordTrace (prefixWord ++ tailWord_2766294) baseStart_2766294 baseEnd_2766294 := by
    simpa [prefixWord, tailWord_2766294, baseEnd_2766294] using wordTrace_append hprefix tailTrace_2766294
  have hstable : (prefixWord ++ tailWord_2766294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766294).length < 2 ^ (prefixWord ++ tailWord_2766294).sum := by decide
  have hdescent : baseEnd_2766294 < baseStart_2766294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766307 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 6]
def baseStart_2766307 : Nat := 118140960795 + 2766307 * 2 ^ 59
def prefixEnd_2766307 : Nat := 4983230072969 + 3 ^ 40 * 2766307 * 2
def baseEnd_2766307 : Nat := 946963419264809029893661

theorem tailTrace_2766307 : CollatzResearch.WordTrace tailWord_2766307 prefixEnd_2766307 946963419264809029893661 := by
  unfold tailWord_2766307
  simp only [CollatzResearch.WordTrace]
  refine ⟨100895505189149661467233175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67263670126099774311488783 100895505189149661467233175)
  ·
    refine ⟨151343257783724492200849763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100895505189149661467233175 151343257783724492200849763)
    ·
      refine ⟨227014886675586738301274645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151343257783724492200849763 227014886675586738301274645)
      ·
        refine ⟨10641322812918128357872249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 227014886675586738301274645 10641322812918128357872249)
        ·
          refine ⟨7980992109688596268404187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641322812918128357872249 7980992109688596268404187)
          ·
            refine ⟨11971488164532894402606281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980992109688596268404187 11971488164532894402606281)
            ·
              refine ⟨8978616123399670801954711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11971488164532894402606281 8978616123399670801954711)
              ·
                refine ⟨13467924185099506202932067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8978616123399670801954711 13467924185099506202932067)
                ·
                  refine ⟨20201886277649259304398101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13467924185099506202932067 20201886277649259304398101)
                  ·
                    refine ⟨946963419264809029893661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20201886277649259304398101 946963419264809029893661)
                    ·
                      rfl

theorem cell22_2766307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_2766307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766307 prefixEnd_2766307 := by exact prefixLift 2766307
  have htrace : WordTrace (prefixWord ++ tailWord_2766307) baseStart_2766307 baseEnd_2766307 := by
    simpa [prefixWord, tailWord_2766307, baseEnd_2766307] using wordTrace_append hprefix tailTrace_2766307
  have hstable : (prefixWord ++ tailWord_2766307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766307).length < 2 ^ (prefixWord ++ tailWord_2766307).sum := by decide
  have hdescent : baseEnd_2766307 < baseStart_2766307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766309 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_2766309 : Nat := 118140960795 + 2766309 * 2 ^ 59
def prefixEnd_2766309 : Nat := 4983230072969 + 3 ^ 40 * 2766309 * 2
def baseEnd_2766309 : Nat := 946964103905681691343655

theorem tailTrace_2766309 : CollatzResearch.WordTrace tailWord_2766309 prefixEnd_2766309 946964103905681691343655 := by
  unfold tailWord_2766309
  simp only [CollatzResearch.WordTrace]
  refine ⟨100895578135142415808805981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67263718756761610539203987 100895578135142415808805981)
  ·
    refine ⟨37835841800678405928302243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100895578135142415808805981 37835841800678405928302243)
    ·
      refine ⟨56753762701017608892453365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37835841800678405928302243 56753762701017608892453365)
      ·
        refine ⟨5320665253220400833667503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56753762701017608892453365 5320665253220400833667503)
        ·
          refine ⟨7980997879830601250501255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320665253220400833667503 7980997879830601250501255)
          ·
            refine ⟨11971496819745901875751883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980997879830601250501255 11971496819745901875751883)
            ·
              refine ⟨17957245229618852813627825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971496819745901875751883 17957245229618852813627825)
              ·
                refine ⟨13467933922214139610220869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17957245229618852813627825 13467933922214139610220869)
                ·
                  refine ⟨2525237610415151176916413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13467933922214139610220869 2525237610415151176916413)
                  ·
                    refine ⟨946964103905681691343655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525237610415151176916413 946964103905681691343655)
                    ·
                      rfl

theorem cell22_2766309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_2766309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766309 prefixEnd_2766309 := by exact prefixLift 2766309
  have htrace : WordTrace (prefixWord ++ tailWord_2766309) baseStart_2766309 baseEnd_2766309 := by
    simpa [prefixWord, tailWord_2766309, baseEnd_2766309] using wordTrace_append hprefix tailTrace_2766309
  have hstable : (prefixWord ++ tailWord_2766309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766309).length < 2 ^ (prefixWord ++ tailWord_2766309).sum := by decide
  have hdescent : baseEnd_2766309 < baseStart_2766309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766311 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 4]
def baseStart_2766311 : Nat := 118140960795 + 2766311 * 2 ^ 59
def prefixEnd_2766311 : Nat := 4983230072969 + 3 ^ 40 * 2766311 * 2
def baseEnd_2766311 : Nat := 315654929515518117597883

theorem tailTrace_2766311 : CollatzResearch.WordTrace tailWord_2766311 prefixEnd_2766311 315654929515518117597883 := by
  unfold tailWord_2766311
  simp only [CollatzResearch.WordTrace]
  refine ⟨100895651081135170150378787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67263767387423446766919191 100895651081135170150378787)
  ·
    refine ⟨151343476621702755225568181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100895651081135170150378787 151343476621702755225568181)
    ·
      refine ⟨14188450933284633302397017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151343476621702755225568181 14188450933284633302397017)
      ·
        refine ⟨10641338199963474976797763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14188450933284633302397017 10641338199963474976797763)
        ·
          refine ⟨15962007299945212465196645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10641338199963474976797763 15962007299945212465196645)
          ·
            refine ⟨2992876368739727337224371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15962007299945212465196645 2992876368739727337224371)
            ·
              refine ⟨4489314553109591005836557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992876368739727337224371 4489314553109591005836557)
              ·
                refine ⟨1683492957416096627188709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4489314553109591005836557 1683492957416096627188709)
                ·
                  refine ⟨315654929515518117597883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683492957416096627188709 315654929515518117597883)
                  ·
                    rfl

theorem cell22_2766311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 4].length) (baseStart_2766311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766311 prefixEnd_2766311 := by exact prefixLift 2766311
  have htrace : WordTrace (prefixWord ++ tailWord_2766311) baseStart_2766311 baseEnd_2766311 := by
    simpa [prefixWord, tailWord_2766311, baseEnd_2766311] using wordTrace_append hprefix tailTrace_2766311
  have hstable : (prefixWord ++ tailWord_2766311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766311).length < 2 ^ (prefixWord ++ tailWord_2766311).sum := by decide
  have hdescent : baseEnd_2766311 < baseStart_2766311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766322 : List Nat := [3, 2, 1, 4, 1, 1, 10]
def baseStart_2766322 : Nat := 118140960795 + 2766322 * 2 ^ 59
def prefixEnd_2766322 : Nat := 4983230072969 + 3 ^ 40 * 2766322 * 2
def baseEnd_2766322 : Nat := 35072909410050147806245

theorem tailTrace_2766322 : CollatzResearch.WordTrace tailWord_2766322 prefixEnd_2766322 35072909410050147806245 := by
  unfold tailWord_2766322
  simp only [CollatzResearch.WordTrace]
  refine ⟨25224013071023829757257305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67264034856063546019352813 25224013071023829757257305)
  ·
    refine ⟨18918009803267872317942979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25224013071023829757257305 18918009803267872317942979)
    ·
      refine ⟨28377014704901808476914469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18918009803267872317942979 28377014704901808476914469)
      ·
        refine ⟨5320690257169089089421463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28377014704901808476914469 5320690257169089089421463)
        ·
          refine ⟨7981035385753633634132195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320690257169089089421463 7981035385753633634132195)
          ·
            refine ⟨11971553078630450451198293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981035385753633634132195 11971553078630450451198293)
            ·
              refine ⟨35072909410050147806245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11971553078630450451198293 35072909410050147806245)
              ·
                rfl

theorem cell22_2766322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 10].length) (baseStart_2766322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766322 prefixEnd_2766322 := by exact prefixLift 2766322
  have htrace : WordTrace (prefixWord ++ tailWord_2766322) baseStart_2766322 baseEnd_2766322 := by
    simpa [prefixWord, tailWord_2766322, baseEnd_2766322] using wordTrace_append hprefix tailTrace_2766322
  have hstable : (prefixWord ++ tailWord_2766322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766322).length < 2 ^ (prefixWord ++ tailWord_2766322).sum := by decide
  have hdescent : baseEnd_2766322 < baseStart_2766322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766343 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 2, 3]
def baseStart_2766343 : Nat := 118140960795 + 2766343 * 2 ^ 59
def prefixEnd_2766343 : Nat := 4983230072969 + 3 ^ 40 * 2766343 * 2
def baseEnd_2766343 : Nat := 946975742800516935993551

theorem tailTrace_2766343 : CollatzResearch.WordTrace tailWord_2766343 prefixEnd_2766343 946975742800516935993551 := by
  unfold tailWord_2766343
  simp only [CollatzResearch.WordTrace]
  refine ⟨100896818217019239615543683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67264545478012826410362455 100896818217019239615543683)
  ·
    refine ⟨151345227325528859423315525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100896818217019239615543683 151345227325528859423315525)
    ·
      refine ⟨28377230123536661141871661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151345227325528859423315525 28377230123536661141871661)
      ·
        refine ⟨10641461296326247928201873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28377230123536661141871661 10641461296326247928201873)
        ·
          refine ⟨7981095972244685946151405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641461296326247928201873 7981095972244685946151405)
          ·
            refine ⟨2992910989591757229806777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7981095972244685946151405 2992910989591757229806777)
            ·
              refine ⟨2244683242193817922355083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2992910989591757229806777 2244683242193817922355083)
              ·
                refine ⟨3367024863290726883532625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244683242193817922355083 3367024863290726883532625)
                ·
                  refine ⟨2525268647468045162649469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367024863290726883532625 2525268647468045162649469)
                  ·
                    refine ⟨946975742800516935993551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525268647468045162649469 946975742800516935993551)
                    ·
                      rfl

theorem cell22_2766343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_2766343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766343 prefixEnd_2766343 := by exact prefixLift 2766343
  have htrace : WordTrace (prefixWord ++ tailWord_2766343) baseStart_2766343 baseEnd_2766343 := by
    simpa [prefixWord, tailWord_2766343, baseEnd_2766343] using wordTrace_append hprefix tailTrace_2766343
  have hstable : (prefixWord ++ tailWord_2766343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766343).length < 2 ^ (prefixWord ++ tailWord_2766343).sum := by decide
  have hdescent : baseEnd_2766343 < baseStart_2766343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766412 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_2766412 : Nat := 118140960795 + 2766412 * 2 ^ 59
def prefixEnd_2766412 : Nat := 4983230072969 + 3 ^ 40 * 2766412 * 2
def baseEnd_2766412 : Nat := 315666454303541252006113

theorem tailTrace_2766412 : CollatzResearch.WordTrace tailWord_2766412 prefixEnd_2766412 315666454303541252006113 := by
  unfold tailWord_2766412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50449667426884632199902745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67266223235846176266536993 50449667426884632199902745)
  ·
    refine ⟨37837250570163474149927059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50449667426884632199902745 37837250570163474149927059)
    ·
      refine ⟨56755875855245211224890589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37837250570163474149927059 56755875855245211224890589)
      ·
        refine ⟨21283453445716954209333971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56755875855245211224890589 21283453445716954209333971)
        ·
          refine ⟨31925180168575431314000957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21283453445716954209333971 31925180168575431314000957)
          ·
            refine ⟨11971942563215786742750359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31925180168575431314000957 11971942563215786742750359)
            ·
              refine ⟨17957913844823680114125539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11971942563215786742750359 17957913844823680114125539)
              ·
                refine ⟨26936870767235520171188309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17957913844823680114125539 26936870767235520171188309)
                ·
                  refine ⟨315666454303541252006113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26936870767235520171188309 315666454303541252006113)
                  ·
                    rfl

theorem cell22_2766412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_2766412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766412 prefixEnd_2766412 := by exact prefixLift 2766412
  have htrace : WordTrace (prefixWord ++ tailWord_2766412) baseStart_2766412 baseEnd_2766412 := by
    simpa [prefixWord, tailWord_2766412, baseEnd_2766412] using wordTrace_append hprefix tailTrace_2766412
  have hstable : (prefixWord ++ tailWord_2766412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766412).length < 2 ^ (prefixWord ++ tailWord_2766412).sum := by decide
  have hdescent : baseEnd_2766412 < baseStart_2766412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766414 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2766414 : Nat := 118140960795 + 2766414 * 2 ^ 59
def prefixEnd_2766414 : Nat := 4983230072969 + 3 ^ 40 * 2766414 * 2
def baseEnd_2766414 : Nat := 947000047551496417468333

theorem tailTrace_2766414 : CollatzResearch.WordTrace tailWord_2766414 prefixEnd_2766414 947000047551496417468333 := by
  unfold tailWord_2766414
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612425974970252342672287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67266271866508012494252197 12612425974970252342672287)
  ·
    refine ⟨18918638962455378514008431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12612425974970252342672287 18918638962455378514008431)
    ·
      refine ⟨28377958443683067771012647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18918638962455378514008431 28377958443683067771012647)
      ·
        refine ⟨42566937665524601656518971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28377958443683067771012647 42566937665524601656518971)
        ·
          refine ⟨63850406498286902484778457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42566937665524601656518971 63850406498286902484778457)
          ·
            refine ⟨47887804873715176863583843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63850406498286902484778457 47887804873715176863583843)
            ·
              refine ⟨71831707310572765295375765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47887804873715176863583843 71831707310572765295375765)
              ·
                refine ⟨3367111280183098373220739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71831707310572765295375765 3367111280183098373220739)
                ·
                  refine ⟨5050666920274647559831109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3367111280183098373220739 5050666920274647559831109)
                  ·
                    refine ⟨947000047551496417468333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5050666920274647559831109 947000047551496417468333)
                    ·
                      rfl

theorem cell22_2766414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2766414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766414 prefixEnd_2766414 := by exact prefixLift 2766414
  have htrace : WordTrace (prefixWord ++ tailWord_2766414) baseStart_2766414 baseEnd_2766414 := by
    simpa [prefixWord, tailWord_2766414, baseEnd_2766414] using wordTrace_append hprefix tailTrace_2766414
  have hstable : (prefixWord ++ tailWord_2766414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766414).length < 2 ^ (prefixWord ++ tailWord_2766414).sum := by decide
  have hdescent : baseEnd_2766414 < baseStart_2766414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766446 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_2766446 : Nat := 118140960795 + 2766446 * 2 ^ 59
def prefixEnd_2766446 : Nat := 4983230072969 + 3 ^ 40 * 2766446 * 2
def baseEnd_2766446 : Nat := 315670333935153000222745

theorem tailTrace_2766446 : CollatzResearch.WordTrace tailWord_2766446 prefixEnd_2766446 315670333935153000222745 := by
  unfold tailWord_2766446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612571866955761025817899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67267049957097392137695461 12612571866955761025817899)
  ·
    refine ⟨18918857800433641538726849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12612571866955761025817899 18918857800433641538726849)
    ·
      refine ⟨14189143350325231154045137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18918857800433641538726849 14189143350325231154045137)
      ·
        refine ⟨10641857512743923365533853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14189143350325231154045137 10641857512743923365533853)
        ·
          refine ⟨3990696567278971262075195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10641857512743923365533853 3990696567278971262075195)
          ·
            refine ⟨5986044850918456893112793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990696567278971262075195 5986044850918456893112793)
            ·
              refine ⟨4489533638188842669834595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5986044850918456893112793 4489533638188842669834595)
              ·
                refine ⟨6734300457283264004751893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489533638188842669834595 6734300457283264004751893)
                ·
                  refine ⟨315670333935153000222745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6734300457283264004751893 315670333935153000222745)
                  ·
                    rfl

theorem cell22_2766446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_2766446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766446 prefixEnd_2766446 := by exact prefixLift 2766446
  have htrace : WordTrace (prefixWord ++ tailWord_2766446) baseStart_2766446 baseEnd_2766446 := by
    simpa [prefixWord, tailWord_2766446, baseEnd_2766446] using wordTrace_append hprefix tailTrace_2766446
  have hstable : (prefixWord ++ tailWord_2766446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766446).length < 2 ^ (prefixWord ++ tailWord_2766446).sum := by decide
  have hdescent : baseEnd_2766446 < baseStart_2766446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766457 : List Nat := [1, 2, 1, 3, 3, 1, 2, 9]
def baseStart_2766457 : Nat := 118140960795 + 2766457 * 2 ^ 59
def prefixEnd_2766457 : Nat := 4983230072969 + 3 ^ 40 * 2766457 * 2
def baseEnd_2766457 : Nat := 105223863036695404293689

theorem tailTrace_2766457 : CollatzResearch.WordTrace tailWord_2766457 prefixEnd_2766457 105223863036695404293689 := by
  unfold tailWord_2766457
  simp only [CollatzResearch.WordTrace]
  refine ⟨100900976138606237085193625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67267317425737491390129083 100900976138606237085193625)
  ·
    refine ⟨75675732103954677813895219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100900976138606237085193625 75675732103954677813895219)
    ·
      refine ⟨113513598155932016720842829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75675732103954677813895219 113513598155932016720842829)
      ·
        refine ⟨42567599308474506270316061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113513598155932016720842829 42567599308474506270316061)
        ·
          refine ⟨15962849740677939851368523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42567599308474506270316061 15962849740677939851368523)
          ·
            refine ⟨23944274611016909777052785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15962849740677939851368523 23944274611016909777052785)
            ·
              refine ⟨17958205958262682332789589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23944274611016909777052785 17958205958262682332789589)
              ·
                refine ⟨105223863036695404293689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17958205958262682332789589 105223863036695404293689)
                ·
                  rfl

theorem cell22_2766457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 9].length) (baseStart_2766457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766457 prefixEnd_2766457 := by exact prefixLift 2766457
  have htrace : WordTrace (prefixWord ++ tailWord_2766457) baseStart_2766457 baseEnd_2766457 := by
    simpa [prefixWord, tailWord_2766457, baseEnd_2766457] using wordTrace_append hprefix tailTrace_2766457
  have hstable : (prefixWord ++ tailWord_2766457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766457).length < 2 ^ (prefixWord ++ tailWord_2766457).sum := by decide
  have hdescent : baseEnd_2766457 < baseStart_2766457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766461 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_2766461 : Nat := 118140960795 + 2766461 * 2 ^ 59
def prefixEnd_2766461 : Nat := 4983230072969 + 3 ^ 40 * 2766461 * 2
def baseEnd_2766461 : Nat := 947016136612003961543189

theorem tailTrace_2766461 : CollatzResearch.WordTrace tailWord_2766461 prefixEnd_2766461 947016136612003961543189 := by
  unfold tailWord_2766461
  simp only [CollatzResearch.WordTrace]
  refine ⟨100901122030591745768339237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67267414687061163845559491 100901122030591745768339237)
  ·
    refine ⟨18918960380735952331563607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100901122030591745768339237 18918960380735952331563607)
    ·
      refine ⟨28378440571103928497345411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18918960380735952331563607 28378440571103928497345411)
      ·
        refine ⟨42567660856655892746018117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28378440571103928497345411 42567660856655892746018117)
        ·
          refine ⟨7981436410622979889878397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42567660856655892746018117 7981436410622979889878397)
          ·
            refine ⟨2993038653983617458704399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7981436410622979889878397 2993038653983617458704399)
            ·
              refine ⟨4489557980975426188056599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993038653983617458704399 4489557980975426188056599)
              ·
                refine ⟨6734336971463139282084899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489557980975426188056599 6734336971463139282084899)
                ·
                  refine ⟨10101505457194708923127349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734336971463139282084899 10101505457194708923127349)
                  ·
                    refine ⟨947016136612003961543189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10101505457194708923127349 947016136612003961543189)
                    ·
                      rfl

theorem cell22_2766461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_2766461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766461 prefixEnd_2766461 := by exact prefixLift 2766461
  have htrace : WordTrace (prefixWord ++ tailWord_2766461) baseStart_2766461 baseEnd_2766461 := by
    simpa [prefixWord, tailWord_2766461, baseEnd_2766461] using wordTrace_append hprefix tailTrace_2766461
  have hstable : (prefixWord ++ tailWord_2766461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766461).length < 2 ^ (prefixWord ++ tailWord_2766461).sum := by decide
  have hdescent : baseEnd_2766461 < baseStart_2766461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766474 : List Nat := [3, 1, 2, 3, 2, 2, 1, 8]
def baseStart_2766474 : Nat := 118140960795 + 2766474 * 2 ^ 59
def prefixEnd_2766474 : Nat := 4983230072969 + 3 ^ 40 * 2766474 * 2
def baseEnd_2766474 : Nat := 105224509641964028996461

theorem tailTrace_2766474 : CollatzResearch.WordTrace tailWord_2766474 prefixEnd_2766474 105224509641964028996461 := by
  unfold tailWord_2766474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25225399044886162247140619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67267730786363099325708317 25225399044886162247140619)
  ·
    refine ⟨37838098567329243370710929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25225399044886162247140619 37838098567329243370710929)
    ·
      refine ⟨28378573925496932528033197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37838098567329243370710929 28378573925496932528033197)
      ·
        refine ⟨10641965222061349698012449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28378573925496932528033197 10641965222061349698012449)
        ·
          refine ⟨7981473916546012273509337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641965222061349698012449 7981473916546012273509337)
          ·
            refine ⟨5986105437409509205132003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7981473916546012273509337 5986105437409509205132003)
            ·
              refine ⟨8979158156114263807698005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986105437409509205132003 8979158156114263807698005)
              ·
                refine ⟨105224509641964028996461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8979158156114263807698005 105224509641964028996461)
                ·
                  rfl

theorem cell22_2766474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_2766474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766474 prefixEnd_2766474 := by exact prefixLift 2766474
  have htrace : WordTrace (prefixWord ++ tailWord_2766474) baseStart_2766474 baseEnd_2766474 := by
    simpa [prefixWord, tailWord_2766474, baseEnd_2766474] using wordTrace_append hprefix tailTrace_2766474
  have hstable : (prefixWord ++ tailWord_2766474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766474).length < 2 ^ (prefixWord ++ tailWord_2766474).sum := by decide
  have hdescent : baseEnd_2766474 < baseStart_2766474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766557 : List Nat := [1, 4, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_2766557 : Nat := 118140960795 + 2766557 * 2 ^ 59
def prefixEnd_2766557 : Nat := 4983230072969 + 3 ^ 40 * 2766557 * 2
def baseEnd_2766557 : Nat := 947048999373891711142895

theorem tailTrace_2766557 : CollatzResearch.WordTrace tailWord_2766557 prefixEnd_2766557 947048999373891711142895 := by
  unfold tailWord_2766557
  simp only [CollatzResearch.WordTrace]
  refine ⟨100904623438243954163833925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67269748958829302775889283 100904623438243954163833925)
  ·
    refine ⟨18919616894670741405718861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100904623438243954163833925 18919616894670741405718861)
    ·
      refine ⟨7094856335501528027144573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18919616894670741405718861 7094856335501528027144573)
      ·
        refine ⟨2660571125813073010179215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7094856335501528027144573 2660571125813073010179215)
        ·
          refine ⟨3990856688719609515268823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660571125813073010179215 3990856688719609515268823)
          ·
            refine ⟨5986285033079414272903235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990856688719609515268823 5986285033079414272903235)
            ·
              refine ⟨8979427549619121409354853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986285033079414272903235 8979427549619121409354853)
              ·
                refine ⟨1683642665553585264254035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8979427549619121409354853 1683642665553585264254035)
                ·
                  refine ⟨2525463998330377896381053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683642665553585264254035 2525463998330377896381053)
                  ·
                    refine ⟨947048999373891711142895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525463998330377896381053 947048999373891711142895)
                    ·
                      rfl

theorem cell22_2766557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_2766557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766557 prefixEnd_2766557 := by exact prefixLift 2766557
  have htrace : WordTrace (prefixWord ++ tailWord_2766557) baseStart_2766557 baseEnd_2766557 := by
    simpa [prefixWord, tailWord_2766557, baseEnd_2766557] using wordTrace_append hprefix tailTrace_2766557
  have hstable : (prefixWord ++ tailWord_2766557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766557).length < 2 ^ (prefixWord ++ tailWord_2766557).sum := by decide
  have hdescent : baseEnd_2766557 < baseStart_2766557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766564 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_2766564 : Nat := 118140960795 + 2766564 * 2 ^ 59
def prefixEnd_2766564 : Nat := 4983230072969 + 3 ^ 40 * 2766564 * 2
def baseEnd_2766564 : Nat := 315683798538982008739291

theorem tailTrace_2766564 : CollatzResearch.WordTrace tailWord_2766564 prefixEnd_2766564 315683798538982008739291 := by
  unfold tailWord_2766564
  simp only [CollatzResearch.WordTrace]
  refine ⟨50452439374609297179669373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67269919166145729572892497 50452439374609297179669373)
  ·
    refine ⟨18919664765478486442376015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50452439374609297179669373 18919664765478486442376015)
    ·
      refine ⟨28379497148217729663564023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18919664765478486442376015 28379497148217729663564023)
      ·
        refine ⟨42569245722326594495346035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28379497148217729663564023 42569245722326594495346035)
        ·
          refine ⟨63853868583489891743019053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42569245722326594495346035 63853868583489891743019053)
          ·
            refine ⟨23945200718808709403632145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63853868583489891743019053 23945200718808709403632145)
            ·
              refine ⟨17958900539106532052724109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23945200718808709403632145 17958900539106532052724109)
              ·
                refine ⟨6734587702164949519771541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17958900539106532052724109 6734587702164949519771541)
                ·
                  refine ⟨315683798538982008739291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6734587702164949519771541 315683798538982008739291)
                  ·
                    rfl

theorem cell22_2766564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_2766564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766564 prefixEnd_2766564 := by exact prefixLift 2766564
  have htrace : WordTrace (prefixWord ++ tailWord_2766564) baseStart_2766564 baseEnd_2766564 := by
    simpa [prefixWord, tailWord_2766564, baseEnd_2766564] using wordTrace_append hprefix tailTrace_2766564
  have hstable : (prefixWord ++ tailWord_2766564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766564).length < 2 ^ (prefixWord ++ tailWord_2766564).sum := by decide
  have hdescent : baseEnd_2766564 < baseStart_2766564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766579 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_2766579 : Nat := 118140960795 + 2766579 * 2 ^ 59
def prefixEnd_2766579 : Nat := 4983230072969 + 3 ^ 40 * 2766579 * 2
def baseEnd_2766579 : Nat := 947056530423490987092827

theorem tailTrace_2766579 : CollatzResearch.WordTrace tailWord_2766579 prefixEnd_2766579 947056530423490987092827 := by
  unfold tailWord_2766579
  simp only [CollatzResearch.WordTrace]
  refine ⟨100905425844164251921134791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67270283896109501280756527 100905425844164251921134791)
  ·
    refine ⟨151358138766246377881702187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100905425844164251921134791 151358138766246377881702187)
    ·
      refine ⟨227037208149369566822553281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151358138766246377881702187 227037208149369566822553281)
      ·
        refine ⟨170277906112027175116914961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227037208149369566822553281 170277906112027175116914961)
        ·
          refine ⟨127708429584020381337686221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170277906112027175116914961 127708429584020381337686221)
          ·
            refine ⟨47890661094007643001632333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127708429584020381337686221 47890661094007643001632333)
            ·
              refine ⟨17958997910252866125612125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47890661094007643001632333 17958997910252866125612125)
              ·
                refine ⟨6734624216344824797104547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17958997910252866125612125 6734624216344824797104547)
                ·
                  refine ⟨10101936324517237195656821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734624216344824797104547 10101936324517237195656821)
                  ·
                    refine ⟨947056530423490987092827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10101936324517237195656821 947056530423490987092827)
                    ·
                      rfl

theorem cell22_2766579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_2766579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766579 prefixEnd_2766579 := by exact prefixLift 2766579
  have htrace : WordTrace (prefixWord ++ tailWord_2766579) baseStart_2766579 baseEnd_2766579 := by
    simpa [prefixWord, tailWord_2766579, baseEnd_2766579] using wordTrace_append hprefix tailTrace_2766579
  have hstable : (prefixWord ++ tailWord_2766579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766579).length < 2 ^ (prefixWord ++ tailWord_2766579).sum := by decide
  have hdescent : baseEnd_2766579 < baseStart_2766579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766596 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_2766596 : Nat := 118140960795 + 2766596 * 2 ^ 59
def prefixEnd_2766596 : Nat := 4983230072969 + 3 ^ 40 * 2766596 * 2
def baseEnd_2766596 : Nat := 947062349870908609417775

theorem tailTrace_2766596 : CollatzResearch.WordTrace tailWord_2766596 prefixEnd_2766596 947062349870908609417775 := by
  unfold tailWord_2766596
  simp only [CollatzResearch.WordTrace]
  refine ⟨50453022942551331912251821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67270697256735109216335761 50453022942551331912251821)
  ·
    refine ⟨18919883603456749467094433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50453022942551331912251821 18919883603456749467094433)
    ·
      refine ⟨14189912702592562100320825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18919883603456749467094433 14189912702592562100320825)
      ·
        refine ⟨10642434526944421575240619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14189912702592562100320825 10642434526944421575240619)
        ·
          refine ⟨15963651790416632362860929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10642434526944421575240619 15963651790416632362860929)
          ·
            refine ⟨11972738842812474272145697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15963651790416632362860929 11972738842812474272145697)
            ·
              refine ⟨8979554132109355704109273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11972738842812474272145697 8979554132109355704109273)
              ·
                refine ⟨6734665599082016778081955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8979554132109355704109273 6734665599082016778081955)
                ·
                  refine ⟨10101998398623025167122933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6734665599082016778081955 10101998398623025167122933)
                  ·
                    refine ⟨947062349870908609417775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10101998398623025167122933 947062349870908609417775)
                    ·
                      rfl

theorem cell22_2766596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_2766596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766596 prefixEnd_2766596 := by exact prefixLift 2766596
  have htrace : WordTrace (prefixWord ++ tailWord_2766596) baseStart_2766596 baseEnd_2766596 := by
    simpa [prefixWord, tailWord_2766596, baseEnd_2766596] using wordTrace_append hprefix tailTrace_2766596
  have hstable : (prefixWord ++ tailWord_2766596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766596).length < 2 ^ (prefixWord ++ tailWord_2766596).sum := by decide
  have hdescent : baseEnd_2766596 < baseStart_2766596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766613 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2766613 : Nat := 118140960795 + 2766613 * 2 ^ 59
def prefixEnd_2766613 : Nat := 4983230072969 + 3 ^ 40 * 2766613 * 2
def baseEnd_2766613 : Nat := 947068169318326231742723

theorem tailTrace_2766613 : CollatzResearch.WordTrace tailWord_2766613 prefixEnd_2766613 947068169318326231742723 := by
  unfold tailWord_2766613
  simp only [CollatzResearch.WordTrace]
  refine ⟨100906665926041075727872493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67271110617360717151914995 100906665926041075727872493)
  ·
    refine ⟨37839999722265403397952185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100906665926041075727872493 37839999722265403397952185)
    ·
      refine ⟨28379999791699052548464139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37839999722265403397952185 28379999791699052548464139)
      ·
        refine ⟨42569999687548578822696209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28379999791699052548464139 42569999687548578822696209)
        ·
          refine ⟨31927499765661434117022157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42569999687548578822696209 31927499765661434117022157)
          ·
            refine ⟨11972812412123037793883309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31927499765661434117022157 11972812412123037793883309)
            ·
              refine ⟨4489804654546139172706241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11972812412123037793883309 4489804654546139172706241)
              ·
                refine ⟨3367353490909604379529681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489804654546139172706241 3367353490909604379529681)
                ·
                  refine ⟨2525515118182203284647261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367353490909604379529681 2525515118182203284647261)
                  ·
                    refine ⟨947068169318326231742723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525515118182203284647261 947068169318326231742723)
                    ·
                      rfl

theorem cell22_2766613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2766613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766613 prefixEnd_2766613 := by exact prefixLift 2766613
  have htrace : WordTrace (prefixWord ++ tailWord_2766613) baseStart_2766613 baseEnd_2766613 := by
    simpa [prefixWord, tailWord_2766613, baseEnd_2766613] using wordTrace_append hprefix tailTrace_2766613
  have hstable : (prefixWord ++ tailWord_2766613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766613).length < 2 ^ (prefixWord ++ tailWord_2766613).sum := by decide
  have hdescent : baseEnd_2766613 < baseStart_2766613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766643 : List Nat := [1, 1, 1, 2, 7, 2, 2, 6]
def baseStart_2766643 : Nat := 118140960795 + 2766643 * 2 ^ 59
def prefixEnd_2766643 : Nat := 4983230072969 + 3 ^ 40 * 2766643 * 2
def baseEnd_2766643 : Nat := 105230937659046239276959

theorem tailTrace_2766643 : CollatzResearch.WordTrace tailWord_2766643 prefixEnd_2766643 105230937659046239276959 := by
  unfold tailWord_2766643
  simp only [CollatzResearch.WordTrace]
  refine ⟨100907760115932390851464583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67271840077288260567643055 100907760115932390851464583)
  ·
    refine ⟨151361640173898586277196875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100907760115932390851464583 151361640173898586277196875)
    ·
      refine ⟨227042460260847879415795313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151361640173898586277196875 227042460260847879415795313)
      ·
        refine ⟨170281845195635909561846485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227042460260847879415795313 170281845195635909561846485)
        ·
          refine ⟨3990980746772716630355777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 170281845195635909561846485 3990980746772716630355777)
          ·
            refine ⟨2993235560079537472766833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3990980746772716630355777 2993235560079537472766833)
            ·
              refine ⟨2244926670059653104575125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2993235560079537472766833 2244926670059653104575125)
              ·
                refine ⟨105230937659046239276959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2244926670059653104575125 105230937659046239276959)
                ·
                  rfl

theorem cell22_2766643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 6].length) (baseStart_2766643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766643 prefixEnd_2766643 := by exact prefixLift 2766643
  have htrace : WordTrace (prefixWord ++ tailWord_2766643) baseStart_2766643 baseEnd_2766643 := by
    simpa [prefixWord, tailWord_2766643, baseEnd_2766643] using wordTrace_append hprefix tailTrace_2766643
  have hstable : (prefixWord ++ tailWord_2766643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766643).length < 2 ^ (prefixWord ++ tailWord_2766643).sum := by decide
  have hdescent : baseEnd_2766643 < baseStart_2766643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766688 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_2766688 : Nat := 118140960795 + 2766688 * 2 ^ 59
def prefixEnd_2766688 : Nat := 4983230072969 + 3 ^ 40 * 2766688 * 2
def baseEnd_2766688 : Nat := 315697947783683678705831

theorem tailTrace_2766688 : CollatzResearch.WordTrace tailWord_2766688 prefixEnd_2766688 315697947783683678705831 := by
  unfold tailWord_2766688
  simp only [CollatzResearch.WordTrace]
  refine ⟨50454700700384681768426359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67272934267179575691235145 50454700700384681768426359)
  ·
    refine ⟨75682051050577022652639539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50454700700384681768426359 75682051050577022652639539)
    ·
      refine ⟨113523076575865533978959309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75682051050577022652639539 113523076575865533978959309)
      ·
        refine ⟨42571153715949575242109741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113523076575865533978959309 42571153715949575242109741)
        ·
          refine ⟨15964182643481090715791153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42571153715949575242109741 15964182643481090715791153)
          ·
            refine ⟨11973136982610818036843365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15964182643481090715791153 11973136982610818036843365)
            ·
              refine ⟨2244963184239528381908131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11973136982610818036843365 2244963184239528381908131)
              ·
                refine ⟨3367444776359292572862197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244963184239528381908131 3367444776359292572862197)
                ·
                  refine ⟨315697947783683678705831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3367444776359292572862197 315697947783683678705831)
                  ·
                    rfl

theorem cell22_2766688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_2766688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766688 prefixEnd_2766688 := by exact prefixLift 2766688
  have htrace : WordTrace (prefixWord ++ tailWord_2766688) baseStart_2766688 baseEnd_2766688 := by
    simpa [prefixWord, tailWord_2766688, baseEnd_2766688] using wordTrace_append hprefix tailTrace_2766688
  have hstable : (prefixWord ++ tailWord_2766688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766688).length < 2 ^ (prefixWord ++ tailWord_2766688).sum := by decide
  have hdescent : baseEnd_2766688 < baseStart_2766688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766699 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 8]
def baseStart_2766699 : Nat := 118140960795 + 2766699 * 2 ^ 59
def prefixEnd_2766699 : Nat := 4983230072969 + 3 ^ 40 * 2766699 * 2
def baseEnd_2766699 : Nat := 315699202958616891364153

theorem tailTrace_2766699 : CollatzResearch.WordTrace tailWord_2766699 prefixEnd_2766699 315699202958616891364153 := by
  unfold tailWord_2766699
  simp only [CollatzResearch.WordTrace]
  refine ⟨100909802603729512415503151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67273201735819674943668767 100909802603729512415503151)
  ·
    refine ⟨151364703905594268623254727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100909802603729512415503151 151364703905594268623254727)
    ·
      refine ⟨227047055858391402934882091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151364703905594268623254727 227047055858391402934882091)
      ·
        refine ⟨340570583787587104402323137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227047055858391402934882091 340570583787587104402323137)
        ·
          refine ⟨255427937840690328301742353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340570583787587104402323137 255427937840690328301742353)
          ·
            refine ⟨191570953380517746226306765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255427937840690328301742353 191570953380517746226306765)
            ·
              refine ⟨71839107517694154834865037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191570953380517746226306765 71839107517694154834865037)
              ·
                refine ⟨26939665319135308063074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71839107517694154834865037 26939665319135308063074389)
                ·
                  refine ⟨315699202958616891364153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26939665319135308063074389 315699202958616891364153)
                  ·
                    rfl

theorem cell22_2766699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_2766699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766699 prefixEnd_2766699 := by exact prefixLift 2766699
  have htrace : WordTrace (prefixWord ++ tailWord_2766699) baseStart_2766699 baseEnd_2766699 := by
    simpa [prefixWord, tailWord_2766699, baseEnd_2766699] using wordTrace_append hprefix tailTrace_2766699
  have hstable : (prefixWord ++ tailWord_2766699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766699).length < 2 ^ (prefixWord ++ tailWord_2766699).sum := by decide
  have hdescent : baseEnd_2766699 < baseStart_2766699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766748 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_2766748 : Nat := 118140960795 + 2766748 * 2 ^ 59
def prefixEnd_2766748 : Nat := 4983230072969 + 3 ^ 40 * 2766748 * 2
def baseEnd_2766748 : Nat := 947114382577230879617309

theorem tailTrace_2766748 : CollatzResearch.WordTrace tailWord_2766748 prefixEnd_2766748 947114382577230879617309 := by
  unfold tailWord_2766748
  simp only [CollatzResearch.WordTrace]
  refine ⟨50455794890275996892018449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67274393187034662522691265 50455794890275996892018449)
  ·
    refine ⟨37841846167706997669013837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50455794890275996892018449 37841846167706997669013837)
    ·
      refine ⟨14190692312890124125880189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37841846167706997669013837 14190692312890124125880189)
      ·
        refine ⟨5321509617333796547205071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14190692312890124125880189 5321509617333796547205071)
        ·
          refine ⟨7982264426000694820807607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5321509617333796547205071 7982264426000694820807607)
          ·
            refine ⟨11973396639001042231211411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7982264426000694820807607 11973396639001042231211411)
            ·
              refine ⟨17960094958501563346817117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11973396639001042231211411 17960094958501563346817117)
              ·
                refine ⟨6735035609438086255056419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17960094958501563346817117 6735035609438086255056419)
                ·
                  refine ⟨10102553414157129382584629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735035609438086255056419 10102553414157129382584629)
                  ·
                    refine ⟨947114382577230879617309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10102553414157129382584629 947114382577230879617309)
                    ·
                      rfl

theorem cell22_2766748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_2766748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766748 prefixEnd_2766748 := by exact prefixLift 2766748
  have htrace : WordTrace (prefixWord ++ tailWord_2766748) baseStart_2766748 baseEnd_2766748 := by
    simpa [prefixWord, tailWord_2766748, baseEnd_2766748] using wordTrace_append hprefix tailTrace_2766748
  have hstable : (prefixWord ++ tailWord_2766748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766748).length < 2 ^ (prefixWord ++ tailWord_2766748).sum := by decide
  have hdescent : baseEnd_2766748 < baseStart_2766748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766782 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2766782 : Nat := 118140960795 + 2766782 * 2 ^ 59
def prefixEnd_2766782 : Nat := 4983230072969 + 3 ^ 40 * 2766782 * 2
def baseEnd_2766782 : Nat := 947126021472066124267205

theorem tailTrace_2766782 : CollatzResearch.WordTrace tailWord_2766782 prefixEnd_2766782 947126021472066124267205 := by
  unfold tailWord_2766782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614103732803602198846825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67275219908285878393849733 12614103732803602198846825)
  ·
    refine ⟨9460577799602701649135119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12614103732803602198846825 9460577799602701649135119)
    ·
      refine ⟨14190866699404052473702679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9460577799602701649135119 14190866699404052473702679)
      ·
        refine ⟨21286300049106078710554019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14190866699404052473702679 21286300049106078710554019)
        ·
          refine ⟨31929450073659118065831029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21286300049106078710554019 31929450073659118065831029)
          ·
            refine ⟨2993385944405542318671659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31929450073659118065831029 2993385944405542318671659)
            ·
              refine ⟨4490078916608313478007489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993385944405542318671659 4490078916608313478007489)
              ·
                refine ⟨3367559187456235108505617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4490078916608313478007489 3367559187456235108505617)
                ·
                  refine ⟨2525669390592176331379213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367559187456235108505617 2525669390592176331379213)
                  ·
                    refine ⟨947126021472066124267205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525669390592176331379213 947126021472066124267205)
                    ·
                      rfl

theorem cell22_2766782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2766782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766782 prefixEnd_2766782 := by exact prefixLift 2766782
  have htrace : WordTrace (prefixWord ++ tailWord_2766782) baseStart_2766782 baseEnd_2766782 := by
    simpa [prefixWord, tailWord_2766782, baseEnd_2766782] using wordTrace_append hprefix tailTrace_2766782
  have hstable : (prefixWord ++ tailWord_2766782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766782).length < 2 ^ (prefixWord ++ tailWord_2766782).sum := by decide
  have hdescent : baseEnd_2766782 < baseStart_2766782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766812 : List Nat := [2, 2, 6, 1, 1, 1, 1, 8]
def baseStart_2766812 : Nat := 118140960795 + 2766812 * 2 ^ 59
def prefixEnd_2766812 : Nat := 4983230072969 + 3 ^ 40 * 2766812 * 2
def baseEnd_2766812 : Nat := 105237365676128449557457

theorem tailTrace_2766812 : CollatzResearch.WordTrace tailWord_2766812 prefixEnd_2766812 105237365676128449557457 := by
  unfold tailWord_2766812
  simp only [CollatzResearch.WordTrace]
  refine ⟨50456962026160066357183345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67275949368213421809577793 50456962026160066357183345)
  ·
    refine ⟨37842721519620049767887509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50456962026160066357183345 37842721519620049767887509)
    ·
      refine ⟨1773877571232189832869727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37842721519620049767887509 1773877571232189832869727)
      ·
        refine ⟨2660816356848284749304591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773877571232189832869727 2660816356848284749304591)
        ·
          refine ⟨3991224535272427123956887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660816356848284749304591 3991224535272427123956887)
          ·
            refine ⟨5986836802908640685935331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991224535272427123956887 5986836802908640685935331)
            ·
              refine ⟨8980255204362961028902997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5986836802908640685935331 8980255204362961028902997)
              ·
                refine ⟨105237365676128449557457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8980255204362961028902997 105237365676128449557457)
                ·
                  rfl

theorem cell22_2766812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_2766812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766812 prefixEnd_2766812 := by exact prefixLift 2766812
  have htrace : WordTrace (prefixWord ++ tailWord_2766812) baseStart_2766812 baseEnd_2766812 := by
    simpa [prefixWord, tailWord_2766812, baseEnd_2766812] using wordTrace_append hprefix tailTrace_2766812
  have hstable : (prefixWord ++ tailWord_2766812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766812).length < 2 ^ (prefixWord ++ tailWord_2766812).sum := by decide
  have hdescent : baseEnd_2766812 < baseStart_2766812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766883 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 1, 5]
def baseStart_2766883 : Nat := 118140960795 + 2766883 * 2 ^ 59
def prefixEnd_2766883 : Nat := 4983230072969 + 3 ^ 40 * 2766883 * 2
def baseEnd_2766883 : Nat := 947160595836135527491895

theorem tailTrace_2766883 : CollatzResearch.WordTrace tailWord_2766883 prefixEnd_2766883 947160595836135527491895 := by
  unfold tailWord_2766883
  simp only [CollatzResearch.WordTrace]
  refine ⟨100916513635062911840201303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67277675756708607893467535 100916513635062911840201303)
  ·
    refine ⟨151374770452594367760301955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100916513635062911840201303 151374770452594367760301955)
    ·
      refine ⟨227062155678891551640452933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151374770452594367760301955 227062155678891551640452933)
      ·
        refine ⟨42574154189792165932584925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227062155678891551640452933 42574154189792165932584925)
        ·
          refine ⟨15965307821172062224719347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42574154189792165932584925 15965307821172062224719347)
          ·
            refine ⟨23947961731758093337079021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15965307821172062224719347 23947961731758093337079021)
            ·
              refine ⟨8980485649409285001404633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23947961731758093337079021 8980485649409285001404633)
              ·
                refine ⟨6735364237056963751053475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8980485649409285001404633 6735364237056963751053475)
                ·
                  refine ⟨10103046355585445626580213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735364237056963751053475 10103046355585445626580213)
                  ·
                    refine ⟨947160595836135527491895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10103046355585445626580213 947160595836135527491895)
                    ·
                      rfl

theorem cell22_2766883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_2766883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766883 prefixEnd_2766883 := by exact prefixLift 2766883
  have htrace : WordTrace (prefixWord ++ tailWord_2766883) baseStart_2766883 baseEnd_2766883 := by
    simpa [prefixWord, tailWord_2766883, baseEnd_2766883] using wordTrace_append hprefix tailTrace_2766883
  have hstable : (prefixWord ++ tailWord_2766883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766883).length < 2 ^ (prefixWord ++ tailWord_2766883).sum := by decide
  have hdescent : baseEnd_2766883 < baseStart_2766883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766896 : List Nat := [2, 1, 1, 1, 2, 15]
def baseStart_2766896 : Nat := 118140960795 + 2766896 * 2 ^ 59
def prefixEnd_2766896 : Nat := 4983230072969 + 3 ^ 40 * 2766896 * 2
def baseEnd_2766896 : Nat := 11693395629651948480455

theorem tailTrace_2766896 : CollatzResearch.WordTrace tailWord_2766896 prefixEnd_2766896 11693395629651948480455 := by
  unfold tailWord_2766896
  simp only [CollatzResearch.WordTrace]
  refine ⟨50458493892007907530212271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67277991856010543373616361 50458493892007907530212271)
  ·
    refine ⟨75687740838011861295318407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50458493892007907530212271 75687740838011861295318407)
    ·
      refine ⟨113531611257017791942977611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75687740838011861295318407 113531611257017791942977611)
      ·
        refine ⟨170297416885526687914466417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113531611257017791942977611 170297416885526687914466417)
        ·
          refine ⟨127723062664145015935849813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170297416885526687914466417 127723062664145015935849813)
          ·
            refine ⟨11693395629651948480455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 127723062664145015935849813 11693395629651948480455)
            ·
              rfl

theorem cell22_2766896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 15].length) (baseStart_2766896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766896 prefixEnd_2766896 := by exact prefixLift 2766896
  have htrace : WordTrace (prefixWord ++ tailWord_2766896) baseStart_2766896 baseEnd_2766896 := by
    simpa [prefixWord, tailWord_2766896, baseEnd_2766896] using wordTrace_append hprefix tailTrace_2766896
  have hstable : (prefixWord ++ tailWord_2766896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766896).length < 2 ^ (prefixWord ++ tailWord_2766896).sum := by decide
  have hdescent : baseEnd_2766896 < baseStart_2766896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766902 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2766902 : Nat := 118140960795 + 2766902 * 2 ^ 59
def prefixEnd_2766902 : Nat := 4983230072969 + 3 ^ 40 * 2766902 * 2
def baseEnd_2766902 : Nat := 315722366641475270422279

theorem tailTrace_2766902 : CollatzResearch.WordTrace tailWord_2766902 prefixEnd_2766902 315722366641475270422279 := by
  unfold tailWord_2766902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307325413874629880321435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67278137747996052056761973 6307325413874629880321435)
  ·
    refine ⟨9460988120811944820482153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6307325413874629880321435 9460988120811944820482153)
    ·
      refine ⟨7095741090608958615361615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9460988120811944820482153 7095741090608958615361615)
      ·
        refine ⟨10643611635913437923042423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7095741090608958615361615 10643611635913437923042423)
        ·
          refine ⟨15965417453870156884563635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10643611635913437923042423 15965417453870156884563635)
          ·
            refine ⟨23948126180805235326845453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15965417453870156884563635 23948126180805235326845453)
            ·
              refine ⟨8980547317801963247567045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23948126180805235326845453 8980547317801963247567045)
              ·
                refine ⟨1683852622087868108918821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8980547317801963247567045 1683852622087868108918821)
                ·
                  refine ⟨315722366641475270422279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1683852622087868108918821 315722366641475270422279)
                  ·
                    rfl

theorem cell22_2766902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2766902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766902 prefixEnd_2766902 := by exact prefixLift 2766902
  have htrace : WordTrace (prefixWord ++ tailWord_2766902) baseStart_2766902 baseEnd_2766902 := by
    simpa [prefixWord, tailWord_2766902, baseEnd_2766902] using wordTrace_append hprefix tailTrace_2766902
  have hstable : (prefixWord ++ tailWord_2766902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766902).length < 2 ^ (prefixWord ++ tailWord_2766902).sum := by decide
  have hdescent : baseEnd_2766902 < baseStart_2766902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766962 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_2766962 : Nat := 118140960795 + 2766962 * 2 ^ 59
def prefixEnd_2766962 : Nat := 4983230072969 + 3 ^ 40 * 2766962 * 2
def baseEnd_2766962 : Nat := 947187639150605654766653

theorem tailTrace_2766962 : CollatzResearch.WordTrace tailWord_2766962 prefixEnd_2766962 947187639150605654766653 := by
  unfold tailWord_2766962
  simp only [CollatzResearch.WordTrace]
  refine ⟨25229848750444177083081785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67279596667851138888218093 25229848750444177083081785)
  ·
    refine ⟨18922386562833132812311339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25229848750444177083081785 18922386562833132812311339)
    ·
      refine ⟨28383579844249699218467009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18922386562833132812311339 28383579844249699218467009)
      ·
        refine ⟨21287684883187274413850257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28383579844249699218467009 21287684883187274413850257)
        ·
          refine ⟨15965763662390455810387693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21287684883187274413850257 15965763662390455810387693)
          ·
            refine ⟨5987161373396420928895385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15965763662390455810387693 5987161373396420928895385)
            ·
              refine ⟨4490371030047315696671539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5987161373396420928895385 4490371030047315696671539)
              ·
                refine ⟨6735556545070973545007309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490371030047315696671539 6735556545070973545007309)
                ·
                  refine ⟨2525833704401615079377741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6735556545070973545007309 2525833704401615079377741)
                  ·
                    refine ⟨947187639150605654766653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525833704401615079377741 947187639150605654766653)
                    ·
                      rfl

theorem cell22_2766962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_2766962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766962 prefixEnd_2766962 := by exact prefixLift 2766962
  have htrace : WordTrace (prefixWord ++ tailWord_2766962) baseStart_2766962 baseEnd_2766962 := by
    simpa [prefixWord, tailWord_2766962, baseEnd_2766962] using wordTrace_append hprefix tailTrace_2766962
  have hstable : (prefixWord ++ tailWord_2766962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766962).length < 2 ^ (prefixWord ++ tailWord_2766962).sum := by decide
  have hdescent : baseEnd_2766962 < baseStart_2766962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2766998 : List Nat := [5, 3, 2, 1, 2, 1, 8]
def baseStart_2766998 : Nat := 118140960795 + 2766998 * 2 ^ 59
def prefixEnd_2766998 : Nat := 4983230072969 + 3 ^ 40 * 2766998 * 2
def baseEnd_2766998 : Nat := 35081480099493094846909

theorem tailTrace_2766998 : CollatzResearch.WordTrace tailWord_2766998 prefixEnd_2766998 35081480099493094846909 := by
  unfold tailWord_2766998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307544251852892905039853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67280472019764190987091765 6307544251852892905039853)
  ·
    refine ⟨2365329094444834839389945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6307544251852892905039853 2365329094444834839389945)
    ·
      refine ⟨1773996820833626129542459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2365329094444834839389945 1773996820833626129542459)
      ·
        refine ⟨2660995231250439194313689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773996820833626129542459 2660995231250439194313689)
        ·
          refine ⟨1995746423437829395735267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2660995231250439194313689 1995746423437829395735267)
          ·
            refine ⟨2993619635156744093602901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995746423437829395735267 2993619635156744093602901)
            ·
              refine ⟨35081480099493094846909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2993619635156744093602901 35081480099493094846909)
              ·
                rfl

theorem cell22_2766998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 8].length) (baseStart_2766998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2766998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2766998 prefixEnd_2766998 := by exact prefixLift 2766998
  have htrace : WordTrace (prefixWord ++ tailWord_2766998) baseStart_2766998 baseEnd_2766998 := by
    simpa [prefixWord, tailWord_2766998, baseEnd_2766998] using wordTrace_append hprefix tailTrace_2766998
  have hstable : (prefixWord ++ tailWord_2766998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2766998).length < 2 ^ (prefixWord ++ tailWord_2766998).sum := by decide
  have hdescent : baseEnd_2766998 < baseStart_2766998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2766998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767069 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2767069 : Nat := 118140960795 + 2767069 * 2 ^ 59
def prefixEnd_2767069 : Nat := 4983230072969 + 3 ^ 40 * 2767069 * 2
def baseEnd_2767069 : Nat := 947224267437293042341325

theorem tailTrace_2767069 : CollatzResearch.WordTrace tailWord_2767069 prefixEnd_2767069 947224267437293042341325 := by
  unfold tailWord_2767069
  simp only [CollatzResearch.WordTrace]
  refine ⟨100923297612389065606472261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67282198408259377070981507 100923297612389065606472261)
  ·
    refine ⟨18923118302322949801213549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100923297612389065606472261 18923118302322949801213549)
    ·
      refine ⟨7096169363371106175455081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18923118302322949801213549 7096169363371106175455081)
      ·
        refine ⟨5322127022528329631591311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7096169363371106175455081 5322127022528329631591311)
        ·
          refine ⟨7983190533792494447386967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5322127022528329631591311 7983190533792494447386967)
          ·
            refine ⟨11974785800688741671080451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7983190533792494447386967 11974785800688741671080451)
            ·
              refine ⟨17962178701033112506620677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11974785800688741671080451 17962178701033112506620677)
              ·
                refine ⟨3367908506443708594991377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17962178701033112506620677 3367908506443708594991377)
                ·
                  refine ⟨2525931379832781446243533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3367908506443708594991377 2525931379832781446243533)
                  ·
                    refine ⟨947224267437293042341325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525931379832781446243533 947224267437293042341325)
                    ·
                      rfl

theorem cell22_2767069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2767069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767069 prefixEnd_2767069 := by exact prefixLift 2767069
  have htrace : WordTrace (prefixWord ++ tailWord_2767069) baseStart_2767069 baseEnd_2767069 := by
    simpa [prefixWord, tailWord_2767069, baseEnd_2767069] using wordTrace_append hprefix tailTrace_2767069
  have hstable : (prefixWord ++ tailWord_2767069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767069).length < 2 ^ (prefixWord ++ tailWord_2767069).sum := by decide
  have hdescent : baseEnd_2767069 < baseStart_2767069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767114 : List Nat := [3, 1, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2767114 : Nat := 118140960795 + 2767114 * 2 ^ 59
def prefixEnd_2767114 : Nat := 4983230072969 + 3 ^ 40 * 2767114 * 2
def baseEnd_2767114 : Nat := 947239671856927924966187

theorem tailTrace_2767114 : CollatzResearch.WordTrace tailWord_2767114 prefixEnd_2767114 947239671856927924966187 := by
  unfold tailWord_2767114
  simp only [CollatzResearch.WordTrace]
  refine ⟨25231234724306509572965099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67283292598150692194573597 25231234724306509572965099)
  ·
    refine ⟨37846852086459764359447649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25231234724306509572965099 37846852086459764359447649)
    ·
      refine ⟨28385139064844823269585737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37846852086459764359447649 28385139064844823269585737)
      ·
        refine ⟨21288854298633617452189303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28385139064844823269585737 21288854298633617452189303)
        ·
          refine ⟨31933281447950426178283955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21288854298633617452189303 31933281447950426178283955)
          ·
            refine ⟨47899922171925639267425933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31933281447950426178283955 47899922171925639267425933)
            ·
              refine ⟨17962470814472114725284725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47899922171925639267425933 17962470814472114725284725)
              ·
                refine ⟨1683981638856760755495443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17962470814472114725284725 1683981638856760755495443)
                ·
                  refine ⟨2525972458285141133243165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683981638856760755495443 2525972458285141133243165)
                  ·
                    refine ⟨947239671856927924966187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2525972458285141133243165 947239671856927924966187)
                    ·
                      rfl

theorem cell22_2767114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2767114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767114 prefixEnd_2767114 := by exact prefixLift 2767114
  have htrace : WordTrace (prefixWord ++ tailWord_2767114) baseStart_2767114 baseEnd_2767114 := by
    simpa [prefixWord, tailWord_2767114, baseEnd_2767114] using wordTrace_append hprefix tailTrace_2767114
  have hstable : (prefixWord ++ tailWord_2767114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767114).length < 2 ^ (prefixWord ++ tailWord_2767114).sum := by decide
  have hdescent : baseEnd_2767114 < baseStart_2767114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767125 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2767125 : Nat := 118140960795 + 2767125 * 2 ^ 59
def prefixEnd_2767125 : Nat := 4983230072969 + 3 ^ 40 * 2767125 * 2
def baseEnd_2767125 : Nat := 947243437381727562941153

theorem tailTrace_2767125 : CollatzResearch.WordTrace tailWord_2767125 prefixEnd_2767125 947243437381727562941153 := by
  unfold tailWord_2767125
  simp only [CollatzResearch.WordTrace]
  refine ⟨100925340100186187170510829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67283560066790791447007219 100925340100186187170510829)
  ·
    refine ⟨37847002537569820188941561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100925340100186187170510829 37847002537569820188941561)
    ·
      refine ⟨28385251903177365141706171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37847002537569820188941561 28385251903177365141706171)
      ·
        refine ⟨42577877854766047712559257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28385251903177365141706171 42577877854766047712559257)
        ·
          refine ⟨31933408391074535784419443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42577877854766047712559257 31933408391074535784419443)
          ·
            refine ⟨47900112586611803676629165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31933408391074535784419443 47900112586611803676629165)
            ·
              refine ⟨17962542219979426378735937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47900112586611803676629165 17962542219979426378735937)
              ·
                refine ⟨13471906664984569784051953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17962542219979426378735937 13471906664984569784051953)
                ·
                  refine ⟨10103929998738427338038965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13471906664984569784051953 10103929998738427338038965)
                  ·
                    refine ⟨947243437381727562941153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10103929998738427338038965 947243437381727562941153)
                    ·
                      rfl

theorem cell22_2767125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2767125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767125 prefixEnd_2767125 := by exact prefixLift 2767125
  have htrace : WordTrace (prefixWord ++ tailWord_2767125) baseStart_2767125 baseEnd_2767125 := by
    simpa [prefixWord, tailWord_2767125, baseEnd_2767125] using wordTrace_append hprefix tailTrace_2767125
  have hstable : (prefixWord ++ tailWord_2767125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767125).length < 2 ^ (prefixWord ++ tailWord_2767125).sum := by decide
  have hdescent : baseEnd_2767125 < baseStart_2767125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767127 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 5]
def baseStart_2767127 : Nat := 118140960795 + 2767127 * 2 ^ 59
def prefixEnd_2767127 : Nat := 4983230072969 + 3 ^ 40 * 2767127 * 2
def baseEnd_2767127 : Nat := 315748040674200074797049

theorem tailTrace_2767127 : CollatzResearch.WordTrace tailWord_2767127 prefixEnd_2767127 315748040674200074797049 := by
  unfold tailWord_2767127
  simp only [CollatzResearch.WordTrace]
  refine ⟨100925413046178941512083635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67283608697452627674722423 100925413046178941512083635)
  ·
    refine ⟨151388119569268412268125453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100925413046178941512083635 151388119569268412268125453)
    ·
      refine ⟨56770544838475654600547045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151388119569268412268125453 56770544838475654600547045)
      ·
        refine ⟨10644477157214185237602571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56770544838475654600547045 10644477157214185237602571)
        ·
          refine ⟨15966715735821277856403857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10644477157214185237602571 15966715735821277856403857)
          ·
            refine ⟨11975036801865958392302893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15966715735821277856403857 11975036801865958392302893)
            ·
              refine ⟨4490638800699734397113585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11975036801865958392302893 4490638800699734397113585)
              ·
                refine ⟨3367979100524800797835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4490638800699734397113585 3367979100524800797835189)
                ·
                  refine ⟨315748040674200074797049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3367979100524800797835189 315748040674200074797049)
                  ·
                    rfl

theorem cell22_2767127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 5].length) (baseStart_2767127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767127 prefixEnd_2767127 := by exact prefixLift 2767127
  have htrace : WordTrace (prefixWord ++ tailWord_2767127) baseStart_2767127 baseEnd_2767127 := by
    simpa [prefixWord, tailWord_2767127, baseEnd_2767127] using wordTrace_append hprefix tailTrace_2767127
  have hstable : (prefixWord ++ tailWord_2767127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767127).length < 2 ^ (prefixWord ++ tailWord_2767127).sum := by decide
  have hdescent : baseEnd_2767127 < baseStart_2767127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767155 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 6]
def baseStart_2767155 : Nat := 118140960795 + 2767155 * 2 ^ 59
def prefixEnd_2767155 : Nat := 4983230072969 + 3 ^ 40 * 2767155 * 2
def baseEnd_2767155 : Nat := 315751235664939161563687

theorem tailTrace_2767155 : CollatzResearch.WordTrace tailWord_2767155 prefixEnd_2767155 315751235664939161563687 := by
  unfold tailWord_2767155
  simp only [CollatzResearch.WordTrace]
  refine ⟨100926434290077502294102919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67284289526718334862735279 100926434290077502294102919)
  ·
    refine ⟨151389651435116253441154379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100926434290077502294102919 151389651435116253441154379)
    ·
      refine ⟨227084477152674380161731569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151389651435116253441154379 227084477152674380161731569)
      ·
        refine ⟨170313357864505785121298677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227084477152674380161731569 170313357864505785121298677)
        ·
          refine ⟨15966877299797417355121751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170313357864505785121298677 15966877299797417355121751)
          ·
            refine ⟨23950315949696126032682627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15966877299797417355121751 23950315949696126032682627)
            ·
              refine ⟨35925473924544189049023941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23950315949696126032682627 35925473924544189049023941)
              ·
                refine ⟨6736026360852035446691989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35925473924544189049023941 6736026360852035446691989)
                ·
                  refine ⟨315751235664939161563687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736026360852035446691989 315751235664939161563687)
                  ·
                    rfl

theorem cell22_2767155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 6].length) (baseStart_2767155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767155 prefixEnd_2767155 := by exact prefixLift 2767155
  have htrace : WordTrace (prefixWord ++ tailWord_2767155) baseStart_2767155 baseEnd_2767155 := by
    simpa [prefixWord, tailWord_2767155, baseEnd_2767155] using wordTrace_append hprefix tailTrace_2767155
  have hstable : (prefixWord ++ tailWord_2767155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767155).length < 2 ^ (prefixWord ++ tailWord_2767155).sum := by decide
  have hdescent : baseEnd_2767155 < baseStart_2767155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767189 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 6]
def baseStart_2767189 : Nat := 118140960795 + 2767189 * 2 ^ 59
def prefixEnd_2767189 : Nat := 4983230072969 + 3 ^ 40 * 2767189 * 2
def baseEnd_2767189 : Nat := 315755115296550909780319

theorem tailTrace_2767189 : CollatzResearch.WordTrace tailWord_2767189 prefixEnd_2767189 315755115296550909780319 := by
  unfold tailWord_2767189
  simp only [CollatzResearch.WordTrace]
  refine ⟨100927674371954326100840621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67285116247969550733893747 100927674371954326100840621)
  ·
    refine ⟨37847877889482872287815233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100927674371954326100840621 37847877889482872287815233)
    ·
      refine ⟨28385908417112154215861425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37847877889482872287815233 28385908417112154215861425)
      ·
        refine ⟨21289431312834115661896069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28385908417112154215861425 21289431312834115661896069)
        ·
          refine ⟨3991768371156396686605513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21289431312834115661896069 3991768371156396686605513)
          ·
            refine ⟨2993826278367297514954135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3991768371156396686605513 2993826278367297514954135)
            ·
              refine ⟨4490739417550946272431203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993826278367297514954135 4490739417550946272431203)
              ·
                refine ⟨6736109126326419408646805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490739417550946272431203 6736109126326419408646805)
                ·
                  refine ⟨315755115296550909780319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6736109126326419408646805 315755115296550909780319)
                  ·
                    rfl

theorem cell22_2767189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_2767189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767189 prefixEnd_2767189 := by exact prefixLift 2767189
  have htrace : WordTrace (prefixWord ++ tailWord_2767189) baseStart_2767189 baseEnd_2767189 := by
    simpa [prefixWord, tailWord_2767189, baseEnd_2767189] using wordTrace_append hprefix tailTrace_2767189
  have hstable : (prefixWord ++ tailWord_2767189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767189).length < 2 ^ (prefixWord ++ tailWord_2767189).sum := by decide
  have hdescent : baseEnd_2767189 < baseStart_2767189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767204 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_2767204 : Nat := 118140960795 + 2767204 * 2 ^ 59
def prefixEnd_2767204 : Nat := 4983230072969 + 3 ^ 40 * 2767204 * 2
def baseEnd_2767204 : Nat := 947270480696197690215911

theorem tailTrace_2767204 : CollatzResearch.WordTrace tailWord_2767204 prefixEnd_2767204 947270480696197690215911 := by
  unfold tailWord_2767204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50464110733449991831318333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67285480977933322441757777 50464110733449991831318333)
  ·
    refine ⟨18924041525043746936744375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50464110733449991831318333 18924041525043746936744375)
    ·
      refine ⟨28386062287565620405116563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18924041525043746936744375 28386062287565620405116563)
      ·
        refine ⟨42579093431348430607674845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28386062287565620405116563 42579093431348430607674845)
        ·
          refine ⟨15967160036755661477878067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42579093431348430607674845 15967160036755661477878067)
          ·
            refine ⟨23950740055133492216817101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15967160036755661477878067 23950740055133492216817101)
            ·
              refine ⟨8981527520675059581306413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23950740055133492216817101 8981527520675059581306413)
              ·
                refine ⟨3368072820253147342989905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8981527520675059581306413 3368072820253147342989905)
                ·
                  refine ⟨2526054615189860507242429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368072820253147342989905 2526054615189860507242429)
                  ·
                    refine ⟨947270480696197690215911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526054615189860507242429 947270480696197690215911)
                    ·
                      rfl

theorem cell22_2767204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_2767204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767204 prefixEnd_2767204 := by exact prefixLift 2767204
  have htrace : WordTrace (prefixWord ++ tailWord_2767204) baseStart_2767204 baseEnd_2767204 := by
    simpa [prefixWord, tailWord_2767204, baseEnd_2767204] using wordTrace_append hprefix tailTrace_2767204
  have hstable : (prefixWord ++ tailWord_2767204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767204).length < 2 ^ (prefixWord ++ tailWord_2767204).sum := by decide
  have hdescent : baseEnd_2767204 < baseStart_2767204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767234 : List Nat := [3, 4, 2, 1, 2, 10]
def baseStart_2767234 : Nat := 118140960795 + 2767234 * 2 ^ 59
def prefixEnd_2767234 : Nat := 4983230072969 + 3 ^ 40 * 2767234 * 2
def baseEnd_2767234 : Nat := 11694824077892439653899

theorem tailTrace_2767234 : CollatzResearch.WordTrace tailWord_2767234 prefixEnd_2767234 11694824077892439653899 := by
  unfold tailWord_2767234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25232328914197824696557189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67286210437860865857485837 25232328914197824696557189)
  ·
    refine ⟨4731061671412092130604473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25232328914197824696557189 4731061671412092130604473)
    ·
      refine ⟨3548296253559069097953355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4731061671412092130604473 3548296253559069097953355)
      ·
        refine ⟨5322444380338603646930033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3548296253559069097953355 5322444380338603646930033)
        ·
          refine ⟨3991833285253952735197525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5322444380338603646930033 3991833285253952735197525)
          ·
            refine ⟨11694824077892439653899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3991833285253952735197525 11694824077892439653899)
            ·
              rfl

theorem cell22_2767234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 10].length) (baseStart_2767234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767234 prefixEnd_2767234 := by exact prefixLift 2767234
  have htrace : WordTrace (prefixWord ++ tailWord_2767234) baseStart_2767234 baseEnd_2767234 := by
    simpa [prefixWord, tailWord_2767234, baseEnd_2767234] using wordTrace_append hprefix tailTrace_2767234
  have hstable : (prefixWord ++ tailWord_2767234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767234).length < 2 ^ (prefixWord ++ tailWord_2767234).sum := by decide
  have hdescent : baseEnd_2767234 < baseStart_2767234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767397 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 9]
def baseStart_2767397 : Nat := 118140960795 + 2767397 * 2 ^ 59
def prefixEnd_2767397 : Nat := 4983230072969 + 3 ^ 40 * 2767397 * 2
def baseEnd_2767397 : Nat := 315778849513469840046773

theorem tailTrace_2767397 : CollatzResearch.WordTrace tailWord_2767397 prefixEnd_2767397 315778849513469840046773 := by
  unfold tailWord_2767397
  simp only [CollatzResearch.WordTrace]
  refine ⟨100935260755200777624412445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67290173836800518416274963 100935260755200777624412445)
  ·
    refine ⟨37850722783200291609154667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100935260755200777624412445 37850722783200291609154667)
    ·
      refine ⟨56776084174800437413732001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37850722783200291609154667 56776084174800437413732001)
      ·
        refine ⟨42582063131100328060299001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56776084174800437413732001 42582063131100328060299001)
        ·
          refine ⟨31936547348325246045224251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42582063131100328060299001 31936547348325246045224251)
          ·
            refine ⟨47904821022487869067836377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31936547348325246045224251 47904821022487869067836377)
            ·
              refine ⟨35928615766865901800877283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47904821022487869067836377 35928615766865901800877283)
              ·
                refine ⟨53892923650298852701315925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35928615766865901800877283 53892923650298852701315925)
                ·
                  refine ⟨315778849513469840046773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53892923650298852701315925 315778849513469840046773)
                  ·
                    rfl

theorem cell22_2767397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_2767397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767397 prefixEnd_2767397 := by exact prefixLift 2767397
  have htrace : WordTrace (prefixWord ++ tailWord_2767397) baseStart_2767397 baseEnd_2767397 := by
    simpa [prefixWord, tailWord_2767397, baseEnd_2767397] using wordTrace_append hprefix tailTrace_2767397
  have hstable : (prefixWord ++ tailWord_2767397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767397).length < 2 ^ (prefixWord ++ tailWord_2767397).sum := by decide
  have hdescent : baseEnd_2767397 < baseStart_2767397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767418 : List Nat := [3, 1, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_2767418 : Nat := 118140960795 + 2767418 * 2 ^ 59
def prefixEnd_2767418 : Nat := 4983230072969 + 3 ^ 40 * 2767418 * 2
def baseEnd_2767418 : Nat := 947343737269572465365255

theorem tailTrace_2767418 : CollatzResearch.WordTrace tailWord_2767418 prefixEnd_2767418 947343737269572465365255 := by
  unfold tailWord_2767418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25234006672031174552731727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67290684458749798807284605 25234006672031174552731727)
  ·
    refine ⟨37851010008046761829097591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25234006672031174552731727 37851010008046761829097591)
    ·
      refine ⟨56776515012070142743646387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37851010008046761829097591 56776515012070142743646387)
      ·
        refine ⟨85164772518105214115469581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56776515012070142743646387 85164772518105214115469581)
        ·
          refine ⟨31936789694289455293301093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85164772518105214115469581 31936789694289455293301093)
          ·
            refine ⟨5988148067679272867493955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31936789694289455293301093 5988148067679272867493955)
            ·
              refine ⟨8982222101518909301240933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988148067679272867493955 8982222101518909301240933)
              ·
                refine ⟨1684166644034795493982675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8982222101518909301240933 1684166644034795493982675)
                ·
                  refine ⟨2526249966052193240974013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684166644034795493982675 2526249966052193240974013)
                  ·
                    refine ⟨947343737269572465365255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526249966052193240974013 947343737269572465365255)
                    ·
                      rfl

theorem cell22_2767418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_2767418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767418 prefixEnd_2767418 := by exact prefixLift 2767418
  have htrace : WordTrace (prefixWord ++ tailWord_2767418) baseStart_2767418 baseEnd_2767418 := by
    simpa [prefixWord, tailWord_2767418, baseEnd_2767418] using wordTrace_append hprefix tailTrace_2767418
  have hstable : (prefixWord ++ tailWord_2767418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767418).length < 2 ^ (prefixWord ++ tailWord_2767418).sum := by decide
  have hdescent : baseEnd_2767418 < baseStart_2767418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767429 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2767429 : Nat := 118140960795 + 2767429 * 2 ^ 59
def prefixEnd_2767429 : Nat := 4983230072969 + 3 ^ 40 * 2767429 * 2
def baseEnd_2767429 : Nat := 947347502794372103340221

theorem tailTrace_2767429 : CollatzResearch.WordTrace tailWord_2767429 prefixEnd_2767429 947347502794372103340221 := by
  unfold tailWord_2767429
  simp only [CollatzResearch.WordTrace]
  refine ⟨100936427891084847089577341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67290951927389898059718227 100936427891084847089577341)
  ·
    refine ⟨37851160459156817658591503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100936427891084847089577341 37851160459156817658591503)
    ·
      refine ⟨56776740688735226487887255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37851160459156817658591503 56776740688735226487887255)
      ·
        refine ⟨85165111033102839731830883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56776740688735226487887255 85165111033102839731830883)
        ·
          refine ⟨127747666549654259597746325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85165111033102839731830883 127747666549654259597746325)
          ·
            refine ⟨5988171869515043418644359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127747666549654259597746325 5988171869515043418644359)
            ·
              refine ⟨8982257804272565127966539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988171869515043418644359 8982257804272565127966539)
              ·
                refine ⟨13473386706408847691949809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8982257804272565127966539 13473386706408847691949809)
                ·
                  refine ⟨10105040029806635768962357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13473386706408847691949809 10105040029806635768962357)
                  ·
                    refine ⟨947347502794372103340221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105040029806635768962357 947347502794372103340221)
                    ·
                      rfl

theorem cell22_2767429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2767429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767429 prefixEnd_2767429 := by exact prefixLift 2767429
  have htrace : WordTrace (prefixWord ++ tailWord_2767429) baseStart_2767429 baseEnd_2767429 := by
    simpa [prefixWord, tailWord_2767429, baseEnd_2767429] using wordTrace_append hprefix tailTrace_2767429
  have hstable : (prefixWord ++ tailWord_2767429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767429).length < 2 ^ (prefixWord ++ tailWord_2767429).sum := by decide
  have hdescent : baseEnd_2767429 < baseStart_2767429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767489 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2767489 : Nat := 118140960795 + 2767489 * 2 ^ 59
def prefixEnd_2767489 : Nat := 4983230072969 + 3 ^ 40 * 2767489 * 2
def baseEnd_2767489 : Nat := 947368042020551946840037

theorem tailTrace_2767489 : CollatzResearch.WordTrace tailWord_2767489 prefixEnd_2767489 947368042020551946840037 := by
  unfold tailWord_2767489
  simp only [CollatzResearch.WordTrace]
  refine ⟨100938616270867477336761521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67292410847244984891174347 100938616270867477336761521)
  ·
    refine ⟨75703962203150608002571141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100938616270867477336761521 75703962203150608002571141)
    ·
      refine ⟨14194492913090739000482089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75703962203150608002571141 14194492913090739000482089)
      ·
        refine ⟨10645869684818054250361567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14194492913090739000482089 10645869684818054250361567)
        ·
          refine ⟨15968804527227081375542351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645869684818054250361567 15968804527227081375542351)
          ·
            refine ⟨23953206790840622063313527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15968804527227081375542351 23953206790840622063313527)
            ·
              refine ⟨35929810186260933094970291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23953206790840622063313527 35929810186260933094970291)
              ·
                refine ⟨53894715279391399642455437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35929810186260933094970291 53894715279391399642455437)
                ·
                  refine ⟨20210518229771774865920789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53894715279391399642455437 20210518229771774865920789)
                  ·
                    refine ⟨947368042020551946840037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20210518229771774865920789 947368042020551946840037)
                    ·
                      rfl

theorem cell22_2767489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2767489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767489 prefixEnd_2767489 := by exact prefixLift 2767489
  have htrace : WordTrace (prefixWord ++ tailWord_2767489) baseStart_2767489 baseEnd_2767489 := by
    simpa [prefixWord, tailWord_2767489, baseEnd_2767489] using wordTrace_append hprefix tailTrace_2767489
  have hstable : (prefixWord ++ tailWord_2767489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767489).length < 2 ^ (prefixWord ++ tailWord_2767489).sum := by decide
  have hdescent : baseEnd_2767489 < baseStart_2767489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767491 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 2, 3]
def baseStart_2767491 : Nat := 118140960795 + 2767491 * 2 ^ 59
def prefixEnd_2767491 : Nat := 4983230072969 + 3 ^ 40 * 2767491 * 2
def baseEnd_2767491 : Nat := 947368726661424608290031

theorem tailTrace_2767491 : CollatzResearch.WordTrace tailWord_2767491 prefixEnd_2767491 947368726661424608290031 := by
  unfold tailWord_2767491
  simp only [CollatzResearch.WordTrace]
  refine ⟨100938689216860231678334327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67292459477906821118889551 100938689216860231678334327)
  ·
    refine ⟨151408033825290347517501491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100938689216860231678334327 151408033825290347517501491)
    ·
      refine ⟨227112050737935521276252237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151408033825290347517501491 227112050737935521276252237)
      ·
        refine ⟨85167019026725820478594589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227112050737935521276252237 85167019026725820478594589)
        ·
          refine ⟨31937632135022182679472971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85167019026725820478594589 31937632135022182679472971)
          ·
            refine ⟨47906448202533274019209457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31937632135022182679472971 47906448202533274019209457)
            ·
              refine ⟨35929836151899955514407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47906448202533274019209457 35929836151899955514407093)
              ·
                refine ⟨3368422139240620829475665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35929836151899955514407093 3368422139240620829475665)
                ·
                  refine ⟨2526316604430465622106749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368422139240620829475665 2526316604430465622106749)
                  ·
                    refine ⟨947368726661424608290031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526316604430465622106749 947368726661424608290031)
                    ·
                      rfl

theorem cell22_2767491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 3].length) (baseStart_2767491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767491 prefixEnd_2767491 := by exact prefixLift 2767491
  have htrace : WordTrace (prefixWord ++ tailWord_2767491) baseStart_2767491 baseEnd_2767491 := by
    simpa [prefixWord, tailWord_2767491, baseEnd_2767491] using wordTrace_append hprefix tailTrace_2767491
  have hstable : (prefixWord ++ tailWord_2767491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767491).length < 2 ^ (prefixWord ++ tailWord_2767491).sum := by decide
  have hdescent : baseEnd_2767491 < baseStart_2767491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767506 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2767506 : Nat := 118140960795 + 2767506 * 2 ^ 59
def prefixEnd_2767506 : Nat := 4983230072969 + 3 ^ 40 * 2767506 * 2
def baseEnd_2767506 : Nat := 947373861467969569164985

theorem tailTrace_2767506 : CollatzResearch.WordTrace tailWord_2767506 prefixEnd_2767506 947373861467969569164985 := by
  unfold tailWord_2767506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25234809077951472310032593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67292824207870592826753581 25234809077951472310032593)
  ·
    refine ⟨18926106808463604232524445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25234809077951472310032593 18926106808463604232524445)
    ·
      refine ⟨7097290053173851587196667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18926106808463604232524445 7097290053173851587196667)
      ·
        refine ⟨10645935079760777380795001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097290053173851587196667 10645935079760777380795001)
        ·
          refine ⟨7984451309820583035596251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10645935079760777380795001 7984451309820583035596251)
          ·
            refine ⟨11976676964730874553394377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7984451309820583035596251 11976676964730874553394377)
            ·
              refine ⟨8982507723548155915045783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11976676964730874553394377 8982507723548155915045783)
              ·
                refine ⟨13473761585322233872568675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8982507723548155915045783 13473761585322233872568675)
                ·
                  refine ⟨20210642377983350808853013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13473761585322233872568675 20210642377983350808853013)
                  ·
                    refine ⟨947373861467969569164985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20210642377983350808853013 947373861467969569164985)
                    ·
                      rfl

theorem cell22_2767506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2767506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767506 prefixEnd_2767506 := by exact prefixLift 2767506
  have htrace : WordTrace (prefixWord ++ tailWord_2767506) baseStart_2767506 baseEnd_2767506 := by
    simpa [prefixWord, tailWord_2767506, baseEnd_2767506] using wordTrace_append hprefix tailTrace_2767506
  have hstable : (prefixWord ++ tailWord_2767506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767506).length < 2 ^ (prefixWord ++ tailWord_2767506).sum := by decide
  have hdescent : baseEnd_2767506 < baseStart_2767506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767508 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2767508 : Nat := 118140960795 + 2767508 * 2 ^ 59
def prefixEnd_2767508 : Nat := 4983230072969 + 3 ^ 40 * 2767508 * 2
def baseEnd_2767508 : Nat := 947374546108842230614979

theorem tailTrace_2767508 : CollatzResearch.WordTrace tailWord_2767508 prefixEnd_2767508 947374546108842230614979 := by
  unfold tailWord_2767508
  simp only [CollatzResearch.WordTrace]
  refine ⟨50469654628899321790851589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67292872838532429054468785 50469654628899321790851589)
  ·
    refine ⟨9463060242918622835784673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50469654628899321790851589 9463060242918622835784673)
    ·
      refine ⟨7097295182188967126838505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9463060242918622835784673 7097295182188967126838505)
      ·
        refine ⟨5322971386641725345128879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7097295182188967126838505 5322971386641725345128879)
        ·
          refine ⟨7984457079962588017693319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5322971386641725345128879 7984457079962588017693319)
          ·
            refine ⟨11976685619943882026539979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7984457079962588017693319 11976685619943882026539979)
            ·
              refine ⟨17965028429915823039809969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11976685619943882026539979 17965028429915823039809969)
              ·
                refine ⟨13473771322436867279857477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17965028429915823039809969 13473771322436867279857477)
                ·
                  refine ⟨2526332122956912614973277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13473771322436867279857477 2526332122956912614973277)
                  ·
                    refine ⟨947374546108842230614979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526332122956912614973277 947374546108842230614979)
                    ·
                      rfl

theorem cell22_2767508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2767508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767508 prefixEnd_2767508 := by exact prefixLift 2767508
  have htrace : WordTrace (prefixWord ++ tailWord_2767508) baseStart_2767508 baseEnd_2767508 := by
    simpa [prefixWord, tailWord_2767508, baseEnd_2767508] using wordTrace_append hprefix tailTrace_2767508
  have hstable : (prefixWord ++ tailWord_2767508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767508).length < 2 ^ (prefixWord ++ tailWord_2767508).sum := by decide
  have hdescent : baseEnd_2767508 < baseStart_2767508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767521 : List Nat := [1, 2, 3, 3, 3, 2, 8]
def baseStart_2767521 : Nat := 118140960795 + 2767521 * 2 ^ 59
def prefixEnd_2767521 : Nat := 4983230072969 + 3 ^ 40 * 2767521 * 2
def baseEnd_2767521 : Nat := 35088110973130167779257

theorem tailTrace_2767521 : CollatzResearch.WordTrace tailWord_2767521 prefixEnd_2767521 35088110973130167779257 := by
  unfold tailWord_2767521
  simp only [CollatzResearch.WordTrace]
  refine ⟨100939783406751546801926417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67293188937834364534617611 100939783406751546801926417)
  ·
    refine ⟨75704837555063660101444813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100939783406751546801926417 75704837555063660101444813)
    ·
      refine ⟨28389314083148872538041805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75704837555063660101444813 28389314083148872538041805)
      ·
        refine ⟨10645992781180827201765677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28389314083148872538041805 10645992781180827201765677)
        ·
          refine ⟨3992247292942810200662129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10645992781180827201765677 3992247292942810200662129)
          ·
            refine ⟨2994185469707107650496597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992247292942810200662129 2994185469707107650496597)
            ·
              refine ⟨35088110973130167779257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2994185469707107650496597 35088110973130167779257)
              ·
                rfl

theorem cell22_2767521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 8].length) (baseStart_2767521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767521 prefixEnd_2767521 := by exact prefixLift 2767521
  have htrace : WordTrace (prefixWord ++ tailWord_2767521) baseStart_2767521 baseEnd_2767521 := by
    simpa [prefixWord, tailWord_2767521, baseEnd_2767521] using wordTrace_append hprefix tailTrace_2767521
  have hstable : (prefixWord ++ tailWord_2767521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767521).length < 2 ^ (prefixWord ++ tailWord_2767521).sum := by decide
  have hdescent : baseEnd_2767521 < baseStart_2767521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767527 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 4]
def baseStart_2767527 : Nat := 118140960795 + 2767527 * 2 ^ 59
def prefixEnd_2767527 : Nat := 4983230072969 + 3 ^ 40 * 2767527 * 2
def baseEnd_2767527 : Nat := 315793683399044171463307

theorem tailTrace_2767527 : CollatzResearch.WordTrace tailWord_2767527 prefixEnd_2767527 315793683399044171463307 := by
  unfold tailWord_2767527
  simp only [CollatzResearch.WordTrace]
  refine ⟨100940002244729809826644835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67293334829819873217763223 100940002244729809826644835)
  ·
    refine ⟨151410003367094714739967253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100940002244729809826644835 151410003367094714739967253)
    ·
      refine ⟨7097343907832564753435965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151410003367094714739967253 7097343907832564753435965)
      ·
        refine ⟨2661503965437211782538487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7097343907832564753435965 2661503965437211782538487)
        ·
          refine ⟨3992255948155817673807731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661503965437211782538487 3992255948155817673807731)
          ·
            refine ⟨5988383922233726510711597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992255948155817673807731 5988383922233726510711597)
            ·
              refine ⟨2245643970837647441516849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5988383922233726510711597 2245643970837647441516849)
              ·
                refine ⟨1684232978128235581137637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245643970837647441516849 1684232978128235581137637)
                ·
                  refine ⟨315793683399044171463307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684232978128235581137637 315793683399044171463307)
                  ·
                    rfl

theorem cell22_2767527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 4].length) (baseStart_2767527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767527 prefixEnd_2767527 := by exact prefixLift 2767527
  have htrace : WordTrace (prefixWord ++ tailWord_2767527) baseStart_2767527 baseEnd_2767527 := by
    simpa [prefixWord, tailWord_2767527, baseEnd_2767527] using wordTrace_append hprefix tailTrace_2767527
  have hstable : (prefixWord ++ tailWord_2767527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767527).length < 2 ^ (prefixWord ++ tailWord_2767527).sum := by decide
  have hdescent : baseEnd_2767527 < baseStart_2767527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767542 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2767542 : Nat := 118140960795 + 2767542 * 2 ^ 59
def prefixEnd_2767542 : Nat := 4983230072969 + 3 ^ 40 * 2767542 * 2
def baseEnd_2767542 : Nat := 947386185003677475264875

theorem tailTrace_2767542 : CollatzResearch.WordTrace tailWord_2767542 prefixEnd_2767542 947386185003677475264875 := by
  unfold tailWord_2767542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308784333729716711777555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67293699559783644925627253 6308784333729716711777555)
  ·
    refine ⟨9463176500594575067666333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6308784333729716711777555 9463176500594575067666333)
    ·
      refine ⟨3548691187722965650374875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9463176500594575067666333 3548691187722965650374875)
      ·
        refine ⟨5323036781584448475562313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3548691187722965650374875 5323036781584448475562313)
        ·
          refine ⟨3992277586188336356671735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5323036781584448475562313 3992277586188336356671735)
          ·
            refine ⟨5988416379282504535007603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992277586188336356671735 5988416379282504535007603)
            ·
              refine ⟨8982624568923756802511405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5988416379282504535007603 8982624568923756802511405)
              ·
                refine ⟨3368484213346408800941777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8982624568923756802511405 3368484213346408800941777)
                ·
                  refine ⟨2526363160009806600706333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368484213346408800941777 2526363160009806600706333)
                  ·
                    refine ⟨947386185003677475264875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526363160009806600706333 947386185003677475264875)
                    ·
                      rfl

theorem cell22_2767542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2767542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767542 prefixEnd_2767542 := by exact prefixLift 2767542
  have htrace : WordTrace (prefixWord ++ tailWord_2767542) baseStart_2767542 baseEnd_2767542 := by
    simpa [prefixWord, tailWord_2767542, baseEnd_2767542] using wordTrace_append hprefix tailTrace_2767542
  have hstable : (prefixWord ++ tailWord_2767542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767542).length < 2 ^ (prefixWord ++ tailWord_2767542).sum := by decide
  have hdescent : baseEnd_2767542 < baseStart_2767542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767587 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 1, 3]
def baseStart_2767587 : Nat := 118140960795 + 2767587 * 2 ^ 59
def prefixEnd_2767587 : Nat := 4983230072969 + 3 ^ 40 * 2767587 * 2
def baseEnd_2767587 : Nat := 947401589423312357889737

theorem tailTrace_2767587 : CollatzResearch.WordTrace tailWord_2767587 prefixEnd_2767587 947401589423312357889737 := by
  unfold tailWord_2767587
  simp only [CollatzResearch.WordTrace]
  refine ⟨100942190624512440073829015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67294793749674960049219343 100942190624512440073829015)
  ·
    refine ⟨151413285936768660110743523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100942190624512440073829015 151413285936768660110743523)
    ·
      refine ⟨227119928905152990166115285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151413285936768660110743523 227119928905152990166115285)
      ·
        refine ⟨5323123333714523207018327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 227119928905152990166115285 5323123333714523207018327)
        ·
          refine ⟨7984685000571784810527491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323123333714523207018327 7984685000571784810527491)
          ·
            refine ⟨11977027500857677215791237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7984685000571784810527491 11977027500857677215791237)
            ·
              refine ⟨2245692656410814477960857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11977027500857677215791237 2245692656410814477960857)
              ·
                refine ⟨1684269492308110858470643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245692656410814477960857 1684269492308110858470643)
                ·
                  refine ⟨2526404238462166287705965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684269492308110858470643 2526404238462166287705965)
                  ·
                    refine ⟨947401589423312357889737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526404238462166287705965 947401589423312357889737)
                    ·
                      rfl

theorem cell22_2767587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 3].length) (baseStart_2767587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767587 prefixEnd_2767587 := by exact prefixLift 2767587
  have htrace : WordTrace (prefixWord ++ tailWord_2767587) baseStart_2767587 baseEnd_2767587 := by
    simpa [prefixWord, tailWord_2767587, baseEnd_2767587] using wordTrace_append hprefix tailTrace_2767587
  have hstable : (prefixWord ++ tailWord_2767587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767587).length < 2 ^ (prefixWord ++ tailWord_2767587).sum := by decide
  have hdescent : baseEnd_2767587 < baseStart_2767587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767626 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2767626 : Nat := 118140960795 + 2767626 * 2 ^ 59
def prefixEnd_2767626 : Nat := 4983230072969 + 3 ^ 40 * 2767626 * 2
def baseEnd_2767626 : Nat := 947414939920329256164617

theorem tailTrace_2767626 : CollatzResearch.WordTrace tailWord_2767626 prefixEnd_2767626 947414939920329256164617 := by
  unfold tailWord_2767626
  simp only [CollatzResearch.WordTrace]
  refine ⟨25235903267842787433624683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67295742047580766489665821 25235903267842787433624683)
  ·
    refine ⟨37853854901764181150437025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25235903267842787433624683 37853854901764181150437025)
    ·
      refine ⟨28390391176323135862827769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37853854901764181150437025 28390391176323135862827769)
      ·
        refine ⟨21292793382242351897120827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28390391176323135862827769 21292793382242351897120827)
        ·
          refine ⟨31939190073363527845681241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21292793382242351897120827 31939190073363527845681241)
          ·
            refine ⟨23954392555022645884260931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31939190073363527845681241 23954392555022645884260931)
            ·
              refine ⟨35931588832533968826391397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23954392555022645884260931 35931588832533968826391397)
              ·
                refine ⟨6737172906100119154948387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35931588832533968826391397 6737172906100119154948387)
                ·
                  refine ⟨10105759359150178732422581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6737172906100119154948387 10105759359150178732422581)
                  ·
                    refine ⟨947414939920329256164617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10105759359150178732422581 947414939920329256164617)
                    ·
                      rfl

theorem cell22_2767626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2767626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767626 prefixEnd_2767626 := by exact prefixLift 2767626
  have htrace : WordTrace (prefixWord ++ tailWord_2767626) baseStart_2767626 baseEnd_2767626 := by
    simpa [prefixWord, tailWord_2767626, baseEnd_2767626] using wordTrace_append hprefix tailTrace_2767626
  have hstable : (prefixWord ++ tailWord_2767626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767626).length < 2 ^ (prefixWord ++ tailWord_2767626).sum := by decide
  have hdescent : baseEnd_2767626 < baseStart_2767626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767645 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 6]
def baseStart_2767645 : Nat := 118140960795 + 2767645 * 2 ^ 59
def prefixEnd_2767645 : Nat := 4983230072969 + 3 ^ 40 * 2767645 * 2
def baseEnd_2767645 : Nat := 315807148002873179979853

theorem tailTrace_2767645 : CollatzResearch.WordTrace tailWord_2767645 prefixEnd_2767645 315807148002873179979853 := by
  unfold tailWord_2767645
  simp only [CollatzResearch.WordTrace]
  refine ⟨100944306058302315979440389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67296204038868210652960259 100944306058302315979440389)
  ·
    refine ⟨18927057385931684246145073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100944306058302315979440389 18927057385931684246145073)
    ·
      refine ⟨14195293039448763184608805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18927057385931684246145073 14195293039448763184608805)
      ·
        refine ⟨2661617444896643097114151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14195293039448763184608805 2661617444896643097114151)
        ·
          refine ⟨3992426167344964645671227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661617444896643097114151 3992426167344964645671227)
          ·
            refine ⟨5988639251017446968506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992426167344964645671227 5988639251017446968506841)
            ·
              refine ⟨4491479438263085226380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5988639251017446968506841 4491479438263085226380131)
              ·
                refine ⟨6737219157394627839570197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491479438263085226380131 6737219157394627839570197)
                ·
                  refine ⟨315807148002873179979853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6737219157394627839570197 315807148002873179979853)
                  ·
                    rfl

theorem cell22_2767645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_2767645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767645 prefixEnd_2767645 := by exact prefixLift 2767645
  have htrace : WordTrace (prefixWord ++ tailWord_2767645) baseStart_2767645 baseEnd_2767645 := by
    simpa [prefixWord, tailWord_2767645, baseEnd_2767645] using wordTrace_append hprefix tailTrace_2767645
  have hstable : (prefixWord ++ tailWord_2767645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767645).length < 2 ^ (prefixWord ++ tailWord_2767645).sum := by decide
  have hdescent : baseEnd_2767645 < baseStart_2767645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767656 : List Nat := [2, 1, 5, 1, 1, 1, 2, 9]
def baseStart_2767656 : Nat := 118140960795 + 2767656 * 2 ^ 59
def prefixEnd_2767656 : Nat := 4983230072969 + 3 ^ 40 * 2767656 * 2
def baseEnd_2767656 : Nat := 105269467725935464212725

theorem tailTrace_2767656 : CollatzResearch.WordTrace tailWord_2767656 prefixEnd_2767656 105269467725935464212725 := by
  unfold tailWord_2767656
  simp only [CollatzResearch.WordTrace]
  refine ⟨50472353630631232429045411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67296471507508309905393881 50472353630631232429045411)
  ·
    refine ⟨75708530445946848643568117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50472353630631232429045411 75708530445946848643568117)
    ·
      refine ⟨7097674729307517060334511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75708530445946848643568117 7097674729307517060334511)
      ·
        refine ⟨10646512093961275590501767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097674729307517060334511 10646512093961275590501767)
        ·
          refine ⟨15969768140941913385752651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10646512093961275590501767 15969768140941913385752651)
          ·
            refine ⟨23954652211412870078628977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15969768140941913385752651 23954652211412870078628977)
            ·
              refine ⟨17965989158559652558971733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23954652211412870078628977 17965989158559652558971733)
              ·
                refine ⟨105269467725935464212725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17965989158559652558971733 105269467725935464212725)
                ·
                  rfl

theorem cell22_2767656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_2767656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767656 prefixEnd_2767656 := by exact prefixLift 2767656
  have htrace : WordTrace (prefixWord ++ tailWord_2767656) baseStart_2767656 baseEnd_2767656 := by
    simpa [prefixWord, tailWord_2767656, baseEnd_2767656] using wordTrace_append hprefix tailTrace_2767656
  have hstable : (prefixWord ++ tailWord_2767656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767656).length < 2 ^ (prefixWord ++ tailWord_2767656).sum := by decide
  have hdescent : baseEnd_2767656 < baseStart_2767656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767660 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_2767660 : Nat := 118140960795 + 2767660 * 2 ^ 59
def prefixEnd_2767660 : Nat := 4983230072969 + 3 ^ 40 * 2767660 * 2
def baseEnd_2767660 : Nat := 947426578815164500814513

theorem tailTrace_2767660 : CollatzResearch.WordTrace tailWord_2767660 prefixEnd_2767660 947426578815164500814513 := by
  unfold tailWord_2767660
  simp only [CollatzResearch.WordTrace]
  refine ⟨50472426576623986770618217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67296568768831982360824289 50472426576623986770618217)
  ·
    refine ⟨37854319932467990077963663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50472426576623986770618217 37854319932467990077963663)
    ·
      refine ⟨56781479898701985116945495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37854319932467990077963663 56781479898701985116945495)
      ·
        refine ⟨85172219848052977675418243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56781479898701985116945495 85172219848052977675418243)
        ·
          refine ⟨127758329772079466513127365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85172219848052977675418243 127758329772079466513127365)
          ·
            refine ⟨23954686832264899971211381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127758329772079466513127365 23954686832264899971211381)
            ·
              refine ⟨2245751890524834372301067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23954686832264899971211381 2245751890524834372301067)
              ·
                refine ⟨3368627835787251558451601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245751890524834372301067 3368627835787251558451601)
                ·
                  refine ⟨2526470876840438668838701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368627835787251558451601 2526470876840438668838701)
                  ·
                    refine ⟨947426578815164500814513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526470876840438668838701 947426578815164500814513)
                    ·
                      rfl

theorem cell22_2767660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_2767660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767660 prefixEnd_2767660 := by exact prefixLift 2767660
  have htrace : WordTrace (prefixWord ++ tailWord_2767660) baseStart_2767660 baseEnd_2767660 := by
    simpa [prefixWord, tailWord_2767660, baseEnd_2767660] using wordTrace_append hprefix tailTrace_2767660
  have hstable : (prefixWord ++ tailWord_2767660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767660).length < 2 ^ (prefixWord ++ tailWord_2767660).sum := by decide
  have hdescent : baseEnd_2767660 < baseStart_2767660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767701 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 7]
def baseStart_2767701 : Nat := 118140960795 + 2767701 * 2 ^ 59
def prefixEnd_2767701 : Nat := 4983230072969 + 3 ^ 40 * 2767701 * 2
def baseEnd_2767701 : Nat := 315813537984351353513129

theorem tailTrace_2767701 : CollatzResearch.WordTrace tailWord_2767701 prefixEnd_2767701 315813537984351353513129 := by
  unfold tailWord_2767701
  simp only [CollatzResearch.WordTrace]
  refine ⟨100946348546099437543478957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67297565697399625028985971 100946348546099437543478957)
  ·
    refine ⟨37854880704787289078804609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100946348546099437543478957 37854880704787289078804609)
    ·
      refine ⟨28391160528590466809103457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37854880704787289078804609 28391160528590466809103457)
      ·
        refine ⟨21293370396442850106827593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28391160528590466809103457 21293370396442850106827593)
        ·
          refine ⟨15970027797332137580120695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21293370396442850106827593 15970027797332137580120695)
          ·
            refine ⟨23955041695998206370181043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15970027797332137580120695 23955041695998206370181043)
            ·
              refine ⟨35932562543997309555271565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23955041695998206370181043 35932562543997309555271565)
              ·
                refine ⟨13474710953998991083226837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35932562543997309555271565 13474710953998991083226837)
                ·
                  refine ⟨315813537984351353513129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13474710953998991083226837 315813537984351353513129)
                  ·
                    rfl

theorem cell22_2767701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_2767701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767701 prefixEnd_2767701 := by exact prefixLift 2767701
  have htrace : WordTrace (prefixWord ++ tailWord_2767701) baseStart_2767701 baseEnd_2767701 := by
    simpa [prefixWord, tailWord_2767701, baseEnd_2767701] using wordTrace_append hprefix tailTrace_2767701
  have hstable : (prefixWord ++ tailWord_2767701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767701).length < 2 ^ (prefixWord ++ tailWord_2767701).sum := by decide
  have hdescent : baseEnd_2767701 < baseStart_2767701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767705 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_2767705 : Nat := 118140960795 + 2767705 * 2 ^ 59
def prefixEnd_2767705 : Nat := 4983230072969 + 3 ^ 40 * 2767705 * 2
def baseEnd_2767705 : Nat := 947441983234799383439375

theorem tailTrace_2767705 : CollatzResearch.WordTrace tailWord_2767705 prefixEnd_2767705 947441983234799383439375 := by
  unfold tailWord_2767705
  simp only [CollatzResearch.WordTrace]
  refine ⟨100946494438084946226624569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67297662958723297484416379 100946494438084946226624569)
  ·
    refine ⟨75709870828563709669968427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100946494438084946226624569 75709870828563709669968427)
    ·
      refine ⟨113564806242845564504952641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75709870828563709669968427 113564806242845564504952641)
      ·
        refine ⟨85173604682134173378714481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113564806242845564504952641 85173604682134173378714481)
        ·
          refine ⟨63880203511600630034035861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85173604682134173378714481 63880203511600630034035861)
          ·
            refine ⟨2994384539606279532845431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 63880203511600630034035861 2994384539606279532845431)
            ·
              refine ⟨4491576809409419299268147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994384539606279532845431 4491576809409419299268147)
              ·
                refine ⟨6737365214114128948902221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4491576809409419299268147 6737365214114128948902221)
                ·
                  refine ⟨2526511955292798355838333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6737365214114128948902221 2526511955292798355838333)
                  ·
                    refine ⟨947441983234799383439375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526511955292798355838333 947441983234799383439375)
                    ·
                      rfl

theorem cell22_2767705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_2767705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767705 prefixEnd_2767705 := by exact prefixLift 2767705
  have htrace : WordTrace (prefixWord ++ tailWord_2767705) baseStart_2767705 baseEnd_2767705 := by
    simpa [prefixWord, tailWord_2767705, baseEnd_2767705] using wordTrace_append hprefix tailTrace_2767705
  have hstable : (prefixWord ++ tailWord_2767705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767705).length < 2 ^ (prefixWord ++ tailWord_2767705).sum := by decide
  have hdescent : baseEnd_2767705 < baseStart_2767705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767761 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_2767761 : Nat := 118140960795 + 2767761 * 2 ^ 59
def prefixEnd_2767761 : Nat := 4983230072969 + 3 ^ 40 * 2767761 * 2
def baseEnd_2767761 : Nat := 947461153179233904039203

theorem tailTrace_2767761 : CollatzResearch.WordTrace tailWord_2767761 prefixEnd_2767761 947461153179233904039203 := by
  unfold tailWord_2767761
  simp only [CollatzResearch.WordTrace]
  refine ⟨100948536925882067790663137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67299024617254711860442091 100948536925882067790663137)
  ·
    refine ⟨75711402694411550842997353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100948536925882067790663137 75711402694411550842997353)
    ·
      refine ⟨56783552020808663132248015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75711402694411550842997353 56783552020808663132248015)
      ·
        refine ⟨85175328031212994698372023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56783552020808663132248015 85175328031212994698372023)
        ·
          refine ⟨127762992046819492047558035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85175328031212994698372023 127762992046819492047558035)
          ·
            refine ⟨191644488070229238071337053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127762992046819492047558035 191644488070229238071337053)
            ·
              refine ⟨71866683026335964276751395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191644488070229238071337053 71866683026335964276751395)
              ·
                refine ⟨107800024539503946415127093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71866683026335964276751395 107800024539503946415127093)
                ·
                  refine ⟨10106252300578494976418165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107800024539503946415127093 10106252300578494976418165)
                  ·
                    refine ⟨947461153179233904039203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10106252300578494976418165 947461153179233904039203)
                    ·
                      rfl

theorem cell22_2767761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_2767761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767761 prefixEnd_2767761 := by exact prefixLift 2767761
  have htrace : WordTrace (prefixWord ++ tailWord_2767761) baseStart_2767761 baseEnd_2767761 := by
    simpa [prefixWord, tailWord_2767761, baseEnd_2767761] using wordTrace_append hprefix tailTrace_2767761
  have hstable : (prefixWord ++ tailWord_2767761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767761).length < 2 ^ (prefixWord ++ tailWord_2767761).sum := by decide
  have hdescent : baseEnd_2767761 < baseStart_2767761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767829 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2767829 : Nat := 118140960795 + 2767829 * 2 ^ 59
def prefixEnd_2767829 : Nat := 4983230072969 + 3 ^ 40 * 2767829 * 2
def baseEnd_2767829 : Nat := 947484430968904393338995

theorem tailTrace_2767829 : CollatzResearch.WordTrace tailWord_2767829 prefixEnd_2767829 947484430968904393338995 := by
  unfold tailWord_2767829
  simp only [CollatzResearch.WordTrace]
  refine ⟨100951017089635715404138541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67300678059757143602759027 100951017089635715404138541)
  ·
    refine ⟨37856631408613393276551953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100951017089635715404138541 37856631408613393276551953)
    ·
      refine ⟨28392473556460044957413965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37856631408613393276551953 28392473556460044957413965)
      ·
        refine ⟨10647177583672516859030237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28392473556460044957413965 10647177583672516859030237)
        ·
          refine ⟨3992691593877193822136339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10647177583672516859030237 3992691593877193822136339)
          ·
            refine ⟨5989037390815790733204509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992691593877193822136339 5989037390815790733204509)
            ·
              refine ⟨2245889021555921524951691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5989037390815790733204509 2245889021555921524951691)
              ·
                refine ⟨3368833532333882287427537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245889021555921524951691 3368833532333882287427537)
                ·
                  refine ⟨2526625149250411715570653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3368833532333882287427537 2526625149250411715570653)
                  ·
                    refine ⟨947484430968904393338995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526625149250411715570653 947484430968904393338995)
                    ·
                      rfl

theorem cell22_2767829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2767829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767829 prefixEnd_2767829 := by exact prefixLift 2767829
  have htrace : WordTrace (prefixWord ++ tailWord_2767829) baseStart_2767829 baseEnd_2767829 := by
    simpa [prefixWord, tailWord_2767829, baseEnd_2767829] using wordTrace_append hprefix tailTrace_2767829
  have hstable : (prefixWord ++ tailWord_2767829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767829).length < 2 ^ (prefixWord ++ tailWord_2767829).sum := by decide
  have hdescent : baseEnd_2767829 < baseStart_2767829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767842 : List Nat := [3, 3, 3, 1, 1, 1, 4, 6]
def baseStart_2767842 : Nat := 118140960795 + 2767842 * 2 ^ 59
def prefixEnd_2767842 : Nat := 4983230072969 + 3 ^ 40 * 2767842 * 2
def baseEnd_2767842 : Nat := 105276542348286299195995

theorem tailTrace_2767842 : CollatzResearch.WordTrace tailWord_2767842 prefixEnd_2767842 105276542348286299195995 := by
  unfold tailWord_2767842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25237872809647154656090445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67300994159059079082907853 25237872809647154656090445)
  ·
    refine ⟨9464202303617682996033917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25237872809647154656090445 9464202303617682996033917)
    ·
      refine ⟨3549075863856631123512719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9464202303617682996033917 3549075863856631123512719)
      ·
        refine ⟨5323613795784946685269079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549075863856631123512719 5323613795784946685269079)
        ·
          refine ⟨7985420693677420027903619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323613795784946685269079 7985420693677420027903619)
          ·
            refine ⟨11978131040516130041855429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7985420693677420027903619 11978131040516130041855429)
            ·
              refine ⟨2245899570096774382847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11978131040516130041855429 2245899570096774382847893)
              ·
                refine ⟨105276542348286299195995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2245899570096774382847893 105276542348286299195995)
                ·
                  rfl

theorem cell22_2767842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_2767842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767842 prefixEnd_2767842 := by exact prefixLift 2767842
  have htrace : WordTrace (prefixWord ++ tailWord_2767842) baseStart_2767842 baseEnd_2767842 := by
    simpa [prefixWord, tailWord_2767842, baseEnd_2767842] using wordTrace_append hprefix tailTrace_2767842
  have hstable : (prefixWord ++ tailWord_2767842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767842).length < 2 ^ (prefixWord ++ tailWord_2767842).sum := by decide
  have hdescent : baseEnd_2767842 < baseStart_2767842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767898 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_2767898 : Nat := 118140960795 + 2767898 * 2 ^ 59
def prefixEnd_2767898 : Nat := 4983230072969 + 3 ^ 40 * 2767898 * 2
def baseEnd_2767898 : Nat := 315836017026337071121261

theorem tailTrace_2767898 : CollatzResearch.WordTrace tailWord_2767898 prefixEnd_2767898 315836017026337071121261 := by
  unfold tailWord_2767898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25238383431596435047100087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67302355817590493458933565 25238383431596435047100087)
  ·
    refine ⟨37857575147394652570650131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25238383431596435047100087 37857575147394652570650131)
    ·
      refine ⟨56786362721091978855975197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37857575147394652570650131 56786362721091978855975197)
      ·
        refine ⟨21294886020409492070990699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56786362721091978855975197 21294886020409492070990699)
        ·
          refine ⟨31942329030614238106486049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21294886020409492070990699 31942329030614238106486049)
          ·
            refine ⟨23956746772960678579864537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31942329030614238106486049 23956746772960678579864537)
            ·
              refine ⟨17967560079720508934898403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23956746772960678579864537 17967560079720508934898403)
              ·
                refine ⟨26951340119580763402347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17967560079720508934898403 26951340119580763402347605)
                ·
                  refine ⟨315836017026337071121261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26951340119580763402347605 315836017026337071121261)
                  ·
                    rfl

theorem cell22_2767898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_2767898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767898 prefixEnd_2767898 := by exact prefixLift 2767898
  have htrace : WordTrace (prefixWord ++ tailWord_2767898) baseStart_2767898 baseEnd_2767898 := by
    simpa [prefixWord, tailWord_2767898, baseEnd_2767898] using wordTrace_append hprefix tailTrace_2767898
  have hstable : (prefixWord ++ tailWord_2767898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767898).length < 2 ^ (prefixWord ++ tailWord_2767898).sum := by decide
  have hdescent : baseEnd_2767898 < baseStart_2767898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767915 : List Nat := [1, 1, 1, 1, 2, 1, 6, 5, 4]
def baseStart_2767915 : Nat := 118140960795 + 2767915 * 2 ^ 59
def prefixEnd_2767915 : Nat := 4983230072969 + 3 ^ 40 * 2767915 * 2
def baseEnd_2767915 : Nat := 315837956842142945229577

theorem tailTrace_2767915 : CollatzResearch.WordTrace tailWord_2767915 prefixEnd_2767915 315837956842142945229577 := by
  unfold tailWord_2767915
  simp only [CollatzResearch.WordTrace]
  refine ⟨100954153767324152091769199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67302769178216101394512799 100954153767324152091769199)
  ·
    refine ⟨151431230650986228137653799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100954153767324152091769199 151431230650986228137653799)
    ·
      refine ⟨227146845976479342206480699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151431230650986228137653799 227146845976479342206480699)
      ·
        refine ⟨340720268964719013309721049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227146845976479342206480699 340720268964719013309721049)
        ·
          refine ⟨255540201723539259982290787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340720268964719013309721049 255540201723539259982290787)
          ·
            refine ⟨383310302585308889973436181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255540201723539259982290787 383310302585308889973436181)
            ·
              refine ⟨17967670433686354217504821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 383310302585308889973436181 17967670433686354217504821)
              ·
                refine ⟨1684469103158095707891077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17967670433686354217504821 1684469103158095707891077)
                ·
                  refine ⟨315837956842142945229577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684469103158095707891077 315837956842142945229577)
                  ·
                    rfl

theorem cell22_2767915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 4].length) (baseStart_2767915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767915 prefixEnd_2767915 := by exact prefixLift 2767915
  have htrace : WordTrace (prefixWord ++ tailWord_2767915) baseStart_2767915 baseEnd_2767915 := by
    simpa [prefixWord, tailWord_2767915, baseEnd_2767915] using wordTrace_append hprefix tailTrace_2767915
  have hstable : (prefixWord ++ tailWord_2767915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767915).length < 2 ^ (prefixWord ++ tailWord_2767915).sum := by decide
  have hdescent : baseEnd_2767915 < baseStart_2767915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767930 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_2767930 : Nat := 118140960795 + 2767930 * 2 ^ 59
def prefixEnd_2767930 : Nat := 4983230072969 + 3 ^ 40 * 2767930 * 2
def baseEnd_2767930 : Nat := 947519005332973796563685

theorem tailTrace_2767930 : CollatzResearch.WordTrace tailWord_2767930 prefixEnd_2767930 947519005332973796563685 := by
  unfold tailWord_2767930
  simp only [CollatzResearch.WordTrace]
  refine ⟨25238675215567452413391311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67303133908179873102376829 25238675215567452413391311)
  ·
    refine ⟨37858012823351178620086967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25238675215567452413391311 37858012823351178620086967)
    ·
      refine ⟨56787019235026767930130451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37858012823351178620086967 56787019235026767930130451)
      ·
        refine ⟨85180528852540151895195677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56787019235026767930130451 85180528852540151895195677)
        ·
          refine ⟨31942698319702556960698379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85180528852540151895195677 31942698319702556960698379)
          ·
            refine ⟨47914047479553835441047569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31942698319702556960698379 47914047479553835441047569)
            ·
              refine ⟨35935535609665376580785677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47914047479553835441047569 35935535609665376580785677)
              ·
                refine ⟨13475825853624516217794629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35935535609665376580785677 13475825853624516217794629)
                ·
                  refine ⟨2526717347554596790836493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13475825853624516217794629 2526717347554596790836493)
                  ·
                    refine ⟨947519005332973796563685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526717347554596790836493 947519005332973796563685)
                    ·
                      rfl

theorem cell22_2767930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_2767930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767930 prefixEnd_2767930 := by exact prefixLift 2767930
  have htrace : WordTrace (prefixWord ++ tailWord_2767930) baseStart_2767930 baseEnd_2767930 := by
    simpa [prefixWord, tailWord_2767930, baseEnd_2767930] using wordTrace_append hprefix tailTrace_2767930
  have hstable : (prefixWord ++ tailWord_2767930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767930).length < 2 ^ (prefixWord ++ tailWord_2767930).sum := by decide
  have hdescent : baseEnd_2767930 < baseStart_2767930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767932 : List Nat := [2, 2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_2767932 : Nat := 118140960795 + 2767932 * 2 ^ 59
def prefixEnd_2767932 : Nat := 4983230072969 + 3 ^ 40 * 2767932 * 2
def baseEnd_2767932 : Nat := 315839896657948819337893

theorem tailTrace_2767932 : CollatzResearch.WordTrace tailWord_2767932 prefixEnd_2767932 315839896657948819337893 := by
  unfold tailWord_2767932
  simp only [CollatzResearch.WordTrace]
  refine ⟨50477386904131281997569025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67303182538841709330092033 50477386904131281997569025)
  ·
    refine ⟨37858040178098461498176769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50477386904131281997569025 37858040178098461498176769)
    ·
      refine ⟨28393530133573846123632577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37858040178098461498176769 28393530133573846123632577)
      ·
        refine ⟨21295147600180384592724433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28393530133573846123632577 21295147600180384592724433)
        ·
          refine ⟨15971360700135288444543325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21295147600180384592724433 15971360700135288444543325)
          ·
            refine ⟨5989260262550733166703747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15971360700135288444543325 5989260262550733166703747)
            ·
              refine ⟨8983890393826099750055621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989260262550733166703747 8983890393826099750055621)
              ·
                refine ⟨1684479448842393703135429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8983890393826099750055621 1684479448842393703135429)
                ·
                  refine ⟨315839896657948819337893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684479448842393703135429 315839896657948819337893)
                  ·
                    rfl

theorem cell22_2767932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_2767932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767932 prefixEnd_2767932 := by exact prefixLift 2767932
  have htrace : WordTrace (prefixWord ++ tailWord_2767932) baseStart_2767932 baseEnd_2767932 := by
    simpa [prefixWord, tailWord_2767932, baseEnd_2767932] using wordTrace_append hprefix tailTrace_2767932
  have hstable : (prefixWord ++ tailWord_2767932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767932).length < 2 ^ (prefixWord ++ tailWord_2767932).sum := by decide
  have hdescent : baseEnd_2767932 < baseStart_2767932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767960 : List Nat := [2, 1, 2, 2, 1, 3, 5, 6]
def baseStart_2767960 : Nat := 118140960795 + 2767960 * 2 ^ 59
def prefixEnd_2767960 : Nat := 4983230072969 + 3 ^ 40 * 2767960 * 2
def baseEnd_2767960 : Nat := 105281030549562635368177

theorem tailTrace_2767960 : CollatzResearch.WordTrace tailWord_2767960 prefixEnd_2767960 105281030549562635368177 := by
  unfold tailWord_2767960
  simp only [CollatzResearch.WordTrace]
  refine ⟨50477897526080562388578667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67303863368107416518104889 50477897526080562388578667)
  ·
    refine ⟨75716846289120843582868001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50477897526080562388578667 75716846289120843582868001)
    ·
      refine ⟨56787634716840632687151001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75716846289120843582868001 56787634716840632687151001)
      ·
        refine ⟨42590726037630474515363251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56787634716840632687151001 42590726037630474515363251)
        ·
          refine ⟨63886089056445711773044877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42590726037630474515363251 63886089056445711773044877)
          ·
            refine ⟨23957283396167141914891829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63886089056445711773044877 23957283396167141914891829)
            ·
              refine ⟨2245995318390669554521109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23957283396167141914891829 2245995318390669554521109)
              ·
                refine ⟨105281030549562635368177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2245995318390669554521109 105281030549562635368177)
                ·
                  rfl

theorem cell22_2767960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_2767960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767960 prefixEnd_2767960 := by exact prefixLift 2767960
  have htrace : WordTrace (prefixWord ++ tailWord_2767960) baseStart_2767960 baseEnd_2767960 := by
    simpa [prefixWord, tailWord_2767960, baseEnd_2767960] using wordTrace_append hprefix tailTrace_2767960
  have hstable : (prefixWord ++ tailWord_2767960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767960).length < 2 ^ (prefixWord ++ tailWord_2767960).sum := by decide
  have hdescent : baseEnd_2767960 < baseStart_2767960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767966 : List Nat := [4, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2767966 : Nat := 118140960795 + 2767966 * 2 ^ 59
def prefixEnd_2767966 : Nat := 4983230072969 + 3 ^ 40 * 2767966 * 2
def baseEnd_2767966 : Nat := 315843776289560567554525

theorem tailTrace_2767966 : CollatzResearch.WordTrace tailWord_2767966 prefixEnd_2767966 315843776289560567554525 := by
  unfold tailWord_2767966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12619501736267423475234469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67304009260092925201250501 12619501736267423475234469)
  ·
    refine ⟨2366156575550141901606463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12619501736267423475234469 2366156575550141901606463)
    ·
      refine ⟨3549234863325212852409695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2366156575550141901606463 3549234863325212852409695)
      ·
        refine ⟨5323852294987819278614543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549234863325212852409695 5323852294987819278614543)
        ·
          refine ⟨7985778442481728917921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323852294987819278614543 7985778442481728917921815)
          ·
            refine ⟨11978667663722593376882723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7985778442481728917921815 11978667663722593376882723)
            ·
              refine ⟨17968001495583890065324085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11978667663722593376882723 17968001495583890065324085)
              ·
                refine ⟨1684500140210989693624133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17968001495583890065324085 1684500140210989693624133)
                ·
                  refine ⟨315843776289560567554525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684500140210989693624133 315843776289560567554525)
                  ·
                    rfl

theorem cell22_2767966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2767966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767966 prefixEnd_2767966 := by exact prefixLift 2767966
  have htrace : WordTrace (prefixWord ++ tailWord_2767966) baseStart_2767966 baseEnd_2767966 := by
    simpa [prefixWord, tailWord_2767966, baseEnd_2767966] using wordTrace_append hprefix tailTrace_2767966
  have hstable : (prefixWord ++ tailWord_2767966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767966).length < 2 ^ (prefixWord ++ tailWord_2767966).sum := by decide
  have hdescent : baseEnd_2767966 < baseStart_2767966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2767998 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2767998 : Nat := 118140960795 + 2767998 * 2 ^ 59
def prefixEnd_2767998 : Nat := 4983230072969 + 3 ^ 40 * 2767998 * 2
def baseEnd_2767998 : Nat := 947542283122644285863477

theorem tailTrace_2767998 : CollatzResearch.WordTrace tailWord_2767998 prefixEnd_2767998 947542283122644285863477 := by
  unfold tailWord_2767998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12619647628252932158380081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67304787350682304844693765 12619647628252932158380081)
  ·
    refine ⟨9464735721189699118785061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12619647628252932158380081 9464735721189699118785061)
    ·
      refine ⟨1774637947723068584772199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9464735721189699118785061 1774637947723068584772199)
      ·
        refine ⟨2661956921584602877158299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774637947723068584772199 2661956921584602877158299)
        ·
          refine ⟨3992935382376904315737449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661956921584602877158299 3992935382376904315737449)
          ·
            refine ⟨2994701536782678236803087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3992935382376904315737449 2994701536782678236803087)
            ·
              refine ⟨4492052305174017355204631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2994701536782678236803087 4492052305174017355204631)
              ·
                refine ⟨6738078457761026032806947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492052305174017355204631 6738078457761026032806947)
                ·
                  refine ⟨10107117686641539049210421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738078457761026032806947 10107117686641539049210421)
                  ·
                    refine ⟨947542283122644285863477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10107117686641539049210421 947542283122644285863477)
                    ·
                      rfl

theorem cell22_2767998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2767998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2767998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2767998 prefixEnd_2767998 := by exact prefixLift 2767998
  have htrace : WordTrace (prefixWord ++ tailWord_2767998) baseStart_2767998 baseEnd_2767998 := by
    simpa [prefixWord, tailWord_2767998, baseEnd_2767998] using wordTrace_append hprefix tailTrace_2767998
  have hstable : (prefixWord ++ tailWord_2767998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2767998).length < 2 ^ (prefixWord ++ tailWord_2767998).sum := by decide
  have hdescent : baseEnd_2767998 < baseStart_2767998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2767998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768026 : List Nat := [3, 1, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_2768026 : Nat := 118140960795 + 2768026 * 2 ^ 59
def prefixEnd_2768026 : Nat := 4983230072969 + 3 ^ 40 * 2768026 * 2
def baseEnd_2768026 : Nat := 947551868094861546163391

theorem tailTrace_2768026 : CollatzResearch.WordTrace tailWord_2768026 prefixEnd_2768026 947551868094861546163391 := by
  unfold tailWord_2768026
  simp only [CollatzResearch.WordTrace]
  refine ⟨25239550567480504512264983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67305468179948012032706621 25239550567480504512264983)
  ·
    refine ⟨37859325851220756768397475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25239550567480504512264983 37859325851220756768397475)
    ·
      refine ⟨56788988776831135152596213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37859325851220756768397475 56788988776831135152596213)
      ·
        refine ⟨5323967697827918920555895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56788988776831135152596213 5323967697827918920555895)
        ·
          refine ⟨7985951546741878380833843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323967697827918920555895 7985951546741878380833843)
          ·
            refine ⟨11978927320112817571250765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7985951546741878380833843 11978927320112817571250765)
            ·
              refine ⟨4492097745042306589219037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11978927320112817571250765 4492097745042306589219037)
              ·
                refine ⟨1684536654390864970957139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4492097745042306589219037 1684536654390864970957139)
                ·
                  refine ⟨2526804981586297456435709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684536654390864970957139 2526804981586297456435709)
                  ·
                    refine ⟨947551868094861546163391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526804981586297456435709 947551868094861546163391)
                    ·
                      rfl

theorem cell22_2768026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_2768026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768026 prefixEnd_2768026 := by exact prefixLift 2768026
  have htrace : WordTrace (prefixWord ++ tailWord_2768026) baseStart_2768026 baseEnd_2768026 := by
    simpa [prefixWord, tailWord_2768026, baseEnd_2768026] using wordTrace_append hprefix tailTrace_2768026
  have hstable : (prefixWord ++ tailWord_2768026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768026).length < 2 ^ (prefixWord ++ tailWord_2768026).sum := by decide
  have hdescent : baseEnd_2768026 < baseStart_2768026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768082 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2768082 : Nat := 118140960795 + 2768082 * 2 ^ 59
def prefixEnd_2768082 : Nat := 4983230072969 + 3 ^ 40 * 2768082 * 2
def baseEnd_2768082 : Nat := 947571038039296066763219

theorem tailTrace_2768082 : CollatzResearch.WordTrace tailWord_2768082 prefixEnd_2768082 947571038039296066763219 := by
  unfold tailWord_2768082
  simp only [CollatzResearch.WordTrace]
  refine ⟨25240061189429784903274625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67306829838479426408732333 25240061189429784903274625)
  ·
    refine ⟨18930045892072338677455969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25240061189429784903274625 18930045892072338677455969)
    ·
      refine ⟨14197534419054254008091977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18930045892072338677455969 14197534419054254008091977)
      ·
        refine ⟨10648150814290690506068983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14197534419054254008091977 10648150814290690506068983)
        ·
          refine ⟨15972226221436035759103475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10648150814290690506068983 15972226221436035759103475)
          ·
            refine ⟨23958339332154053638655213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15972226221436035759103475 23958339332154053638655213)
            ·
              refine ⟨8984377249557770114495705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23958339332154053638655213 8984377249557770114495705)
              ·
                refine ⟨6738282937168327585871779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8984377249557770114495705 6738282937168327585871779)
                ·
                  refine ⟨10107424405752491378807669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6738282937168327585871779 10107424405752491378807669)
                  ·
                    refine ⟨947571038039296066763219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10107424405752491378807669 947571038039296066763219)
                    ·
                      rfl

theorem cell22_2768082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2768082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768082 prefixEnd_2768082 := by exact prefixLift 2768082
  have htrace : WordTrace (prefixWord ++ tailWord_2768082) baseStart_2768082 baseEnd_2768082 := by
    simpa [prefixWord, tailWord_2768082, baseEnd_2768082] using wordTrace_append hprefix tailTrace_2768082
  have hstable : (prefixWord ++ tailWord_2768082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768082).length < 2 ^ (prefixWord ++ tailWord_2768082).sum := by decide
  have hdescent : baseEnd_2768082 < baseStart_2768082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768097 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2768097 : Nat := 118140960795 + 2768097 * 2 ^ 59
def prefixEnd_2768097 : Nat := 4983230072969 + 3 ^ 40 * 2768097 * 2
def baseEnd_2768097 : Nat := 947576172845841027638173

theorem tailTrace_2768097 : CollatzResearch.WordTrace tailWord_2768097 prefixEnd_2768097 947576172845841027638173 := by
  unfold tailWord_2768097
  simp only [CollatzResearch.WordTrace]
  refine ⟨100960791852664797174894545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67307194568443198116596363 100960791852664797174894545)
  ·
    refine ⟨75720593889498597881170909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100960791852664797174894545 75720593889498597881170909)
    ·
      refine ⟨28395222708561974205439091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75720593889498597881170909 28395222708561974205439091)
      ·
        refine ⟨42592834062842961308158637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28395222708561974205439091 42592834062842961308158637)
        ·
          refine ⟨15972312773566110490559489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42592834062842961308158637 15972312773566110490559489)
          ·
            refine ⟨11979234580174582867919617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15972312773566110490559489 11979234580174582867919617)
            ·
              refine ⟨8984425935130937150939713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11979234580174582867919617 8984425935130937150939713)
              ·
                refine ⟨6738319451348202863204785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8984425935130937150939713 6738319451348202863204785)
                ·
                  refine ⟨5053739588511152147403589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6738319451348202863204785 5053739588511152147403589)
                  ·
                    refine ⟨947576172845841027638173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5053739588511152147403589 947576172845841027638173)
                    ·
                      rfl

theorem cell22_2768097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2768097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768097 prefixEnd_2768097 := by exact prefixLift 2768097
  have htrace : WordTrace (prefixWord ++ tailWord_2768097) baseStart_2768097 baseEnd_2768097 := by
    simpa [prefixWord, tailWord_2768097, baseEnd_2768097] using wordTrace_append hprefix tailTrace_2768097
  have hstable : (prefixWord ++ tailWord_2768097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768097).length < 2 ^ (prefixWord ++ tailWord_2768097).sum := by decide
  have hdescent : baseEnd_2768097 < baseStart_2768097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768127 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 5, 3]
def baseStart_2768127 : Nat := 118140960795 + 2768127 * 2 ^ 59
def prefixEnd_2768127 : Nat := 4983230072969 + 3 ^ 40 * 2768127 * 2
def baseEnd_2768127 : Nat := 947586442458930949388081

theorem tailTrace_2768127 : CollatzResearch.WordTrace tailWord_2768127 prefixEnd_2768127 947586442458930949388081 := by
  unfold tailWord_2768127
  simp only [CollatzResearch.WordTrace]
  refine ⟨100961886042556112298486635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67307924028370741532324423 100961886042556112298486635)
  ·
    refine ⟨151442829063834168447729953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100961886042556112298486635 151442829063834168447729953)
    ·
      refine ⟨113582121797875626335797465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151442829063834168447729953 113582121797875626335797465)
      ·
        refine ⟨85186591348406719751848099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113582121797875626335797465 85186591348406719751848099)
        ·
          refine ⟨127779887022610079627772149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85186591348406719751848099 127779887022610079627772149)
          ·
            refine ⟨11979364408369694965103639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127779887022610079627772149 11979364408369694965103639)
            ·
              refine ⟨17969046612554542447655459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11979364408369694965103639 17969046612554542447655459)
              ·
                refine ⟨26953569918831813671483189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17969046612554542447655459 26953569918831813671483189)
                ·
                  refine ⟨2526897179890482531701549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26953569918831813671483189 2526897179890482531701549)
                  ·
                    refine ⟨947586442458930949388081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2526897179890482531701549 947586442458930949388081)
                    ·
                      rfl

theorem cell22_2768127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_2768127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768127 prefixEnd_2768127 := by exact prefixLift 2768127
  have htrace : WordTrace (prefixWord ++ tailWord_2768127) baseStart_2768127 baseEnd_2768127 := by
    simpa [prefixWord, tailWord_2768127, baseEnd_2768127] using wordTrace_append hprefix tailTrace_2768127
  have hstable : (prefixWord ++ tailWord_2768127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768127).length < 2 ^ (prefixWord ++ tailWord_2768127).sum := by decide
  have hdescent : baseEnd_2768127 < baseStart_2768127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768204 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_2768204 : Nat := 118140960795 + 2768204 * 2 ^ 59
def prefixEnd_2768204 : Nat := 4983230072969 + 3 ^ 40 * 2768204 * 2
def baseEnd_2768204 : Nat := 947612801132528415212845

theorem tailTrace_2768204 : CollatzResearch.WordTrace tailWord_2768204 prefixEnd_2768204 947612801132528415212845 := by
  unfold tailWord_2768204
  simp only [CollatzResearch.WordTrace]
  refine ⟨50482347231638577224519833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67309796308851436299359777 50482347231638577224519833)
  ·
    refine ⟨37861760423728932918389875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50482347231638577224519833 37861760423728932918389875)
    ·
      refine ⟨56792640635593399377584813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37861760423728932918389875 56792640635593399377584813)
      ·
        refine ⟨21297240238347524766594305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56792640635593399377584813 21297240238347524766594305)
        ·
          refine ⟨15972930178760643574945729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21297240238347524766594305 15972930178760643574945729)
          ·
            refine ⟨11979697634070482681209297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15972930178760643574945729 11979697634070482681209297)
            ·
              refine ⟨8984773225552862010906973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11979697634070482681209297 8984773225552862010906973)
              ·
                refine ⟨3369289959582323254090115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8984773225552862010906973 3369289959582323254090115)
                ·
                  refine ⟨5053934939373484881135173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369289959582323254090115 5053934939373484881135173)
                  ·
                    refine ⟨947612801132528415212845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5053934939373484881135173 947612801132528415212845)
                    ·
                      rfl

theorem cell22_2768204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_2768204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768204 prefixEnd_2768204 := by exact prefixLift 2768204
  have htrace : WordTrace (prefixWord ++ tailWord_2768204) baseStart_2768204 baseEnd_2768204 := by
    simpa [prefixWord, tailWord_2768204, baseEnd_2768204] using wordTrace_append hprefix tailTrace_2768204
  have hstable : (prefixWord ++ tailWord_2768204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768204).length < 2 ^ (prefixWord ++ tailWord_2768204).sum := by decide
  have hdescent : baseEnd_2768204 < baseStart_2768204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768270 : List Nat := [4, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_2768270 : Nat := 118140960795 + 2768270 * 2 ^ 59
def prefixEnd_2768270 : Nat := 4983230072969 + 3 ^ 40 * 2768270 * 2
def baseEnd_2768270 : Nat := 315878464760442081020881

theorem tailTrace_2768270 : CollatzResearch.WordTrace tailWord_2768270 prefixEnd_2768270 315878464760442081020881 := by
  unfold tailWord_2768270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12620887710129755965117783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67311401120692031813961509 12620887710129755965117783)
  ·
    refine ⟨18931331565194633947676675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12620887710129755965117783 18931331565194633947676675)
    ·
      refine ⟨28396997347791950921515013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18931331565194633947676675 28396997347791950921515013)
      ·
        refine ⟨5324437002710990797784065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28396997347791950921515013 5324437002710990797784065)
        ·
          refine ⟨3993327752033243098338049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5324437002710990797784065 3993327752033243098338049)
          ·
            refine ⟨2994995814024932323753537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3993327752033243098338049 2994995814024932323753537)
            ·
              refine ⟨2246246860518699242815153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2994995814024932323753537 2246246860518699242815153)
              ·
                refine ⟨1684685145389024432111365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246246860518699242815153 1684685145389024432111365)
                ·
                  refine ⟨315878464760442081020881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1684685145389024432111365 315878464760442081020881)
                  ·
                    rfl

theorem cell22_2768270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_2768270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768270 prefixEnd_2768270 := by exact prefixLift 2768270
  have htrace : WordTrace (prefixWord ++ tailWord_2768270) baseStart_2768270 baseEnd_2768270 := by
    simpa [prefixWord, tailWord_2768270, baseEnd_2768270] using wordTrace_append hprefix tailTrace_2768270
  have hstable : (prefixWord ++ tailWord_2768270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768270).length < 2 ^ (prefixWord ++ tailWord_2768270).sum := by decide
  have hdescent : baseEnd_2768270 < baseStart_2768270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768277 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2768277 : Nat := 118140960795 + 2768277 * 2 ^ 59
def prefixEnd_2768277 : Nat := 4983230072969 + 3 ^ 40 * 2768277 * 2
def baseEnd_2768277 : Nat := 947637790524380558137621

theorem tailTrace_2768277 : CollatzResearch.WordTrace tailWord_2768277 prefixEnd_2768277 947637790524380558137621 := by
  unfold tailWord_2768277
  simp only [CollatzResearch.WordTrace]
  refine ⟨100967356992012687916447085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67311571328008458610964723 100967356992012687916447085)
  ·
    refine ⟨37862758872004757968667657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100967356992012687916447085 37862758872004757968667657)
    ·
      refine ⟨28397069154003568476500743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37862758872004757968667657 28397069154003568476500743)
      ·
        refine ⟨42595603731005352714751115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28397069154003568476500743 42595603731005352714751115)
        ·
          refine ⟨63893405596508029072126673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42595603731005352714751115 63893405596508029072126673)
          ·
            refine ⟨47920054197381021804095005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63893405596508029072126673 47920054197381021804095005)
            ·
              refine ⟨17970020324017883176535627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47920054197381021804095005 17970020324017883176535627)
              ·
                refine ⟨26955030486026824764803441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17970020324017883176535627 26955030486026824764803441)
                ·
                  refine ⟨20216272864520118573602581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26955030486026824764803441 20216272864520118573602581)
                  ·
                    refine ⟨947637790524380558137621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20216272864520118573602581 947637790524380558137621)
                    ·
                      rfl

theorem cell22_2768277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2768277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768277 prefixEnd_2768277 := by exact prefixLift 2768277
  have htrace : WordTrace (prefixWord ++ tailWord_2768277) baseStart_2768277 baseEnd_2768277 := by
    simpa [prefixWord, tailWord_2768277, baseEnd_2768277] using wordTrace_append hprefix tailTrace_2768277
  have hstable : (prefixWord ++ tailWord_2768277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768277).length < 2 ^ (prefixWord ++ tailWord_2768277).sum := by decide
  have hdescent : baseEnd_2768277 < baseStart_2768277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768279 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 3, 3]
def baseStart_2768279 : Nat := 118140960795 + 2768279 * 2 ^ 59
def prefixEnd_2768279 : Nat := 4983230072969 + 3 ^ 40 * 2768279 * 2
def baseEnd_2768279 : Nat := 947638475165253219587615

theorem tailTrace_2768279 : CollatzResearch.WordTrace tailWord_2768279 prefixEnd_2768279 947638475165253219587615 := by
  unfold tailWord_2768279
  simp only [CollatzResearch.WordTrace]
  refine ⟨100967429938005442258019891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67311619958670294838679927 100967429938005442258019891)
  ·
    refine ⟨151451144907008163387029837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100967429938005442258019891 151451144907008163387029837)
    ·
      refine ⟨56794179340128061270136189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151451144907008163387029837 56794179340128061270136189)
      ·
        refine ⟨21297817252548022976301071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56794179340128061270136189 21297817252548022976301071)
        ·
          refine ⟨31946725878822034464451607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21297817252548022976301071 31946725878822034464451607)
          ·
            refine ⟨47920088818233051696677411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31946725878822034464451607 47920088818233051696677411)
            ·
              refine ⟨71880133227349577545016117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47920088818233051696677411 71880133227349577545016117)
              ·
                refine ⟨6738762490064022894845261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71880133227349577545016117 6738762490064022894845261)
                ·
                  refine ⟨2527035933774008585566973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6738762490064022894845261 2527035933774008585566973)
                  ·
                    refine ⟨947638475165253219587615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527035933774008585566973 947638475165253219587615)
                    ·
                      rfl

theorem cell22_2768279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_2768279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768279 prefixEnd_2768279 := by exact prefixLift 2768279
  have htrace : WordTrace (prefixWord ++ tailWord_2768279) baseStart_2768279 baseEnd_2768279 := by
    simpa [prefixWord, tailWord_2768279, baseEnd_2768279] using wordTrace_append hprefix tailTrace_2768279
  have hstable : (prefixWord ++ tailWord_2768279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768279).length < 2 ^ (prefixWord ++ tailWord_2768279).sum := by decide
  have hdescent : baseEnd_2768279 < baseStart_2768279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768292 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_2768292 : Nat := 118140960795 + 2768292 * 2 ^ 59
def prefixEnd_2768292 : Nat := 4983230072969 + 3 ^ 40 * 2768292 * 2
def baseEnd_2768292 : Nat := 315880975110308506337525

theorem tailTrace_2768292 : CollatzResearch.WordTrace tailWord_2768292 prefixEnd_2768292 315880975110308506337525 := by
  unfold tailWord_2768292
  simp only [CollatzResearch.WordTrace]
  refine ⟨50483952043479172739121565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67311936057972230318828753 50483952043479172739121565)
  ·
    refine ⟨18931482016304689777170587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50483952043479172739121565 18931482016304689777170587)
    ·
      refine ⟨28397223024457034665755881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18931482016304689777170587 28397223024457034665755881)
      ·
        refine ⟨21297917268342775999316911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28397223024457034665755881 21297917268342775999316911)
        ·
          refine ⟨31946875902514163998975367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21297917268342775999316911 31946875902514163998975367)
          ·
            refine ⟨47920313853771245998463051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31946875902514163998975367 47920313853771245998463051)
            ·
              refine ⟨71880470780656868997694577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47920313853771245998463051 71880470780656868997694577)
              ·
                refine ⟨53910353085492651748270933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71880470780656868997694577 53910353085492651748270933)
                ·
                  refine ⟨315880975110308506337525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53910353085492651748270933 315880975110308506337525)
                  ·
                    rfl

theorem cell22_2768292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_2768292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768292 prefixEnd_2768292 := by exact prefixLift 2768292
  have htrace : WordTrace (prefixWord ++ tailWord_2768292) baseStart_2768292 baseEnd_2768292 := by
    simpa [prefixWord, tailWord_2768292, baseEnd_2768292] using wordTrace_append hprefix tailTrace_2768292
  have hstable : (prefixWord ++ tailWord_2768292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768292).length < 2 ^ (prefixWord ++ tailWord_2768292).sum := by decide
  have hdescent : baseEnd_2768292 < baseStart_2768292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768373 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2768373 : Nat := 118140960795 + 2768373 * 2 ^ 59
def prefixEnd_2768373 : Nat := 4983230072969 + 3 ^ 40 * 2768373 * 2
def baseEnd_2768373 : Nat := 947670653286268307737327

theorem tailTrace_2768373 : CollatzResearch.WordTrace tailWord_2768373 prefixEnd_2768373 947670653286268307737327 := by
  unfold tailWord_2768373
  simp only [CollatzResearch.WordTrace]
  refine ⟨100970858399664896311941773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67313905599776597541294515 100970858399664896311941773)
  ·
    refine ⟨37864071899874336116978165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100970858399664896311941773 37864071899874336116978165)
    ·
      refine ⟨3549756740613219010966703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37864071899874336116978165 3549756740613219010966703)
      ·
        refine ⟨5324635110919828516450055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549756740613219010966703 5324635110919828516450055)
        ·
          refine ⟨7986952666379742774675083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5324635110919828516450055 7986952666379742774675083)
          ·
            refine ⟨11980428999569614162012625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7986952666379742774675083 11980428999569614162012625)
            ·
              refine ⟨8985321749677210621509469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11980428999569614162012625 8985321749677210621509469)
              ·
                refine ⟨3369495656128953983066051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8985321749677210621509469 3369495656128953983066051)
                ·
                  refine ⟨5054243484193430974599077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3369495656128953983066051 5054243484193430974599077)
                  ·
                    refine ⟨947670653286268307737327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5054243484193430974599077 947670653286268307737327)
                    ·
                      rfl

theorem cell22_2768373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2768373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768373 prefixEnd_2768373 := by exact prefixLift 2768373
  have htrace : WordTrace (prefixWord ++ tailWord_2768373) baseStart_2768373 baseEnd_2768373 := by
    simpa [prefixWord, tailWord_2768373, baseEnd_2768373] using wordTrace_append hprefix tailTrace_2768373
  have hstable : (prefixWord ++ tailWord_2768373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768373).length < 2 ^ (prefixWord ++ tailWord_2768373).sum := by decide
  have hdescent : baseEnd_2768373 < baseStart_2768373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768388 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_2768388 : Nat := 118140960795 + 2768388 * 2 ^ 59
def prefixEnd_2768388 : Nat := 4983230072969 + 3 ^ 40 * 2768388 * 2
def baseEnd_2768388 : Nat := 315891929364271089537427

theorem tailTrace_2768388 : CollatzResearch.WordTrace tailWord_2768388 prefixEnd_2768388 315891929364271089537427 := by
  unfold tailWord_2768388
  simp only [CollatzResearch.WordTrace]
  refine ⟨50485702747305276936868909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67314270329740369249158545 50485702747305276936868909)
  ·
    refine ⟨18932138530239478851325841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50485702747305276936868909 18932138530239478851325841)
    ·
      refine ⟨14199103897679609138494381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18932138530239478851325841 14199103897679609138494381)
      ·
        refine ⟨5324663961629853426935393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14199103897679609138494381 5324663961629853426935393)
        ·
          refine ⟨3993497971222390070201545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5324663961629853426935393 3993497971222390070201545)
          ·
            refine ⟨2995123478416792552651159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3993497971222390070201545 2995123478416792552651159)
            ·
              refine ⟨4492685217625188828976739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995123478416792552651159 4492685217625188828976739)
              ·
                refine ⟨6739027826437783243465109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492685217625188828976739 6739027826437783243465109)
                ·
                  refine ⟨315891929364271089537427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6739027826437783243465109 315891929364271089537427)
                  ·
                    rfl

theorem cell22_2768388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_2768388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768388 prefixEnd_2768388 := by exact prefixLift 2768388
  have htrace : WordTrace (prefixWord ++ tailWord_2768388) baseStart_2768388 baseEnd_2768388 := by
    simpa [prefixWord, tailWord_2768388, baseEnd_2768388] using wordTrace_append hprefix tailTrace_2768388
  have hstable : (prefixWord ++ tailWord_2768388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768388).length < 2 ^ (prefixWord ++ tailWord_2768388).sum := by decide
  have hdescent : baseEnd_2768388 < baseStart_2768388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768403 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 2, 3]
def baseStart_2768403 : Nat := 118140960795 + 2768403 * 2 ^ 59
def prefixEnd_2768403 : Nat := 4983230072969 + 3 ^ 40 * 2768403 * 2
def baseEnd_2768403 : Nat := 947680922899358229487235

theorem tailTrace_2768403 : CollatzResearch.WordTrace tailWord_2768403 prefixEnd_2768403 947680922899358229487235 := by
  unfold tailWord_2768403
  simp only [CollatzResearch.WordTrace]
  refine ⟨100971952589556211435533863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67314635059704140957022575 100971952589556211435533863)
  ·
    refine ⟨151457928884334317153300795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100971952589556211435533863 151457928884334317153300795)
    ·
      refine ⟨227186893326501475729951193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151457928884334317153300795 227186893326501475729951193)
      ·
        refine ⟨170390169994876106797463395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227186893326501475729951193 170390169994876106797463395)
        ·
          refine ⟨255585254992314160196195093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170390169994876106797463395 255585254992314160196195093)
          ·
            refine ⟨11980558827764726259196645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255585254992314160196195093 11980558827764726259196645)
            ·
              refine ⟨2246354780205886173599371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11980558827764726259196645 2246354780205886173599371)
              ·
                refine ⟨3369532170308829260399057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246354780205886173599371 3369532170308829260399057)
                ·
                  refine ⟨2527149127731621945299293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369532170308829260399057 2527149127731621945299293)
                  ·
                    refine ⟨947680922899358229487235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527149127731621945299293 947680922899358229487235)
                    ·
                      rfl

theorem cell22_2768403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 2, 3].length) (baseStart_2768403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768403 prefixEnd_2768403 := by exact prefixLift 2768403
  have htrace : WordTrace (prefixWord ++ tailWord_2768403) baseStart_2768403 baseEnd_2768403 := by
    simpa [prefixWord, tailWord_2768403, baseEnd_2768403] using wordTrace_append hprefix tailTrace_2768403
  have hstable : (prefixWord ++ tailWord_2768403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768403).length < 2 ^ (prefixWord ++ tailWord_2768403).sum := by decide
  have hdescent : baseEnd_2768403 < baseStart_2768403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768521 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 1, 5]
def baseStart_2768521 : Nat := 118140960795 + 2768521 * 2 ^ 59
def prefixEnd_2768521 : Nat := 4983230072969 + 3 ^ 40 * 2768521 * 2
def baseEnd_2768521 : Nat := 947721316710845255036873

theorem tailTrace_2768521 : CollatzResearch.WordTrace tailWord_2768521 prefixEnd_2768521 947721316710845255036873 := by
  unfold tailWord_2768521
  simp only [CollatzResearch.WordTrace]
  refine ⟨100976256403128717588329417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67317504268752478392219611 100976256403128717588329417)
  ·
    refine ⟨75732192302346538191247063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100976256403128717588329417 75732192302346538191247063)
    ·
      refine ⟨113598288453519807286870595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75732192302346538191247063 113598288453519807286870595)
      ·
        refine ⟨170397432680279710930305893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113598288453519807286870595 170397432680279710930305893)
        ·
          refine ⟨31949518627552445799432355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170397432680279710930305893 31949518627552445799432355)
          ·
            refine ⟨47924277941328668699148533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31949518627552445799432355 47924277941328668699148533)
            ·
              refine ⟨4492901056999562690545175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47924277941328668699148533 4492901056999562690545175)
              ·
                refine ⟨6739351585499344035817763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4492901056999562690545175 6739351585499344035817763)
                ·
                  refine ⟨10109027378249016053726645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6739351585499344035817763 10109027378249016053726645)
                  ·
                    refine ⟨947721316710845255036873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10109027378249016053726645 947721316710845255036873)
                    ·
                      rfl

theorem cell22_2768521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 5].length) (baseStart_2768521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768521 prefixEnd_2768521 := by exact prefixLift 2768521
  have htrace : WordTrace (prefixWord ++ tailWord_2768521) baseStart_2768521 baseEnd_2768521 := by
    simpa [prefixWord, tailWord_2768521, baseEnd_2768521] using wordTrace_append hprefix tailTrace_2768521
  have hstable : (prefixWord ++ tailWord_2768521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768521).length < 2 ^ (prefixWord ++ tailWord_2768521).sum := by decide
  have hdescent : baseEnd_2768521 < baseStart_2768521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768536 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_2768536 : Nat := 118140960795 + 2768536 * 2 ^ 59
def prefixEnd_2768536 : Nat := 4983230072969 + 3 ^ 40 * 2768536 * 2
def baseEnd_2768536 : Nat := 947726451517390215911827

theorem tailTrace_2768536 : CollatzResearch.WordTrace tailWord_2768536 prefixEnd_2768536 947726451517390215911827 := by
  unfold tailWord_2768536
  simp only [CollatzResearch.WordTrace]
  refine ⟨50488401749037187575062731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67317868998716250100083641 50488401749037187575062731)
  ·
    refine ⟨75732602623555781362594097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50488401749037187575062731 75732602623555781362594097)
    ·
      refine ⟨56799451967666836021945573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75732602623555781362594097 56799451967666836021945573)
      ·
        refine ⟨10649897243937531754114795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56799451967666836021945573 10649897243937531754114795)
        ·
          refine ⟨15974845865906297631172193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10649897243937531754114795 15974845865906297631172193)
          ·
            refine ⟨11981134399429723223379145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15974845865906297631172193 11981134399429723223379145)
            ·
              refine ⟨8985850799572292417534359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11981134399429723223379145 8985850799572292417534359)
              ·
                refine ⟨13478776199358438626301539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8985850799572292417534359 13478776199358438626301539)
                ·
                  refine ⟨20218164299037657939452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13478776199358438626301539 20218164299037657939452309)
                  ·
                    refine ⟨947726451517390215911827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20218164299037657939452309 947726451517390215911827)
                    ·
                      rfl

theorem cell22_2768536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_2768536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768536 prefixEnd_2768536 := by exact prefixLift 2768536
  have htrace : WordTrace (prefixWord ++ tailWord_2768536) baseStart_2768536 baseEnd_2768536 := by
    simpa [prefixWord, tailWord_2768536, baseEnd_2768536] using wordTrace_append hprefix tailTrace_2768536
  have hstable : (prefixWord ++ tailWord_2768536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768536).length < 2 ^ (prefixWord ++ tailWord_2768536).sum := by decide
  have hdescent : baseEnd_2768536 < baseStart_2768536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768572 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_2768572 : Nat := 118140960795 + 2768572 * 2 ^ 59
def prefixEnd_2768572 : Nat := 4983230072969 + 3 ^ 40 * 2768572 * 2
def baseEnd_2768572 : Nat := 947738775053098122011717

theorem tailTrace_2768572 : CollatzResearch.WordTrace tailWord_2768572 prefixEnd_2768572 947738775053098122011717 := by
  unfold tailWord_2768572
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489058262971976649217985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67318744350629302198957313 50489058262971976649217985)
  ·
    refine ⟨37866793697228982486913489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50489058262971976649217985 37866793697228982486913489)
    ·
      refine ⟨28400095272921736865185117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37866793697228982486913489 28400095272921736865185117)
      ·
        refine ⟨10650035727345651324444419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28400095272921736865185117 10650035727345651324444419)
        ·
          refine ⟨15975053591018476986666629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650035727345651324444419 15975053591018476986666629)
          ·
            refine ⟨2995322548315964434999993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15975053591018476986666629 2995322548315964434999993)
            ·
              refine ⟨2246491911236973326249995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995322548315964434999993 2246491911236973326249995)
              ·
                refine ⟨3369737866855459989374993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246491911236973326249995 3369737866855459989374993)
                ·
                  refine ⟨2527303400141594992031245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3369737866855459989374993 2527303400141594992031245)
                  ·
                    refine ⟨947738775053098122011717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527303400141594992031245 947738775053098122011717)
                    ·
                      rfl

theorem cell22_2768572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_2768572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768572 prefixEnd_2768572 := by exact prefixLift 2768572
  have htrace : WordTrace (prefixWord ++ tailWord_2768572) baseStart_2768572 baseEnd_2768572 := by
    simpa [prefixWord, tailWord_2768572, baseEnd_2768572] using wordTrace_append hprefix tailTrace_2768572
  have hstable : (prefixWord ++ tailWord_2768572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768572).length < 2 ^ (prefixWord ++ tailWord_2768572).sum := by decide
  have hdescent : baseEnd_2768572 < baseStart_2768572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768600 : List Nat := [2, 1, 2, 2, 3, 1, 2, 5, 1, 3]
def baseStart_2768600 : Nat := 118140960795 + 2768600 * 2 ^ 59
def prefixEnd_2768600 : Nat := 4983230072969 + 3 ^ 40 * 2768600 * 2
def baseEnd_2768600 : Nat := 947748360025315382311631

theorem tailTrace_2768600 : CollatzResearch.WordTrace tailWord_2768600 prefixEnd_2768600 947748360025315382311631 := by
  unfold tailWord_2768600
  simp only [CollatzResearch.WordTrace]
  refine ⟨50489568884921257040227627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67319425179895009386970169 50489568884921257040227627)
  ·
    refine ⟨75734353327381885560341441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50489568884921257040227627 75734353327381885560341441)
    ·
      refine ⟨56800764995536414170256081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75734353327381885560341441 56800764995536414170256081)
      ·
        refine ⟨42600573746652310627692061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56800764995536414170256081 42600573746652310627692061)
        ·
          refine ⟨15975215154994616485384523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42600573746652310627692061 15975215154994616485384523)
          ·
            refine ⟨23962822732491924728076785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975215154994616485384523 23962822732491924728076785)
            ·
              refine ⟨17972117049368943546057589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23962822732491924728076785 17972117049368943546057589)
              ·
                refine ⟨1684885973378338457442899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17972117049368943546057589 1684885973378338457442899)
                ·
                  refine ⟨2527328960067507686164349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684885973378338457442899 2527328960067507686164349)
                  ·
                    refine ⟨947748360025315382311631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527328960067507686164349 947748360025315382311631)
                    ·
                      rfl

theorem cell22_2768600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_2768600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768600 prefixEnd_2768600 := by exact prefixLift 2768600
  have htrace : WordTrace (prefixWord ++ tailWord_2768600) baseStart_2768600 baseEnd_2768600 := by
    simpa [prefixWord, tailWord_2768600, baseEnd_2768600] using wordTrace_append hprefix tailTrace_2768600
  have hstable : (prefixWord ++ tailWord_2768600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768600).length < 2 ^ (prefixWord ++ tailWord_2768600).sum := by decide
  have hdescent : baseEnd_2768600 < baseStart_2768600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768613 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 5]
def baseStart_2768613 : Nat := 118140960795 + 2768613 * 2 ^ 59
def prefixEnd_2768613 : Nat := 4983230072969 + 3 ^ 40 * 2768613 * 2
def baseEnd_2768613 : Nat := 315917603396995893912197

theorem tailTrace_2768613 : CollatzResearch.WordTrace tailWord_2768613 prefixEnd_2768613 315917603396995893912197 := by
  unfold tailWord_2768613
  simp only [CollatzResearch.WordTrace]
  refine ⟨100979611918795417300678493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67319741279196944867118995 100979611918795417300678493)
  ·
    refine ⟨37867354469548281487754435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100979611918795417300678493 37867354469548281487754435)
    ·
      refine ⟨56801031704322422231631653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37867354469548281487754435 56801031704322422231631653)
      ·
        refine ⟨10650193444560454168430935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56801031704322422231631653 10650193444560454168430935)
        ·
          refine ⟨15975290166840681252646403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10650193444560454168430935 15975290166840681252646403)
          ·
            refine ⟨23962935250261021878969605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15975290166840681252646403 23962935250261021878969605)
            ·
              refine ⟨4493050359423941602306801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23962935250261021878969605 4493050359423941602306801)
              ·
                refine ⟨3369787769567956201730101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493050359423941602306801 3369787769567956201730101)
                ·
                  refine ⟨315917603396995893912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3369787769567956201730101 315917603396995893912197)
                  ·
                    rfl

theorem cell22_2768613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_2768613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768613 prefixEnd_2768613 := by exact prefixLift 2768613
  have htrace : WordTrace (prefixWord ++ tailWord_2768613) baseStart_2768613 baseEnd_2768613 := by
    simpa [prefixWord, tailWord_2768613, baseEnd_2768613] using wordTrace_append hprefix tailTrace_2768613
  have hstable : (prefixWord ++ tailWord_2768613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768613).length < 2 ^ (prefixWord ++ tailWord_2768613).sum := by decide
  have hdescent : baseEnd_2768613 < baseStart_2768613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768641 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 8]
def baseStart_2768641 : Nat := 118140960795 + 2768641 * 2 ^ 59
def prefixEnd_2768641 : Nat := 4983230072969 + 3 ^ 40 * 2768641 * 2
def baseEnd_2768641 : Nat := 315920798387734980678835

theorem tailTrace_2768641 : CollatzResearch.WordTrace tailWord_2768641 prefixEnd_2768641 315920798387734980678835 := by
  unfold tailWord_2768641
  simp only [CollatzResearch.WordTrace]
  refine ⟨100980633162693978082697777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67320422108462652055131851 100980633162693978082697777)
  ·
    refine ⟨75735474872020483562023333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100980633162693978082697777 75735474872020483562023333)
    ·
      refine ⟨14200401538503840667879375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75735474872020483562023333 14200401538503840667879375)
      ·
        refine ⟨21300602307755761001819063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14200401538503840667879375 21300602307755761001819063)
        ·
          refine ⟨31950903461633641502728595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21300602307755761001819063 31950903461633641502728595)
          ·
            refine ⟨47926355192450462254092893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31950903461633641502728595 47926355192450462254092893)
            ·
              refine ⟨17972383197168923345284835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47926355192450462254092893 17972383197168923345284835)
              ·
                refine ⟨26958574795753385017927253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17972383197168923345284835 26958574795753385017927253)
                ·
                  refine ⟨315920798387734980678835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26958574795753385017927253 315920798387734980678835)
                  ·
                    rfl

theorem cell22_2768641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 8].length) (baseStart_2768641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768641 prefixEnd_2768641 := by exact prefixLift 2768641
  have htrace : WordTrace (prefixWord ++ tailWord_2768641) baseStart_2768641 baseEnd_2768641 := by
    simpa [prefixWord, tailWord_2768641, baseEnd_2768641] using wordTrace_append hprefix tailTrace_2768641
  have hstable : (prefixWord ++ tailWord_2768641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768641).length < 2 ^ (prefixWord ++ tailWord_2768641).sum := by decide
  have hdescent : baseEnd_2768641 < baseStart_2768641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768690 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2768690 : Nat := 118140960795 + 2768690 * 2 ^ 59
def prefixEnd_2768690 : Nat := 4983230072969 + 3 ^ 40 * 2768690 * 2
def baseEnd_2768690 : Nat := 947779168864585147561355

theorem tailTrace_2768690 : CollatzResearch.WordTrace tailWord_2768690 prefixEnd_2768690 947779168864585147561355 := by
  unfold tailWord_2768690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25245605084879114862807881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67321613559677639634154349 25245605084879114862807881)
  ·
    refine ⟨18934203813659336147105911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25245605084879114862807881 18934203813659336147105911)
    ·
      refine ⟨28401305720489004220658867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18934203813659336147105911 28401305720489004220658867)
      ·
        refine ⟨42601958580733506330988301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28401305720489004220658867 42601958580733506330988301)
        ·
          refine ⟨15975734467775064874120613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42601958580733506330988301 15975734467775064874120613)
          ·
            refine ⟨2995450212707824663897615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15975734467775064874120613 2995450212707824663897615)
            ·
              refine ⟨4493175319061736995846423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995450212707824663897615 4493175319061736995846423)
              ·
                refine ⟨6739762978592605493769635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493175319061736995846423 6739762978592605493769635)
                ·
                  refine ⟨10109644467888908240654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6739762978592605493769635 10109644467888908240654453)
                  ·
                    refine ⟨947779168864585147561355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10109644467888908240654453 947779168864585147561355)
                    ·
                      rfl

theorem cell22_2768690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2768690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768690 prefixEnd_2768690 := by exact prefixLift 2768690
  have htrace : WordTrace (prefixWord ++ tailWord_2768690) baseStart_2768690 baseEnd_2768690 := by
    simpa [prefixWord, tailWord_2768690, baseEnd_2768690] using wordTrace_append hprefix tailTrace_2768690
  have hstable : (prefixWord ++ tailWord_2768690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768690).length < 2 ^ (prefixWord ++ tailWord_2768690).sum := by decide
  have hdescent : baseEnd_2768690 < baseStart_2768690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768703 : List Nat := [1, 1, 2, 2, 6, 1, 1, 8]
def baseStart_2768703 : Nat := 118140960795 + 2768703 * 2 ^ 59
def prefixEnd_2768703 : Nat := 4983230072969 + 3 ^ 40 * 2768703 * 2
def baseEnd_2768703 : Nat := 105309291003361938554035

theorem tailTrace_2768703 : CollatzResearch.WordTrace tailWord_2768703 prefixEnd_2768703 105309291003361938554035 := by
  unfold tailWord_2768703
  simp only [CollatzResearch.WordTrace]
  refine ⟨100982894488469362671454763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67321929658979575114303175 100982894488469362671454763)
  ·
    refine ⟨151474341732704044007182145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100982894488469362671454763 151474341732704044007182145)
    ·
      refine ⟨113605756299528033005386609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151474341732704044007182145 113605756299528033005386609)
      ·
        refine ⟨85204317224646024754039957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113605756299528033005386609 85204317224646024754039957)
        ·
          refine ⟨3993952369905282410345623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85204317224646024754039957 3993952369905282410345623)
          ·
            refine ⟨5990928554857923615518435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993952369905282410345623 5990928554857923615518435)
            ·
              refine ⟨8986392832286885423277653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5990928554857923615518435 8986392832286885423277653)
              ·
                refine ⟨105309291003361938554035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8986392832286885423277653 105309291003361938554035)
                ·
                  rfl

theorem cell22_2768703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 8].length) (baseStart_2768703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768703 prefixEnd_2768703 := by exact prefixLift 2768703
  have htrace : WordTrace (prefixWord ++ tailWord_2768703) baseStart_2768703 baseEnd_2768703 := by
    simpa [prefixWord, tailWord_2768703, baseEnd_2768703] using wordTrace_append hprefix tailTrace_2768703
  have hstable : (prefixWord ++ tailWord_2768703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768703).length < 2 ^ (prefixWord ++ tailWord_2768703).sum := by decide
  have hdescent : baseEnd_2768703 < baseStart_2768703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768735 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 3, 3]
def baseStart_2768735 : Nat := 118140960795 + 2768735 * 2 ^ 59
def prefixEnd_2768735 : Nat := 4983230072969 + 3 ^ 40 * 2768735 * 2
def baseEnd_2768735 : Nat := 947794573284220030186217

theorem tailTrace_2768735 : CollatzResearch.WordTrace tailWord_2768735 prefixEnd_2768735 947794573284220030186217 := by
  unfold tailWord_2768735
  simp only [CollatzResearch.WordTrace]
  refine ⟨100984061624353432136619659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67322707749568954757746439 100984061624353432136619659)
  ·
    refine ⟨151476092436530148204929489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100984061624353432136619659 151476092436530148204929489)
    ·
      refine ⟨113607069327397611153697117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151476092436530148204929489 113607069327397611153697117)
      ·
        refine ⟨42602650997774104182636419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113607069327397611153697117 42602650997774104182636419)
        ·
          refine ⟨63903976496661156273954629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42602650997774104182636419 63903976496661156273954629)
          ·
            refine ⟨11981995593123966801366493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63903976496661156273954629 11981995593123966801366493)
            ·
              refine ⟨4493248347421487550512435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11981995593123966801366493 4493248347421487550512435)
              ·
                refine ⟨6739872521132231325768653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493248347421487550512435 6739872521132231325768653)
                ·
                  refine ⟨2527452195424586747163245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6739872521132231325768653 2527452195424586747163245)
                  ·
                    refine ⟨947794573284220030186217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527452195424586747163245 947794573284220030186217)
                    ·
                      rfl

theorem cell22_2768735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_2768735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768735 prefixEnd_2768735 := by exact prefixLift 2768735
  have htrace : WordTrace (prefixWord ++ tailWord_2768735) baseStart_2768735 baseEnd_2768735 := by
    simpa [prefixWord, tailWord_2768735, baseEnd_2768735] using wordTrace_append hprefix tailTrace_2768735
  have hstable : (prefixWord ++ tailWord_2768735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768735).length < 2 ^ (prefixWord ++ tailWord_2768735).sum := by decide
  have hdescent : baseEnd_2768735 < baseStart_2768735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768786 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2768786 : Nat := 118140960795 + 2768786 * 2 ^ 59
def prefixEnd_2768786 : Nat := 4983230072969 + 3 ^ 40 * 2768786 * 2
def baseEnd_2768786 : Nat := 947812031626472897161061

theorem tailTrace_2768786 : CollatzResearch.WordTrace tailWord_2768786 prefixEnd_2768786 947812031626472897161061 := by
  unfold tailWord_2768786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246480436792166961681553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67323947831445778564484141 25246480436792166961681553)
  ·
    refine ⟨18934860327594125221261165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25246480436792166961681553 18934860327594125221261165)
    ·
      refine ⟨7100572622847796957972937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18934860327594125221261165 7100572622847796957972937)
      ·
        refine ⟨5325429467135847718479703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7100572622847796957972937 5325429467135847718479703)
        ·
          refine ⟨7988144200703771577719555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5325429467135847718479703 7988144200703771577719555)
          ·
            refine ⟨11982216301055657366579333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7988144200703771577719555 11982216301055657366579333)
            ·
              refine ⟨2246665556447935756233625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11982216301055657366579333 2246665556447935756233625)
              ·
                refine ⟨1684999167335951817175219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2246665556447935756233625 1684999167335951817175219)
                ·
                  refine ⟨2527498751003927725762829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684999167335951817175219 2527498751003927725762829)
                  ·
                    refine ⟨947812031626472897161061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527498751003927725762829 947812031626472897161061)
                    ·
                      rfl

theorem cell22_2768786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2768786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768786 prefixEnd_2768786 := by exact prefixLift 2768786
  have htrace : WordTrace (prefixWord ++ tailWord_2768786) baseStart_2768786 baseEnd_2768786 := by
    simpa [prefixWord, tailWord_2768786, baseEnd_2768786] using wordTrace_append hprefix tailTrace_2768786
  have hstable : (prefixWord ++ tailWord_2768786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768786).length < 2 ^ (prefixWord ++ tailWord_2768786).sum := by decide
  have hdescent : baseEnd_2768786 < baseStart_2768786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768825 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 4, 3]
def baseStart_2768825 : Nat := 118140960795 + 2768825 * 2 ^ 59
def prefixEnd_2768825 : Nat := 4983230072969 + 3 ^ 40 * 2768825 * 2
def baseEnd_2768825 : Nat := 947825382123489795435941

theorem tailTrace_2768825 : CollatzResearch.WordTrace tailWord_2768825 prefixEnd_2768825 947825382123489795435941 := by
  unfold tailWord_2768825
  simp only [CollatzResearch.WordTrace]
  refine ⟨100987344194027377507395929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67324896129351585004930619 100987344194027377507395929)
  ·
    refine ⟨75740508145520533130546947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100987344194027377507395929 75740508145520533130546947)
    ·
      refine ⟨113610762218280799695820421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75740508145520533130546947 113610762218280799695820421)
      ·
        refine ⟨21302017915927649942966329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113610762218280799695820421 21302017915927649942966329)
        ·
          refine ⟨15976513436945737457224747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21302017915927649942966329 15976513436945737457224747)
          ·
            refine ⟨23964770155418606185837121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15976513436945737457224747 23964770155418606185837121)
            ·
              refine ⟨17973577616563954639377841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23964770155418606185837121 17973577616563954639377841)
              ·
                refine ⟨13480183212422965979533381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17973577616563954639377841 13480183212422965979533381)
                ·
                  refine ⟨2527534352329306121162509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13480183212422965979533381 2527534352329306121162509)
                  ·
                    refine ⟨947825382123489795435941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527534352329306121162509 947825382123489795435941)
                    ·
                      rfl

theorem cell22_2768825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 3].length) (baseStart_2768825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768825 prefixEnd_2768825 := by exact prefixLift 2768825
  have htrace : WordTrace (prefixWord ++ tailWord_2768825) baseStart_2768825 baseEnd_2768825 := by
    simpa [prefixWord, tailWord_2768825, baseEnd_2768825] using wordTrace_append hprefix tailTrace_2768825
  have hstable : (prefixWord ++ tailWord_2768825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768825).length < 2 ^ (prefixWord ++ tailWord_2768825).sum := by decide
  have hdescent : baseEnd_2768825 < baseStart_2768825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768829 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2768829 : Nat := 118140960795 + 2768829 * 2 ^ 59
def prefixEnd_2768829 : Nat := 4983230072969 + 3 ^ 40 * 2768829 * 2
def baseEnd_2768829 : Nat := 947826751405235118335929

theorem tailTrace_2768829 : CollatzResearch.WordTrace tailWord_2768829 prefixEnd_2768829 947826751405235118335929 := by
  unfold tailWord_2768829
  simp only [CollatzResearch.WordTrace]
  refine ⟨100987490086012886190541541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67324993390675257460361027 100987490086012886190541541)
  ·
    refine ⟨18935154391127416160726539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100987490086012886190541541 18935154391127416160726539)
    ·
      refine ⟨28402731586691124241089809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18935154391127416160726539 28402731586691124241089809)
      ·
        refine ⟨21302048690018343180817357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28402731586691124241089809 21302048690018343180817357)
        ·
          refine ⟨7988268258756878692806509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21302048690018343180817357 7988268258756878692806509)
          ·
            refine ⟨2995600597033829509802441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7988268258756878692806509 2995600597033829509802441)
            ·
              refine ⟨2246700447775372132351831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995600597033829509802441 2246700447775372132351831)
              ·
                refine ⟨3370050671663058198527747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246700447775372132351831 3370050671663058198527747)
                ·
                  refine ⟨5055076007494587297791621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370050671663058198527747 5055076007494587297791621)
                  ·
                    refine ⟨947826751405235118335929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055076007494587297791621 947826751405235118335929)
                    ·
                      rfl

theorem cell22_2768829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2768829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768829 prefixEnd_2768829 := by exact prefixLift 2768829
  have htrace : WordTrace (prefixWord ++ tailWord_2768829) baseStart_2768829 baseEnd_2768829 := by
    simpa [prefixWord, tailWord_2768829, baseEnd_2768829] using wordTrace_append hprefix tailTrace_2768829
  have hstable : (prefixWord ++ tailWord_2768829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768829).length < 2 ^ (prefixWord ++ tailWord_2768829).sum := by decide
  have hdescent : baseEnd_2768829 < baseStart_2768829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768842 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2768842 : Nat := 118140960795 + 2768842 * 2 ^ 59
def prefixEnd_2768842 : Nat := 4983230072969 + 3 ^ 40 * 2768842 * 2
def baseEnd_2768842 : Nat := 947831201570907417760889

theorem tailTrace_2768842 : CollatzResearch.WordTrace tailWord_2768842 prefixEnd_2768842 947831201570907417760889 := by
  unfold tailWord_2768842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25246991058741447352691195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67325309489977192940509853 25246991058741447352691195)
  ·
    refine ⟨37870486588112171029036793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25246991058741447352691195 37870486588112171029036793)
    ·
      refine ⟨28402864941084128271777595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37870486588112171029036793 28402864941084128271777595)
      ·
        refine ⟨42604297411626192407666393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28402864941084128271777595 42604297411626192407666393)
        ·
          refine ⟨31953223058719644305749795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42604297411626192407666393 31953223058719644305749795)
          ·
            refine ⟨47929834588079466458624693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31953223058719644305749795 47929834588079466458624693)
            ·
              refine ⟨4493421992632449980496065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47929834588079466458624693 4493421992632449980496065)
              ·
                refine ⟨3370066494474337485372049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4493421992632449980496065 3370066494474337485372049)
                ·
                  refine ⟨2527549870855753114029037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3370066494474337485372049 2527549870855753114029037)
                  ·
                    refine ⟨947831201570907417760889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527549870855753114029037 947831201570907417760889)
                    ·
                      rfl

theorem cell22_2768842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2768842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768842 prefixEnd_2768842 := by exact prefixLift 2768842
  have htrace : WordTrace (prefixWord ++ tailWord_2768842) baseStart_2768842 baseEnd_2768842 := by
    simpa [prefixWord, tailWord_2768842, baseEnd_2768842] using wordTrace_append hprefix tailTrace_2768842
  have hstable : (prefixWord ++ tailWord_2768842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768842).length < 2 ^ (prefixWord ++ tailWord_2768842).sum := by decide
  have hdescent : baseEnd_2768842 < baseStart_2768842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768913 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 10]
def baseStart_2768913 : Nat := 118140960795 + 2768913 * 2 ^ 59
def prefixEnd_2768913 : Nat := 4983230072969 + 3 ^ 40 * 2768913 * 2
def baseEnd_2768913 : Nat := 947855506321886899235671

theorem tailTrace_2768913 : CollatzResearch.WordTrace tailWord_2768913 prefixEnd_2768913 947855506321886899235671 := by
  unfold tailWord_2768913
  simp only [CollatzResearch.WordTrace]
  refine ⟨100990553817708568536599393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67327035878472379024399595 100990553817708568536599393)
  ·
    refine ⟨75742915363281426402449545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100990553817708568536599393 75742915363281426402449545)
    ·
      refine ⟨56807186522461069801837159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75742915363281426402449545 56807186522461069801837159)
      ·
        refine ⟨85210779783691604702755739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56807186522461069801837159 85210779783691604702755739)
        ·
          refine ⟨127816169675537407054133609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85210779783691604702755739 127816169675537407054133609)
          ·
            refine ⟨95862127256653055290600207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127816169675537407054133609 95862127256653055290600207)
            ·
              refine ⟨143793190884979582935900311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95862127256653055290600207 143793190884979582935900311)
              ·
                refine ⟨215689786327469374403850467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143793190884979582935900311 215689786327469374403850467)
                ·
                  refine ⟨323534679491204061605775701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215689786327469374403850467 323534679491204061605775701)
                  ·
                    refine ⟨947855506321886899235671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 323534679491204061605775701 947855506321886899235671)
                    ·
                      rfl

theorem cell22_2768913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_2768913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768913 prefixEnd_2768913 := by exact prefixLift 2768913
  have htrace : WordTrace (prefixWord ++ tailWord_2768913) baseStart_2768913 baseEnd_2768913 := by
    simpa [prefixWord, tailWord_2768913, baseEnd_2768913] using wordTrace_append hprefix tailTrace_2768913
  have hstable : (prefixWord ++ tailWord_2768913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768913).length < 2 ^ (prefixWord ++ tailWord_2768913).sum := by decide
  have hdescent : baseEnd_2768913 < baseStart_2768913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768917 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 5]
def baseStart_2768917 : Nat := 118140960795 + 2768917 * 2 ^ 59
def prefixEnd_2768917 : Nat := 4983230072969 + 3 ^ 40 * 2768917 * 2
def baseEnd_2768917 : Nat := 315952291867877407378553

theorem tailTrace_2768917 : CollatzResearch.WordTrace tailWord_2768917 prefixEnd_2768917 315952291867877407378553 := by
  unfold tailWord_2768917
  simp only [CollatzResearch.WordTrace]
  refine ⟨100990699709694077219745005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67327133139796051479830003 100990699709694077219745005)
  ·
    refine ⟨37871512391135278957404377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100990699709694077219745005 37871512391135278957404377)
    ·
      refine ⟨28403634293351459218053283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37871512391135278957404377 28403634293351459218053283)
      ·
        refine ⟨42605451440027188827079925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28403634293351459218053283 42605451440027188827079925)
        ·
          refine ⟨3994261072502548952538743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42605451440027188827079925 3994261072502548952538743)
          ·
            refine ⟨5991391608753823428808115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994261072502548952538743 5991391608753823428808115)
            ·
              refine ⟨8987087413130735143212173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5991391608753823428808115 8987087413130735143212173)
              ·
                refine ⟨3370157779924025678704565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8987087413130735143212173 3370157779924025678704565)
                ·
                  refine ⟨315952291867877407378553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370157779924025678704565 315952291867877407378553)
                  ·
                    rfl

theorem cell22_2768917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_2768917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768917 prefixEnd_2768917 := by exact prefixLift 2768917
  have htrace : WordTrace (prefixWord ++ tailWord_2768917) baseStart_2768917 baseEnd_2768917 := by
    simpa [prefixWord, tailWord_2768917, baseEnd_2768917] using wordTrace_append hprefix tailTrace_2768917
  have hstable : (prefixWord ++ tailWord_2768917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768917).length < 2 ^ (prefixWord ++ tailWord_2768917).sum := by decide
  have hdescent : baseEnd_2768917 < baseStart_2768917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2768992 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_2768992 : Nat := 118140960795 + 2768992 * 2 ^ 59
def prefixEnd_2768992 : Nat := 4983230072969 + 3 ^ 40 * 2768992 * 2
def baseEnd_2768992 : Nat := 947882549636357026510429

theorem tailTrace_2768992 : CollatzResearch.WordTrace tailWord_2768992 prefixEnd_2768992 947882549636357026510429 := by
  unfold tailWord_2768992
  simp only [CollatzResearch.WordTrace]
  refine ⟨50496717592211182514362615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67328956789614910019150153 50496717592211182514362615)
  ·
    refine ⟨75745076388316773771543923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50496717592211182514362615 75745076388316773771543923)
    ·
      refine ⟨113617614582475160657315885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75745076388316773771543923 113617614582475160657315885)
      ·
        refine ⟨42606605468428185246493457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113617614582475160657315885 42606605468428185246493457)
        ·
          refine ⟨31954954101321138934870093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42606605468428185246493457 31954954101321138934870093)
          ·
            refine ⟨11983107787995427100576285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31954954101321138934870093 11983107787995427100576285)
            ·
              refine ⟨4493665420498285162716107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11983107787995427100576285 4493665420498285162716107)
              ·
                refine ⟨6740498130747427744074161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493665420498285162716107 6740498130747427744074161)
                ·
                  refine ⟨5055373598060570808055621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6740498130747427744074161 5055373598060570808055621)
                  ·
                    refine ⟨947882549636357026510429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5055373598060570808055621 947882549636357026510429)
                    ·
                      rfl

theorem cell22_2768992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_2768992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2768992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2768992 prefixEnd_2768992 := by exact prefixLift 2768992
  have htrace : WordTrace (prefixWord ++ tailWord_2768992) baseStart_2768992 baseEnd_2768992 := by
    simpa [prefixWord, tailWord_2768992, baseEnd_2768992] using wordTrace_append hprefix tailTrace_2768992
  have hstable : (prefixWord ++ tailWord_2768992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2768992).length < 2 ^ (prefixWord ++ tailWord_2768992).sum := by decide
  have hdescent : baseEnd_2768992 < baseStart_2768992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2768992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769056 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 1, 3]
def baseStart_2769056 : Nat := 118140960795 + 2769056 * 2 ^ 59
def prefixEnd_2769056 : Nat := 4983230072969 + 3 ^ 40 * 2769056 * 2
def baseEnd_2769056 : Nat := 947904458144282192910233

theorem tailTrace_2769056 : CollatzResearch.WordTrace tailWord_2769056 prefixEnd_2769056 947904458144282192910233 := by
  unfold tailWord_2769056
  simp only [CollatzResearch.WordTrace]
  refine ⟨50497884728095251979527511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67330512970793669306036681 50497884728095251979527511)
  ·
    refine ⟨75746827092142877969291267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50497884728095251979527511 75746827092142877969291267)
    ·
      refine ⟨113620240638214316953936901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75746827092142877969291267 113620240638214316953936901)
      ·
        refine ⟨21303795119665184428863169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113620240638214316953936901 21303795119665184428863169)
        ·
          refine ⟨15977846339748888321647377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21303795119665184428863169 15977846339748888321647377)
          ·
            refine ⟨11983384754811666241235533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15977846339748888321647377 11983384754811666241235533)
            ·
              refine ⟨4493769283054374840463325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11983384754811666241235533 4493769283054374840463325)
              ·
                refine ⟨1685163481145390565173747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4493769283054374840463325 1685163481145390565173747)
                ·
                  refine ⟨2527745221718085847760621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685163481145390565173747 2527745221718085847760621)
                  ·
                    refine ⟨947904458144282192910233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527745221718085847760621 947904458144282192910233)
                    ·
                      rfl

theorem cell22_2769056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_2769056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769056 prefixEnd_2769056 := by exact prefixLift 2769056
  have htrace : WordTrace (prefixWord ++ tailWord_2769056) baseStart_2769056 baseEnd_2769056 := by
    simpa [prefixWord, tailWord_2769056, baseEnd_2769056] using wordTrace_append hprefix tailTrace_2769056
  have hstable : (prefixWord ++ tailWord_2769056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769056).length < 2 ^ (prefixWord ++ tailWord_2769056).sum := by decide
  have hdescent : baseEnd_2769056 < baseStart_2769056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769073 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 3, 3]
def baseStart_2769073 : Nat := 118140960795 + 2769073 * 2 ^ 59
def prefixEnd_2769073 : Nat := 4983230072969 + 3 ^ 40 * 2769073 * 2
def baseEnd_2769073 : Nat := 947910277591699815235181

theorem tailTrace_2769073 : CollatzResearch.WordTrace tailWord_2769073 prefixEnd_2769073 947910277591699815235181 := by
  unfold tailWord_2769073
  simp only [CollatzResearch.WordTrace]
  refine ⟨100996389497128915862423873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67330926331419277241615915 100996389497128915862423873)
  ·
    refine ⟨75747292122846686896817905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100996389497128915862423873 75747292122846686896817905)
    ·
      refine ⟨56810469092135015172613429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75747292122846686896817905 56810469092135015172613429)
      ·
        refine ⟨5325981477387657672432509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56810469092135015172613429 5325981477387657672432509)
        ·
          refine ⟨1997243054020371627162191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5325981477387657672432509 1997243054020371627162191)
          ·
            refine ⟨2995864581030557440743287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997243054020371627162191 2995864581030557440743287)
            ·
              refine ⟨4493796871545836161114931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995864581030557440743287 4493796871545836161114931)
              ·
                refine ⟨6740695307318754241672397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493796871545836161114931 6740695307318754241672397)
                ·
                  refine ⟨2527760740244532840627149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6740695307318754241672397 2527760740244532840627149)
                  ·
                    refine ⟨947910277591699815235181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2527760740244532840627149 947910277591699815235181)
                    ·
                      rfl

theorem cell22_2769073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_2769073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769073 prefixEnd_2769073 := by exact prefixLift 2769073
  have htrace : WordTrace (prefixWord ++ tailWord_2769073) baseStart_2769073 baseEnd_2769073 := by
    simpa [prefixWord, tailWord_2769073, baseEnd_2769073] using wordTrace_append hprefix tailTrace_2769073
  have hstable : (prefixWord ++ tailWord_2769073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769073).length < 2 ^ (prefixWord ++ tailWord_2769073).sum := by decide
  have hdescent : baseEnd_2769073 < baseStart_2769073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769112 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_2769112 : Nat := 118140960795 + 2769112 * 2 ^ 59
def prefixEnd_2769112 : Nat := 4983230072969 + 3 ^ 40 * 2769112 * 2
def baseEnd_2769112 : Nat := 947923628088716713510061

theorem tailTrace_2769112 : CollatzResearch.WordTrace tailWord_2769112 prefixEnd_2769112 947923628088716713510061 := by
  unfold tailWord_2769112
  simp only [CollatzResearch.WordTrace]
  refine ⟨50498905971993812761546795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67331874629325083682062393 50498905971993812761546795)
  ·
    refine ⟨75748358957990719142320193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50498905971993812761546795 75748358957990719142320193)
    ·
      refine ⟨56811269218493039356740145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75748358957990719142320193 56811269218493039356740145)
      ·
        refine ⟨42608451913869779517555109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56811269218493039356740145 42608451913869779517555109)
        ·
          refine ⟨7989084733850583659541583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42608451913869779517555109 7989084733850583659541583)
          ·
            refine ⟨11983627100775875489312375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989084733850583659541583 11983627100775875489312375)
            ·
              refine ⟨17975440651163813233968563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11983627100775875489312375 17975440651163813233968563)
              ·
                refine ⟨26963160976745719850952845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17975440651163813233968563 26963160976745719850952845)
                ·
                  refine ⟨10111185366279644944107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26963160976745719850952845 10111185366279644944107317)
                  ·
                    refine ⟨947923628088716713510061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10111185366279644944107317 947923628088716713510061)
                    ·
                      rfl

theorem cell22_2769112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_2769112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769112 prefixEnd_2769112 := by exact prefixLift 2769112
  have htrace : WordTrace (prefixWord ++ tailWord_2769112) baseStart_2769112 baseEnd_2769112 := by
    simpa [prefixWord, tailWord_2769112, baseEnd_2769112] using wordTrace_append hprefix tailTrace_2769112
  have hstable : (prefixWord ++ tailWord_2769112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769112).length < 2 ^ (prefixWord ++ tailWord_2769112).sum := by decide
  have hdescent : baseEnd_2769112 < baseStart_2769112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769187 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 7]
def baseStart_2769187 : Nat := 118140960795 + 2769187 * 2 ^ 59
def prefixEnd_2769187 : Nat := 4983230072969 + 3 ^ 40 * 2769187 * 2
def baseEnd_2769187 : Nat := 315983100707147172628277

theorem tailTrace_2769187 : CollatzResearch.WordTrace tailWord_2769187 prefixEnd_2769187 315983100707147172628277 := by
  unfold tailWord_2769187
  simp only [CollatzResearch.WordTrace]
  refine ⟨101000547418715913332073815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67333698279143942221382543 101000547418715913332073815)
  ·
    refine ⟨151500821128073869998110723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101000547418715913332073815 151500821128073869998110723)
    ·
      refine ⟨227251231692110804997166085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151500821128073869998110723 227251231692110804997166085)
      ·
        refine ⟨42609605942270775936968641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227251231692110804997166085 42609605942270775936968641)
        ·
          refine ⟨31957204456703081952726481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42609605942270775936968641 31957204456703081952726481)
          ·
            refine ⟨23967903342527311464544861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31957204456703081952726481 23967903342527311464544861)
            ·
              refine ⟨8987963753447741799204323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23967903342527311464544861 8987963753447741799204323)
              ·
                refine ⟨13481945630171612698806485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8987963753447741799204323 13481945630171612698806485)
                ·
                  refine ⟨315983100707147172628277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13481945630171612698806485 315983100707147172628277)
                  ·
                    rfl

theorem cell22_2769187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 7].length) (baseStart_2769187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769187 prefixEnd_2769187 := by exact prefixLift 2769187
  have htrace : WordTrace (prefixWord ++ tailWord_2769187) baseStart_2769187 baseEnd_2769187 := by
    simpa [prefixWord, tailWord_2769187, baseEnd_2769187] using wordTrace_append hprefix tailTrace_2769187
  have hstable : (prefixWord ++ tailWord_2769187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769187).length < 2 ^ (prefixWord ++ tailWord_2769187).sum := by decide
  have hdescent : baseEnd_2769187 < baseStart_2769187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769281 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2769281 : Nat := 118140960795 + 2769281 * 2 ^ 59
def prefixEnd_2769281 : Nat := 4983230072969 + 3 ^ 40 * 2769281 * 2
def baseEnd_2769281 : Nat := 947981480242456606034543

theorem tailTrace_2769281 : CollatzResearch.WordTrace tailWord_2769281 prefixEnd_2769281 947981480242456606034543 := by
  unfold tailWord_2769281
  simp only [CollatzResearch.WordTrace]
  refine ⟨101003975880375367385995697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67335983920250244923997131 101003975880375367385995697)
  ·
    refine ⟨75752981910281525539496773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101003975880375367385995697 75752981910281525539496773)
    ·
      refine ⟨14203684108177786038655645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75752981910281525539496773 14203684108177786038655645)
      ·
        refine ⟨5326381540566669764495867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14203684108177786038655645 5326381540566669764495867)
        ·
          refine ⟨7989572310850004646743801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326381540566669764495867 7989572310850004646743801)
          ·
            refine ⟨5992179233137503485057851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7989572310850004646743801 5992179233137503485057851)
            ·
              refine ⟨8988268849706255227586777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992179233137503485057851 8988268849706255227586777)
              ·
                refine ⟨6741201637279691420690083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8988268849706255227586777 6741201637279691420690083)
                ·
                  refine ⟨10111802455919537131035125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6741201637279691420690083 10111802455919537131035125)
                  ·
                    refine ⟨947981480242456606034543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10111802455919537131035125 947981480242456606034543)
                    ·
                      rfl

theorem cell22_2769281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2769281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769281 prefixEnd_2769281 := by exact prefixLift 2769281
  have htrace : WordTrace (prefixWord ++ tailWord_2769281) baseStart_2769281 baseEnd_2769281 := by
    simpa [prefixWord, tailWord_2769281, baseEnd_2769281] using wordTrace_append hprefix tailTrace_2769281
  have hstable : (prefixWord ++ tailWord_2769281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769281).length < 2 ^ (prefixWord ++ tailWord_2769281).sum := by decide
  have hdescent : baseEnd_2769281 < baseStart_2769281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769294 : List Nat := [4, 1, 1, 4, 1, 11]
def baseStart_2769294 : Nat := 118140960795 + 2769294 * 2 ^ 59
def prefixEnd_2769294 : Nat := 4983230072969 + 3 ^ 40 * 2769294 * 2
def baseEnd_2769294 : Nat := 11703530005038628462463

theorem tailTrace_2769294 : CollatzResearch.WordTrace tailWord_2769294 prefixEnd_2769294 11703530005038628462463 := by
  unfold tailWord_2769294
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625556253666033825777367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67336300019552180404145957 12625556253666033825777367)
  ·
    refine ⟨18938334380499050738666051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625556253666033825777367 18938334380499050738666051)
    ·
      refine ⟨28407501570748576107999077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18938334380499050738666051 28407501570748576107999077)
      ·
        refine ⟨5326406544515358020249827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28407501570748576107999077 5326406544515358020249827)
        ·
          refine ⟨7989609816773037030374741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326406544515358020249827 7989609816773037030374741)
          ·
            refine ⟨11703530005038628462463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7989609816773037030374741 11703530005038628462463)
            ·
              rfl

theorem cell22_2769294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 11].length) (baseStart_2769294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769294 prefixEnd_2769294 := by exact prefixLift 2769294
  have htrace : WordTrace (prefixWord ++ tailWord_2769294) baseStart_2769294 baseEnd_2769294 := by
    simpa [prefixWord, tailWord_2769294, baseEnd_2769294] using wordTrace_append hprefix tailTrace_2769294
  have hstable : (prefixWord ++ tailWord_2769294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769294).length < 2 ^ (prefixWord ++ tailWord_2769294).sum := by decide
  have hdescent : baseEnd_2769294 < baseStart_2769294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769354 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2769354 : Nat := 118140960795 + 2769354 * 2 ^ 59
def prefixEnd_2769354 : Nat := 4983230072969 + 3 ^ 40 * 2769354 * 2
def baseEnd_2769354 : Nat := 948006469634308748959319

theorem tailTrace_2769354 : CollatzResearch.WordTrace tailWord_2769354 prefixEnd_2769354 948006469634308748959319 := by
  unfold tailWord_2769354
  simp only [CollatzResearch.WordTrace]
  refine ⟨25251659602277725213350779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67337758939407267235602077 25251659602277725213350779)
  ·
    refine ⟨37877489403416587820026169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25251659602277725213350779 37877489403416587820026169)
    ·
      refine ⟨28408117052562440865019627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37877489403416587820026169 28408117052562440865019627)
      ·
        refine ⟨42612175578843661297529441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28408117052562440865019627 42612175578843661297529441)
        ·
          refine ⟨31959131684132745973147081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42612175578843661297529441 31959131684132745973147081)
          ·
            refine ⟨23969348763099559479860311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31959131684132745973147081 23969348763099559479860311)
            ·
              refine ⟨35954023144649339219790467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23969348763099559479860311 35954023144649339219790467)
              ·
                refine ⟨53931034716974008829685701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35954023144649339219790467 53931034716974008829685701)
                ·
                  refine ⟨10112069009432626655566069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53931034716974008829685701 10112069009432626655566069)
                  ·
                    refine ⟨948006469634308748959319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10112069009432626655566069 948006469634308748959319)
                    ·
                      rfl

theorem cell22_2769354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2769354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769354 prefixEnd_2769354 := by exact prefixLift 2769354
  have htrace : WordTrace (prefixWord ++ tailWord_2769354) baseStart_2769354 baseEnd_2769354 := by
    simpa [prefixWord, tailWord_2769354, baseEnd_2769354] using wordTrace_append hprefix tailTrace_2769354
  have hstable : (prefixWord ++ tailWord_2769354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769354).length < 2 ^ (prefixWord ++ tailWord_2769354).sum := by decide
  have hdescent : baseEnd_2769354 < baseStart_2769354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769356 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_2769356 : Nat := 118140960795 + 2769356 * 2 ^ 59
def prefixEnd_2769356 : Nat := 4983230072969 + 3 ^ 40 * 2769356 * 2
def baseEnd_2769356 : Nat := 316002384758393803469771

theorem tailTrace_2769356 : CollatzResearch.WordTrace tailWord_2769356 prefixEnd_2769356 316002384758393803469771 := by
  unfold tailWord_2769356
  simp only [CollatzResearch.WordTrace]
  refine ⟨50503355677551827597487961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67337807570069103463317281 50503355677551827597487961)
  ·
    refine ⟨37877516758163870698115971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50503355677551827597487961 37877516758163870698115971)
    ·
      refine ⟨56816275137245806047173957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37877516758163870698115971 56816275137245806047173957)
      ·
        refine ⟨10653051588233588633845117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56816275137245806047173957 10653051588233588633845117)
        ·
          refine ⟨3994894345587595737691919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10653051588233588633845117 3994894345587595737691919)
          ·
            refine ⟨5992341518381393606537879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3994894345587595737691919 5992341518381393606537879)
            ·
              refine ⟨8988512277572090409806819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992341518381393606537879 8988512277572090409806819)
              ·
                refine ⟨13482768416358135614710229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8988512277572090409806819 13482768416358135614710229)
                ·
                  refine ⟨316002384758393803469771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13482768416358135614710229 316002384758393803469771)
                  ·
                    rfl

theorem cell22_2769356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_2769356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769356 prefixEnd_2769356 := by exact prefixLift 2769356
  have htrace : WordTrace (prefixWord ++ tailWord_2769356) baseStart_2769356 baseEnd_2769356 := by
    simpa [prefixWord, tailWord_2769356, baseEnd_2769356] using wordTrace_append hprefix tailTrace_2769356
  have hstable : (prefixWord ++ tailWord_2769356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769356).length < 2 ^ (prefixWord ++ tailWord_2769356).sum := by decide
  have hdescent : baseEnd_2769356 < baseStart_2769356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769373 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 5]
def baseStart_2769373 : Nat := 118140960795 + 2769373 * 2 ^ 59
def prefixEnd_2769373 : Nat := 4983230072969 + 3 ^ 40 * 2769373 * 2
def baseEnd_2769373 : Nat := 316004324574199677578087

theorem tailTrace_2769373 : CollatzResearch.WordTrace tailWord_2769373 prefixEnd_2769373 316004324574199677578087 := by
  unfold tailWord_2769373
  simp only [CollatzResearch.WordTrace]
  refine ⟨101007331396042067098344773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67338220930694711398896515 101007331396042067098344773)
  ·
    refine ⟨18938874636757887580939645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101007331396042067098344773 18938874636757887580939645)
    ·
      refine ⟨7102077988784207842852367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18938874636757887580939645 7102077988784207842852367)
      ·
        refine ⟨10653116983176311764278551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102077988784207842852367 10653116983176311764278551)
        ·
          refine ⟨15979675474764467646417827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10653116983176311764278551 15979675474764467646417827)
          ·
            refine ⟨23969513212146701469626741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15979675474764467646417827 23969513212146701469626741)
            ·
              refine ⟨2247141863638753262777507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23969513212146701469626741 2247141863638753262777507)
              ·
                refine ⟨3370712795458129894166261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2247141863638753262777507 3370712795458129894166261)
                ·
                  refine ⟨316004324574199677578087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3370712795458129894166261 316004324574199677578087)
                  ·
                    rfl

theorem cell22_2769373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_2769373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769373 prefixEnd_2769373 := by exact prefixLift 2769373
  have htrace : WordTrace (prefixWord ++ tailWord_2769373) baseStart_2769373 baseEnd_2769373 := by
    simpa [prefixWord, tailWord_2769373, baseEnd_2769373] using wordTrace_append hprefix tailTrace_2769373
  have hstable : (prefixWord ++ tailWord_2769373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769373).length < 2 ^ (prefixWord ++ tailWord_2769373).sum := by decide
  have hdescent : baseEnd_2769373 < baseStart_2769373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769394 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_2769394 : Nat := 118140960795 + 2769394 * 2 ^ 59
def prefixEnd_2769394 : Nat := 4983230072969 + 3 ^ 40 * 2769394 * 2
def baseEnd_2769394 : Nat := 948020162451761977959197

theorem tailTrace_2769394 : CollatzResearch.WordTrace tailWord_2769394 prefixEnd_2769394 948020162451761977959197 := by
  unfold tailWord_2769394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25252024332241496921214809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67338731552643991789906157 25252024332241496921214809)
  ·
    refine ⟨18939018249181122690911107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25252024332241496921214809 18939018249181122690911107)
    ·
      refine ⟨28408527373771684036366661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18939018249181122690911107 28408527373771684036366661)
      ·
        refine ⟨5326598882582190756818749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28408527373771684036366661 5326598882582190756818749)
        ·
          refine ⟨1997474580968321533807031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5326598882582190756818749 1997474580968321533807031)
          ·
            refine ⟨2996211871452482300710547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997474580968321533807031 2996211871452482300710547)
            ·
              refine ⟨4494317807178723451065821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996211871452482300710547 4494317807178723451065821)
              ·
                refine ⟨1685369177692021294149683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4494317807178723451065821 1685369177692021294149683)
                ·
                  refine ⟨2528053766538031941224525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685369177692021294149683 2528053766538031941224525)
                  ·
                    refine ⟨948020162451761977959197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528053766538031941224525 948020162451761977959197)
                    ·
                      rfl

theorem cell22_2769394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_2769394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769394 prefixEnd_2769394 := by exact prefixLift 2769394
  have htrace : WordTrace (prefixWord ++ tailWord_2769394) baseStart_2769394 baseEnd_2769394 := by
    simpa [prefixWord, tailWord_2769394, baseEnd_2769394] using wordTrace_append hprefix tailTrace_2769394
  have hstable : (prefixWord ++ tailWord_2769394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769394).length < 2 ^ (prefixWord ++ tailWord_2769394).sum := by decide
  have hdescent : baseEnd_2769394 < baseStart_2769394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769448 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2769448 : Nat := 118140960795 + 2769448 * 2 ^ 59
def prefixEnd_2769448 : Nat := 4983230072969 + 3 ^ 40 * 2769448 * 2
def baseEnd_2769448 : Nat := 948038647755323837109031

theorem tailTrace_2769448 : CollatzResearch.WordTrace tailWord_2769448 prefixEnd_2769448 948038647755323837109031 := by
  unfold tailWord_2769448
  simp only [CollatzResearch.WordTrace]
  refine ⟨50505033435385177453662499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67340044580513569938216665 50505033435385177453662499)
  ·
    refine ⟨75757550153077766180493749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50505033435385177453662499 75757550153077766180493749)
    ·
      refine ⟨7102270326851040579421289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75757550153077766180493749 7102270326851040579421289)
      ·
        refine ⟨5326702745138280434565967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7102270326851040579421289 5326702745138280434565967)
        ·
          refine ⟨7990054117707420651848951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326702745138280434565967 7990054117707420651848951)
          ·
            refine ⟨11985081176561130977773427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990054117707420651848951 11985081176561130977773427)
            ·
              refine ⟨17977621764841696466660141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11985081176561130977773427 17977621764841696466660141)
              ·
                refine ⟨6741608161815636174997553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17977621764841696466660141 6741608161815636174997553)
                ·
                  refine ⟨5056206121361727131248165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741608161815636174997553 5056206121361727131248165)
                  ·
                    refine ⟨948038647755323837109031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056206121361727131248165 948038647755323837109031)
                    ·
                      rfl

theorem cell22_2769448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2769448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769448 prefixEnd_2769448 := by exact prefixLift 2769448
  have htrace : WordTrace (prefixWord ++ tailWord_2769448) baseStart_2769448 baseEnd_2769448 := by
    simpa [prefixWord, tailWord_2769448, baseEnd_2769448] using wordTrace_append hprefix tailTrace_2769448
  have hstable : (prefixWord ++ tailWord_2769448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769448).length < 2 ^ (prefixWord ++ tailWord_2769448).sum := by decide
  have hdescent : baseEnd_2769448 < baseStart_2769448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769536 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_2769536 : Nat := 118140960795 + 2769536 * 2 ^ 59
def prefixEnd_2769536 : Nat := 4983230072969 + 3 ^ 40 * 2769536 * 2
def baseEnd_2769536 : Nat := 316022923984573646969587

theorem tailTrace_2769536 : CollatzResearch.WordTrace tailWord_2769536 prefixEnd_2769536 316022923984573646969587 := by
  unfold tailWord_2769536
  simp only [CollatzResearch.WordTrace]
  refine ⟨50506638247225772968264231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67342184329634363957685641 50506638247225772968264231)
  ·
    refine ⟨75759957370838659452396347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50506638247225772968264231 75759957370838659452396347)
    ·
      refine ⟨113639936056257989178594521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75759957370838659452396347 113639936056257989178594521)
      ·
        refine ⟨85229952042193491883945891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113639936056257989178594521 85229952042193491883945891)
        ·
          refine ⟨127844928063290237825918837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85229952042193491883945891 127844928063290237825918837)
          ·
            refine ⟨11985462005933459796179891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127844928063290237825918837 11985462005933459796179891)
            ·
              refine ⟨17978193008900189694269837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11985462005933459796179891 17978193008900189694269837)
              ·
                refine ⟨6741822378337571135351189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17978193008900189694269837 6741822378337571135351189)
                ·
                  refine ⟨316022923984573646969587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6741822378337571135351189 316022923984573646969587)
                  ·
                    rfl

theorem cell22_2769536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_2769536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769536 prefixEnd_2769536 := by exact prefixLift 2769536
  have htrace : WordTrace (prefixWord ++ tailWord_2769536) baseStart_2769536 baseEnd_2769536 := by
    simpa [prefixWord, tailWord_2769536, baseEnd_2769536] using wordTrace_append hprefix tailTrace_2769536
  have hstable : (prefixWord ++ tailWord_2769536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769536).length < 2 ^ (prefixWord ++ tailWord_2769536).sum := by decide
  have hdescent : baseEnd_2769536 < baseStart_2769536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769583 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 2, 4]
def baseStart_2769583 : Nat := 118140960795 + 2769583 * 2 ^ 59
def prefixEnd_2769583 : Nat := 4983230072969 + 3 ^ 40 * 2769583 * 2
def baseEnd_2769583 : Nat := 948084861014228484983617

theorem tailTrace_2769583 : CollatzResearch.WordTrace tailWord_2769583 prefixEnd_2769583 948084861014228484983617 := by
  unfold tailWord_2769583
  simp only [CollatzResearch.WordTrace]
  refine ⟨101014990725281272963489403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67343327150187515308992935 101014990725281272963489403)
  ·
    refine ⟨151522486087921909445234105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101014990725281272963489403 151522486087921909445234105)
    ·
      refine ⟨113641864565941432083925579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151522486087921909445234105 113641864565941432083925579)
      ·
        refine ⟨170462796848912148125888369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113641864565941432083925579 170462796848912148125888369)
        ·
          refine ⟨127847097636684111094416277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170462796848912148125888369 127847097636684111094416277)
          ·
            refine ⟨5992832701719567707550763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127847097636684111094416277 5992832701719567707550763)
            ·
              refine ⟨8989249052579351561326145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992832701719567707550763 8989249052579351561326145)
              ·
                refine ⟨6741936789434513670994609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8989249052579351561326145 6741936789434513670994609)
                ·
                  refine ⟨5056452592075885253245957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6741936789434513670994609 5056452592075885253245957)
                  ·
                    refine ⟨948084861014228484983617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056452592075885253245957 948084861014228484983617)
                    ·
                      rfl

theorem cell22_2769583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_2769583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769583 prefixEnd_2769583 := by exact prefixLift 2769583
  have htrace : WordTrace (prefixWord ++ tailWord_2769583) baseStart_2769583 baseEnd_2769583 := by
    simpa [prefixWord, tailWord_2769583, baseEnd_2769583] using wordTrace_append hprefix tailTrace_2769583
  have hstable : (prefixWord ++ tailWord_2769583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769583).length < 2 ^ (prefixWord ++ tailWord_2769583).sum := by decide
  have hdescent : baseEnd_2769583 < baseStart_2769583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769598 : List Nat := [4, 2, 1, 1, 2, 1, 4, 7]
def baseStart_2769598 : Nat := 118140960795 + 2769598 * 2 ^ 59
def prefixEnd_2769598 : Nat := 4983230072969 + 3 ^ 40 * 2769598 * 2
def baseEnd_2769598 : Nat := 105343332868974827317619

theorem tailTrace_2769598 : CollatzResearch.WordTrace tailWord_2769598 prefixEnd_2769598 105343332868974827317619 := by
  unfold tailWord_2769598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12626942227528366315660681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67343691880151287016856965 12626942227528366315660681)
  ·
    refine ⟨9470206670646274736745511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12626942227528366315660681 9470206670646274736745511)
    ·
      refine ⟨14205310005969412105118267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9470206670646274736745511 14205310005969412105118267)
      ·
        refine ⟨21307965008954118157677401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14205310005969412105118267 21307965008954118157677401)
        ·
          refine ⟨15980973756715588618258051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21307965008954118157677401 15980973756715588618258051)
          ·
            refine ⟨23971460635073382927387077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15980973756715588618258051 23971460635073382927387077)
            ·
              refine ⟨4494648869076259298885077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23971460635073382927387077 4494648869076259298885077)
              ·
                refine ⟨105343332868974827317619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4494648869076259298885077 105343332868974827317619)
                ·
                  rfl

theorem cell22_2769598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_2769598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769598 prefixEnd_2769598 := by exact prefixLift 2769598
  have htrace : WordTrace (prefixWord ++ tailWord_2769598) baseStart_2769598 baseEnd_2769598 := by
    simpa [prefixWord, tailWord_2769598, baseEnd_2769598] using wordTrace_append hprefix tailTrace_2769598
  have hstable : (prefixWord ++ tailWord_2769598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769598).length < 2 ^ (prefixWord ++ tailWord_2769598).sum := by decide
  have hdescent : baseEnd_2769598 < baseStart_2769598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769606 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2769606 : Nat := 118140960795 + 2769606 * 2 ^ 59
def prefixEnd_2769606 : Nat := 4983230072969 + 3 ^ 40 * 2769606 * 2
def baseEnd_2769606 : Nat := 948092734384264091658547

theorem tailTrace_2769606 : CollatzResearch.WordTrace tailWord_2769606 prefixEnd_2769606 948092734384264091658547 := by
  unfold tailWord_2769606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156744675131185871611771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67343886402798631927717781 3156744675131185871611771)
  ·
    refine ⟨4735117012696778807417657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3156744675131185871611771 4735117012696778807417657)
    ·
      refine ⟨3551337759522584105563243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735117012696778807417657 3551337759522584105563243)
      ·
        refine ⟨5327006639283876158344865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551337759522584105563243 5327006639283876158344865)
        ·
          refine ⟨3995254979462907118758649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5327006639283876158344865 3995254979462907118758649)
          ·
            refine ⟨2996441234597180339068987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3995254979462907118758649 2996441234597180339068987)
            ·
              refine ⟨4494661851895770508603481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996441234597180339068987 4494661851895770508603481)
              ·
                refine ⟨3370996388921827881452611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494661851895770508603481 3370996388921827881452611)
                ·
                  refine ⟨5056494583382741822178917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3370996388921827881452611 5056494583382741822178917)
                  ·
                    refine ⟨948092734384264091658547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056494583382741822178917 948092734384264091658547)
                    ·
                      rfl

theorem cell22_2769606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2769606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769606 prefixEnd_2769606 := by exact prefixLift 2769606
  have htrace : WordTrace (prefixWord ++ tailWord_2769606) baseStart_2769606 baseEnd_2769606 := by
    simpa [prefixWord, tailWord_2769606, baseEnd_2769606] using wordTrace_append hprefix tailTrace_2769606
  have hstable : (prefixWord ++ tailWord_2769606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769606).length < 2 ^ (prefixWord ++ tailWord_2769606).sum := by decide
  have hdescent : baseEnd_2769606 < baseStart_2769606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769647 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 1, 3]
def baseStart_2769647 : Nat := 118140960795 + 2769647 * 2 ^ 59
def prefixEnd_2769647 : Nat := 4983230072969 + 3 ^ 40 * 2769647 * 2
def baseEnd_2769647 : Nat := 948106769522153651383421

theorem tailTrace_2769647 : CollatzResearch.WordTrace tailWord_2769647 prefixEnd_2769647 948106769522153651383421 := by
  unfold tailWord_2769647
  simp only [CollatzResearch.WordTrace]
  refine ⟨101017324997049411893819195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67344883331366274595879463 101017324997049411893819195)
  ·
    refine ⟨151525987495574117840728793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101017324997049411893819195 151525987495574117840728793)
    ·
      refine ⟨113644490621680588380546595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151525987495574117840728793 113644490621680588380546595)
      ·
        refine ⟨170466735932520882570819893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113644490621680588380546595 170466735932520882570819893)
        ·
          refine ⟨15981256493673832741014365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170466735932520882570819893 15981256493673832741014365)
          ·
            refine ⟨5992971185127687277880387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15981256493673832741014365 5992971185127687277880387)
            ·
              refine ⟨8989456777691530916820581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5992971185127687277880387 8989456777691530916820581)
              ·
                refine ⟨1685523145817162046903859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8989456777691530916820581 1685523145817162046903859)
                ·
                  refine ⟨2528284718725743070355789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685523145817162046903859 2528284718725743070355789)
                  ·
                    refine ⟨948106769522153651383421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528284718725743070355789 948106769522153651383421)
                    ·
                      rfl

theorem cell22_2769647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_2769647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769647 prefixEnd_2769647 := by exact prefixLift 2769647
  have htrace : WordTrace (prefixWord ++ tailWord_2769647) baseStart_2769647 baseEnd_2769647 := by
    simpa [prefixWord, tailWord_2769647, baseEnd_2769647] using wordTrace_append hprefix tailTrace_2769647
  have hstable : (prefixWord ++ tailWord_2769647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769647).length < 2 ^ (prefixWord ++ tailWord_2769647).sum := by decide
  have hdescent : baseEnd_2769647 < baseStart_2769647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769673 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_2769673 : Nat := 118140960795 + 2769673 * 2 ^ 59
def prefixEnd_2769673 : Nat := 4983230072969 + 3 ^ 40 * 2769673 * 2
def baseEnd_2769673 : Nat := 948115669853498250233341

theorem tailTrace_2769673 : CollatzResearch.WordTrace tailWord_2769673 prefixEnd_2769673 948115669853498250233341 := by
  unfold tailWord_2769673
  simp only [CollatzResearch.WordTrace]
  refine ⟨101018273294955218334265673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67345515529970145556177115 101018273294955218334265673)
  ·
    refine ⟨75763704971216413750699255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101018273294955218334265673 75763704971216413750699255)
    ·
      refine ⟨113645557456824620626048883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75763704971216413750699255 113645557456824620626048883)
      ·
        refine ⟨170468336185236930939073325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113645557456824620626048883 170468336185236930939073325)
        ·
          refine ⟨63925626069463849102152497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170468336185236930939073325 63925626069463849102152497)
          ·
            refine ⟨47944219552097886826614373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63925626069463849102152497 47944219552097886826614373)
            ·
              refine ⟨8989541166018353779990195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47944219552097886826614373 8989541166018353779990195)
              ·
                refine ⟨13484311749027530669985293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8989541166018353779990195 13484311749027530669985293)
                ·
                  refine ⟨5056616905885324001244485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13484311749027530669985293 5056616905885324001244485)
                  ·
                    refine ⟨948115669853498250233341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056616905885324001244485 948115669853498250233341)
                    ·
                      rfl

theorem cell22_2769673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_2769673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769673 prefixEnd_2769673 := by exact prefixLift 2769673
  have htrace : WordTrace (prefixWord ++ tailWord_2769673) baseStart_2769673 baseEnd_2769673 := by
    simpa [prefixWord, tailWord_2769673, baseEnd_2769673] using wordTrace_append hprefix tailTrace_2769673
  have hstable : (prefixWord ++ tailWord_2769673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769673).length < 2 ^ (prefixWord ++ tailWord_2769673).sum := by decide
  have hdescent : baseEnd_2769673 < baseStart_2769673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769690 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_2769690 : Nat := 118140960795 + 2769690 * 2 ^ 59
def prefixEnd_2769690 : Nat := 4983230072969 + 3 ^ 40 * 2769690 * 2
def baseEnd_2769690 : Nat := 948121489300915872558289

theorem tailTrace_2769690 : CollatzResearch.WordTrace tailWord_2769690 prefixEnd_2769690 948121489300915872558289 := by
  unfold tailWord_2769690
  simp only [CollatzResearch.WordTrace]
  refine ⟨25254723333973407559408631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67345928890595753491756349 25254723333973407559408631)
  ·
    refine ⟨37882085000960111339112947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25254723333973407559408631 37882085000960111339112947)
    ·
      refine ⟨56823127501440167008669421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37882085000960111339112947 56823127501440167008669421)
      ·
        refine ⟨21308672813040062628251033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56823127501440167008669421 21308672813040062628251033)
        ·
          refine ⟨15981504609780046971188275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21308672813040062628251033 15981504609780046971188275)
          ·
            refine ⟨23972256914670070456782413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15981504609780046971188275 23972256914670070456782413)
            ·
              refine ⟨8989596343001276421293405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23972256914670070456782413 8989596343001276421293405)
              ·
                refine ⟨3371098628625478657985027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8989596343001276421293405 3371098628625478657985027)
                ·
                  refine ⟨5056647942938217986977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3371098628625478657985027 5056647942938217986977541)
                  ·
                    refine ⟨948121489300915872558289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5056647942938217986977541 948121489300915872558289)
                    ·
                      rfl

theorem cell22_2769690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_2769690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769690 prefixEnd_2769690 := by exact prefixLift 2769690
  have htrace : WordTrace (prefixWord ++ tailWord_2769690) baseStart_2769690 baseEnd_2769690 := by
    simpa [prefixWord, tailWord_2769690, baseEnd_2769690] using wordTrace_append hprefix tailTrace_2769690
  have hstable : (prefixWord ++ tailWord_2769690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769690).length < 2 ^ (prefixWord ++ tailWord_2769690).sum := by decide
  have hdescent : baseEnd_2769690 < baseStart_2769690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769812 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2769812 : Nat := 118140960795 + 2769812 * 2 ^ 59
def prefixEnd_2769812 : Nat := 4983230072969 + 3 ^ 40 * 2769812 * 2
def baseEnd_2769812 : Nat := 316054417464716073669305

theorem tailTrace_2769812 : CollatzResearch.WordTrace tailWord_2769812 prefixEnd_2769812 316054417464716073669305 := by
  unfold tailWord_2769812
  simp only [CollatzResearch.WordTrace]
  refine ⟨50511671520725822536787845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67348895360967763382383793 50511671520725822536787845)
  ·
    refine ⟨9470938410136091725647721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50511671520725822536787845 9470938410136091725647721)
    ·
      refine ⟨7103203807602068794235791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9470938410136091725647721 7103203807602068794235791)
      ·
        refine ⟨10654805711403103191353687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7103203807602068794235791 10654805711403103191353687)
        ·
          refine ⟨15982208567104654787030531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10654805711403103191353687 15982208567104654787030531)
          ·
            refine ⟨23973312850656982180545797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15982208567104654787030531 23973312850656982180545797)
            ·
              refine ⟨4494996159498184158852337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23973312850656982180545797 4494996159498184158852337)
              ·
                refine ⟨3371247119623638119139253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4494996159498184158852337 3371247119623638119139253)
                ·
                  refine ⟨316054417464716073669305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3371247119623638119139253 316054417464716073669305)
                  ·
                    rfl

theorem cell22_2769812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2769812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769812 prefixEnd_2769812 := by exact prefixLift 2769812
  have htrace : WordTrace (prefixWord ++ tailWord_2769812) baseStart_2769812 baseEnd_2769812 := by
    simpa [prefixWord, tailWord_2769812, baseEnd_2769812] using wordTrace_append hprefix tailTrace_2769812
  have hstable : (prefixWord ++ tailWord_2769812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769812).length < 2 ^ (prefixWord ++ tailWord_2769812).sum := by decide
  have hdescent : baseEnd_2769812 < baseStart_2769812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769814 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2769814 : Nat := 118140960795 + 2769814 * 2 ^ 59
def prefixEnd_2769814 : Nat := 4983230072969 + 3 ^ 40 * 2769814 * 2
def baseEnd_2769814 : Nat := 948163937035020882457909

theorem tailTrace_2769814 : CollatzResearch.WordTrace tailWord_2769814 prefixEnd_2769814 948163937035020882457909 := by
  unfold tailWord_2769814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313963499215274963446781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67348943991629599610098997 6313963499215274963446781)
  ·
    refine ⟨2367736312205728111292543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6313963499215274963446781 2367736312205728111292543)
    ·
      refine ⟨3551604468308592166938815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367736312205728111292543 3551604468308592166938815)
      ·
        refine ⟨5327406702462888250408223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551604468308592166938815 5327406702462888250408223)
        ·
          refine ⟨7991110053694332375612335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327406702462888250408223 7991110053694332375612335)
          ·
            refine ⟨11986665080541498563418503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991110053694332375612335 11986665080541498563418503)
            ·
              refine ⟨17979997620812247845127755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11986665080541498563418503 17979997620812247845127755)
              ·
                refine ⟨26969996431218371767691633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17979997620812247845127755 26969996431218371767691633)
                ·
                  refine ⟨20227497323413778825768725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26969996431218371767691633 20227497323413778825768725)
                  ·
                    refine ⟨948163937035020882457909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20227497323413778825768725 948163937035020882457909)
                    ·
                      rfl

theorem cell22_2769814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2769814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769814 prefixEnd_2769814 := by exact prefixLift 2769814
  have htrace : WordTrace (prefixWord ++ tailWord_2769814) baseStart_2769814 baseEnd_2769814 := by
    simpa [prefixWord, tailWord_2769814, baseEnd_2769814] using wordTrace_append hprefix tailTrace_2769814
  have hstable : (prefixWord ++ tailWord_2769814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769814).length < 2 ^ (prefixWord ++ tailWord_2769814).sum := by decide
  have hdescent : baseEnd_2769814 < baseStart_2769814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769874 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_2769874 : Nat := 118140960795 + 2769874 * 2 ^ 59
def prefixEnd_2769874 : Nat := 4983230072969 + 3 ^ 40 * 2769874 * 2
def baseEnd_2769874 : Nat := 316061492087066908652575

theorem tailTrace_2769874 : CollatzResearch.WordTrace tailWord_2769874 prefixEnd_2769874 316061492087066908652575 := by
  unfold tailWord_2769874
  simp only [CollatzResearch.WordTrace]
  refine ⟨25256401091806757415583169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67350402911484686441555117 25256401091806757415583169)
  ·
    refine ⟨18942300818855068061687377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25256401091806757415583169 18942300818855068061687377)
    ·
      refine ⟨14206725614141301046265533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18942300818855068061687377 14206725614141301046265533)
      ·
        refine ⟨5327522105302987892349575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14206725614141301046265533 5327522105302987892349575)
        ·
          refine ⟨7991283157954481838524363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327522105302987892349575 7991283157954481838524363)
          ·
            refine ⟨11986924736931722757786545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7991283157954481838524363 11986924736931722757786545)
            ·
              refine ⟨8990193552698792068339909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11986924736931722757786545 8990193552698792068339909)
              ·
                refine ⟨1685661291131023512813733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8990193552698792068339909 1685661291131023512813733)
                ·
                  refine ⟨316061492087066908652575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1685661291131023512813733 316061492087066908652575)
                  ·
                    rfl

theorem cell22_2769874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_2769874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769874 prefixEnd_2769874 := by exact prefixLift 2769874
  have htrace : WordTrace (prefixWord ++ tailWord_2769874) baseStart_2769874 baseEnd_2769874 := by
    simpa [prefixWord, tailWord_2769874, baseEnd_2769874] using wordTrace_append hprefix tailTrace_2769874
  have hstable : (prefixWord ++ tailWord_2769874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769874).length < 2 ^ (prefixWord ++ tailWord_2769874).sum := by decide
  have hdescent : baseEnd_2769874 < baseStart_2769874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769902 : List Nat := [4, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2769902 : Nat := 118140960795 + 2769902 * 2 ^ 59
def prefixEnd_2769902 : Nat := 4983230072969 + 3 ^ 40 * 2769902 * 2
def baseEnd_2769902 : Nat := 105354895692601998473071

theorem tailTrace_2769902 : CollatzResearch.WordTrace tailWord_2769902 prefixEnd_2769902 105354895692601998473071 := by
  unfold tailWord_2769902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628328201390698805543995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67351083740750393629567973 12628328201390698805543995)
  ·
    refine ⟨18942492302086048208315993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12628328201390698805543995 18942492302086048208315993)
    ·
      refine ⟨14206869226564536156236995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18942492302086048208315993 14206869226564536156236995)
      ·
        refine ⟨21310303839846804234355493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14206869226564536156236995 21310303839846804234355493)
        ·
          refine ⟨3995681969971275793941655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21310303839846804234355493 3995681969971275793941655)
          ·
            refine ⟨5993522954956913690912483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995681969971275793941655 5993522954956913690912483)
            ·
              refine ⟨8990284432435370536368725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993522954956913690912483 8990284432435370536368725)
              ·
                refine ⟨105354895692601998473071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8990284432435370536368725 105354895692601998473071)
                ·
                  rfl

theorem cell22_2769902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2769902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769902 prefixEnd_2769902 := by exact prefixLift 2769902
  have htrace : WordTrace (prefixWord ++ tailWord_2769902) baseStart_2769902 baseEnd_2769902 := by
    simpa [prefixWord, tailWord_2769902, baseEnd_2769902] using wordTrace_append hprefix tailTrace_2769902
  have hstable : (prefixWord ++ tailWord_2769902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769902).length < 2 ^ (prefixWord ++ tailWord_2769902).sum := by decide
  have hdescent : baseEnd_2769902 < baseStart_2769902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769934 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2769934 : Nat := 118140960795 + 2769934 * 2 ^ 59
def prefixEnd_2769934 : Nat := 4983230072969 + 3 ^ 40 * 2769934 * 2
def baseEnd_2769934 : Nat := 948205015487380569457541

theorem tailTrace_2769934 : CollatzResearch.WordTrace tailWord_2769934 prefixEnd_2769934 948205015487380569457541 := by
  unfold tailWord_2769934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12628474093376207488689607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67351861831339773273011237 12628474093376207488689607)
  ·
    refine ⟨18942711140064311233034411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12628474093376207488689607 18942711140064311233034411)
    ·
      refine ⟨28414066710096466849551617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18942711140064311233034411 28414066710096466849551617)
      ·
        refine ⟨21310550032572350137163713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28414066710096466849551617 21310550032572350137163713)
        ·
          refine ⟨15982912524429262602872785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21310550032572350137163713 15982912524429262602872785)
          ·
            refine ⟨11987184393321946952154589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15982912524429262602872785 11987184393321946952154589)
            ·
              refine ⟨4495194147495730107057971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11987184393321946952154589 4495194147495730107057971)
              ·
                refine ⟨6742791221243595160586957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4495194147495730107057971 6742791221243595160586957)
                ·
                  refine ⟨2528546707966348185220109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6742791221243595160586957 2528546707966348185220109)
                  ·
                    refine ⟨948205015487380569457541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528546707966348185220109 948205015487380569457541)
                    ·
                      rfl

theorem cell22_2769934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2769934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769934 prefixEnd_2769934 := by exact prefixLift 2769934
  have htrace : WordTrace (prefixWord ++ tailWord_2769934) baseStart_2769934 baseEnd_2769934 := by
    simpa [prefixWord, tailWord_2769934, baseEnd_2769934] using wordTrace_append hprefix tailTrace_2769934
  have hstable : (prefixWord ++ tailWord_2769934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769934).length < 2 ^ (prefixWord ++ tailWord_2769934).sum := by decide
  have hdescent : baseEnd_2769934 < baseStart_2769934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769945 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2769945 : Nat := 118140960795 + 2769945 * 2 ^ 59
def prefixEnd_2769945 : Nat := 4983230072969 + 3 ^ 40 * 2769945 * 2
def baseEnd_2769945 : Nat := 948208781012180207432507

theorem tailTrace_2769945 : CollatzResearch.WordTrace tailWord_2769945 prefixEnd_2769945 948208781012180207432507 := by
  unfold tailWord_2769945
  simp only [CollatzResearch.WordTrace]
  refine ⟨101028193949969808788167289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67352129299979872525444859 101028193949969808788167289)
  ·
    refine ⟨75771145462477356591125467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101028193949969808788167289 75771145462477356591125467)
    ·
      refine ⟨113656718193716034886688201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75771145462477356591125467 113656718193716034886688201)
      ·
        refine ⟨85242538645287026165016151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113656718193716034886688201 85242538645287026165016151)
        ·
          refine ⟨127863807967930539247524227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85242538645287026165016151 127863807967930539247524227)
          ·
            refine ⟨191795711951895808871286341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127863807967930539247524227 191795711951895808871286341)
            ·
              refine ⟨35961695990980464163366189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 191795711951895808871286341 35961695990980464163366189)
              ·
                refine ⟨13485635996617674061262321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35961695990980464163366189 13485635996617674061262321)
                ·
                  refine ⟨10114226997463255545946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13485635996617674061262321 10114226997463255545946741)
                  ·
                    refine ⟨948208781012180207432507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10114226997463255545946741 948208781012180207432507)
                    ·
                      rfl

theorem cell22_2769945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2769945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769945 prefixEnd_2769945 := by exact prefixLift 2769945
  have htrace : WordTrace (prefixWord ++ tailWord_2769945) baseStart_2769945 baseEnd_2769945 := by
    simpa [prefixWord, tailWord_2769945, baseEnd_2769945] using wordTrace_append hprefix tailTrace_2769945
  have hstable : (prefixWord ++ tailWord_2769945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769945).length < 2 ^ (prefixWord ++ tailWord_2769945).sum := by decide
  have hdescent : baseEnd_2769945 < baseStart_2769945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2769985 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2769985 : Nat := 118140960795 + 2769985 * 2 ^ 59
def prefixEnd_2769985 : Nat := 4983230072969 + 3 ^ 40 * 2769985 * 2
def baseEnd_2769985 : Nat := 948222473829633436432385

theorem tailTrace_2769985 : CollatzResearch.WordTrace tailWord_2769985 prefixEnd_2769985 948222473829633436432385 := by
  unfold tailWord_2769985
  simp only [CollatzResearch.WordTrace]
  refine ⟨101029652869824895619623409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353101913216597079748939 101029652869824895619623409)
  ·
    refine ⟨75772239652368671714717557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101029652869824895619623409 75772239652368671714717557)
    ·
      refine ⟨7103647467409562973254771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75772239652368671714717557 7103647467409562973254771)
      ·
        refine ⟨10655471201114344459882157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7103647467409562973254771 10655471201114344459882157)
        ·
          refine ⟨3995801700417879172455809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10655471201114344459882157 3995801700417879172455809)
          ·
            refine ⟨2996851275313409379341857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3995801700417879172455809 2996851275313409379341857)
            ·
              refine ⟨2247638456485057034506393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2996851275313409379341857 2247638456485057034506393)
              ·
                refine ⟨1685728842363792775879795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247638456485057034506393 1685728842363792775879795)
                ·
                  refine ⟨2528593263545689163819693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685728842363792775879795 2528593263545689163819693)
                  ·
                    refine ⟨948222473829633436432385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528593263545689163819693 948222473829633436432385)
                    ·
                      rfl

theorem cell22_2769985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2769985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2769985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2769985 prefixEnd_2769985 := by exact prefixLift 2769985
  have htrace : WordTrace (prefixWord ++ tailWord_2769985) baseStart_2769985 baseEnd_2769985 := by
    simpa [prefixWord, tailWord_2769985, baseEnd_2769985] using wordTrace_append hprefix tailTrace_2769985
  have hstable : (prefixWord ++ tailWord_2769985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2769985).length < 2 ^ (prefixWord ++ tailWord_2769985).sum := by decide
  have hdescent : baseEnd_2769985 < baseStart_2769985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2769985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770007 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 6, 3]
def baseStart_2770007 : Nat := 118140960795 + 2770007 * 2 ^ 59
def prefixEnd_2770007 : Nat := 4983230072969 + 3 ^ 40 * 2770007 * 2
def baseEnd_2770007 : Nat := 948230004879232712382317

theorem tailTrace_2770007 : CollatzResearch.WordTrace tailWord_2770007 prefixEnd_2770007 948230004879232712382317 := by
  unfold tailWord_2770007
  simp only [CollatzResearch.WordTrace]
  refine ⟨101030455275745193376924275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67353636850496795584616183 101030455275745193376924275)
  ·
    refine ⟨151545682913617790065386413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101030455275745193376924275 151545682913617790065386413)
    ·
      refine ⟨56829631092606671274519905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151545682913617790065386413 56829631092606671274519905)
      ·
        refine ⟨42622223319455003455889929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56829631092606671274519905 42622223319455003455889929)
        ·
          refine ⟨31966667489591252591917447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42622223319455003455889929 31966667489591252591917447)
          ·
            refine ⟨47950001234386878887876171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31966667489591252591917447 47950001234386878887876171)
            ·
              refine ⟨71925001851580318331814257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47950001234386878887876171 71925001851580318331814257)
              ·
                refine ⟨53943751388685238748860693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71925001851580318331814257 53943751388685238748860693)
                ·
                  refine ⟨2528613346344620566352845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53943751388685238748860693 2528613346344620566352845)
                  ·
                    refine ⟨948230004879232712382317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528613346344620566352845 948230004879232712382317)
                    ·
                      rfl

theorem cell22_2770007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_2770007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770007 prefixEnd_2770007 := by exact prefixLift 2770007
  have htrace : WordTrace (prefixWord ++ tailWord_2770007) baseStart_2770007 baseEnd_2770007 := by
    simpa [prefixWord, tailWord_2770007, baseEnd_2770007] using wordTrace_append hprefix tailTrace_2770007
  have hstable : (prefixWord ++ tailWord_2770007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770007).length < 2 ^ (prefixWord ++ tailWord_2770007).sum := by decide
  have hdescent : baseEnd_2770007 < baseStart_2770007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770026 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_2770026 : Nat := 118140960795 + 2770026 * 2 ^ 59
def prefixEnd_2770026 : Nat := 4983230072969 + 3 ^ 40 * 2770026 * 2
def baseEnd_2770026 : Nat := 316078836322507665385753

theorem tailTrace_2770026 : CollatzResearch.WordTrace tailWord_2770026 prefixEnd_2770026 316078836322507665385753 := by
  unfold tailWord_2770026
  simp only [CollatzResearch.WordTrace]
  refine ⟨25257787065669089905466483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67354098841784239747910621 25257787065669089905466483)
  ·
    refine ⟨37886680598503634858199725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25257787065669089905466483 37886680598503634858199725)
    ·
      refine ⟨14207505224438863071824897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37886680598503634858199725 14207505224438863071824897)
      ·
        refine ⟨10655628918329147303868673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14207505224438863071824897 10655628918329147303868673)
        ·
          refine ⟨7991721688746860477901505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10655628918329147303868673 7991721688746860477901505)
          ·
            refine ⟨5993791266560145358426129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7991721688746860477901505 5993791266560145358426129)
            ·
              refine ⟨4495343449920109018819597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5993791266560145358426129 4495343449920109018819597)
              ·
                refine ⟨1685753793720040882057349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4495343449920109018819597 1685753793720040882057349)
                ·
                  refine ⟨316078836322507665385753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1685753793720040882057349 316078836322507665385753)
                  ·
                    rfl

theorem cell22_2770026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_2770026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770026 prefixEnd_2770026 := by exact prefixLift 2770026
  have htrace : WordTrace (prefixWord ++ tailWord_2770026) baseStart_2770026 baseEnd_2770026 := by
    simpa [prefixWord, tailWord_2770026, baseEnd_2770026] using wordTrace_append hprefix tailTrace_2770026
  have hstable : (prefixWord ++ tailWord_2770026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770026).length < 2 ^ (prefixWord ++ tailWord_2770026).sum := by decide
  have hdescent : baseEnd_2770026 < baseStart_2770026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770035 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 9]
def baseStart_2770035 : Nat := 118140960795 + 2770035 * 2 ^ 59
def prefixEnd_2770035 : Nat := 4983230072969 + 3 ^ 40 * 2770035 * 2
def baseEnd_2770035 : Nat := 948239589851449972682231

theorem tailTrace_2770035 : CollatzResearch.WordTrace tailWord_2770035 prefixEnd_2770035 948239589851449972682231 := by
  unfold tailWord_2770035
  simp only [CollatzResearch.WordTrace]
  refine ⟨101031476519643754158943559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67354317679762502772629039 101031476519643754158943559)
  ·
    refine ⟨151547214779465631238415339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101031476519643754158943559 151547214779465631238415339)
    ·
      refine ⟨227320822169198446857623009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151547214779465631238415339 227320822169198446857623009)
      ·
        refine ⟨170490616626898835143217257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227320822169198446857623009 170490616626898835143217257)
        ·
          refine ⟨127867962470174126357412943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170490616626898835143217257 127867962470174126357412943)
          ·
            refine ⟨191801943705261189536119415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127867962470174126357412943 191801943705261189536119415)
            ·
              refine ⟨287702915557891784304179123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191801943705261189536119415 287702915557891784304179123)
              ·
                refine ⟨431554373336837676456268685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287702915557891784304179123 431554373336837676456268685)
                ·
                  refine ⟨161832890001314128671100757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 431554373336837676456268685 161832890001314128671100757)
                  ·
                    refine ⟨948239589851449972682231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 161832890001314128671100757 948239589851449972682231)
                    ·
                      rfl

theorem cell22_2770035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_2770035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770035 prefixEnd_2770035 := by exact prefixLift 2770035
  have htrace : WordTrace (prefixWord ++ tailWord_2770035) baseStart_2770035 baseEnd_2770035 := by
    simpa [prefixWord, tailWord_2770035, baseEnd_2770035] using wordTrace_append hprefix tailTrace_2770035
  have hstable : (prefixWord ++ tailWord_2770035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770035).length < 2 ^ (prefixWord ++ tailWord_2770035).sum := by decide
  have hdescent : baseEnd_2770035 < baseStart_2770035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770103 : List Nat := [1, 1, 3, 1, 4, 1, 5, 2, 1, 3]
def baseStart_2770103 : Nat := 118140960795 + 2770103 * 2 ^ 59
def prefixEnd_2770103 : Nat := 4983230072969 + 3 ^ 40 * 2770103 * 2
def baseEnd_2770103 : Nat := 948262867641120461982023

theorem tailTrace_2770103 : CollatzResearch.WordTrace tailWord_2770103 prefixEnd_2770103 948262867641120461982023 := by
  unfold tailWord_2770103
  simp only [CollatzResearch.WordTrace]
  refine ⟨101033956683397401772418963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67355971122264934514945975 101033956683397401772418963)
  ·
    refine ⟨151550935025096102658628445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101033956683397401772418963 151550935025096102658628445)
    ·
      refine ⟨56831600634411038496985667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151550935025096102658628445 56831600634411038496985667)
      ·
        refine ⟨85247400951616557745478501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56831600634411038496985667 85247400951616557745478501)
        ·
          refine ⟨15983887678428104577277219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85247400951616557745478501 15983887678428104577277219)
          ·
            refine ⟨23975831517642156865915829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15983887678428104577277219 23975831517642156865915829)
            ·
              refine ⟨2247734204778952206179609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23975831517642156865915829 2247734204778952206179609)
              ·
                refine ⟨1685800653584214154634707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2247734204778952206179609 1685800653584214154634707)
                ·
                  refine ⟨2528700980376321231952061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685800653584214154634707 2528700980376321231952061)
                  ·
                    refine ⟨948262867641120461982023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528700980376321231952061 948262867641120461982023)
                    ·
                      rfl

theorem cell22_2770103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_2770103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770103 prefixEnd_2770103 := by exact prefixLift 2770103
  have htrace : WordTrace (prefixWord ++ tailWord_2770103) baseStart_2770103 baseEnd_2770103 := by
    simpa [prefixWord, tailWord_2770103, baseEnd_2770103] using wordTrace_append hprefix tailTrace_2770103
  have hstable : (prefixWord ++ tailWord_2770103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770103).length < 2 ^ (prefixWord ++ tailWord_2770103).sum := by decide
  have hdescent : baseEnd_2770103 < baseStart_2770103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770116 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_2770116 : Nat := 118140960795 + 2770116 * 2 ^ 59
def prefixEnd_2770116 : Nat := 4983230072969 + 3 ^ 40 * 2770116 * 2
def baseEnd_2770116 : Nat := 316089105935597587135661

theorem tailTrace_2770116 : CollatzResearch.WordTrace tailWord_2770116 prefixEnd_2770116 316089105935597587135661 := by
  unfold tailWord_2770116
  simp only [CollatzResearch.WordTrace]
  refine ⟨50517215416175152496321101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67356287221566869995094801 50517215416175152496321101)
  ·
    refine ⟨18943955781065682186120413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50517215416175152496321101 18943955781065682186120413)
    ·
      refine ⟨7103983417899630819795155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18943955781065682186120413 7103983417899630819795155)
      ·
        refine ⟨10655975126849446229692733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7103983417899630819795155 10655975126849446229692733)
        ·
          refine ⟨3995990672568542336134775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10655975126849446229692733 3995990672568542336134775)
          ·
            refine ⟨5993986008852813504202163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3995990672568542336134775 5993986008852813504202163)
            ·
              refine ⟨8990979013279220256303245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5993986008852813504202163 8990979013279220256303245)
              ·
                refine ⟨3371617129979707596113717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8990979013279220256303245 3371617129979707596113717)
                ·
                  refine ⟨316089105935597587135661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3371617129979707596113717 316089105935597587135661)
                  ·
                    rfl

theorem cell22_2770116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_2770116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770116 prefixEnd_2770116 := by exact prefixLift 2770116
  have htrace : WordTrace (prefixWord ++ tailWord_2770116) baseStart_2770116 baseEnd_2770116 := by
    simpa [prefixWord, tailWord_2770116, baseEnd_2770116] using wordTrace_append hprefix tailTrace_2770116
  have hstable : (prefixWord ++ tailWord_2770116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770116).length < 2 ^ (prefixWord ++ tailWord_2770116).sum := by decide
  have hdescent : baseEnd_2770116 < baseStart_2770116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770210 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_2770210 : Nat := 118140960795 + 2770210 * 2 ^ 59
def prefixEnd_2770210 : Nat := 4983230072969 + 3 ^ 40 * 2770210 * 2
def baseEnd_2770210 : Nat := 948299495927807849556695

theorem tailTrace_2770210 : CollatzResearch.WordTrace tailWord_2770210 prefixEnd_2770210 948299495927807849556695 := by
  unfold tailWord_2770210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25259464823502439761641021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67358572862673172697709389 25259464823502439761641021)
  ·
    refine ⟨9472299308813414910615383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25259464823502439761641021 9472299308813414910615383)
    ·
      refine ⟨14208448963220122365923075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9472299308813414910615383 14208448963220122365923075)
      ·
        refine ⟨21312673444830183548884613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14208448963220122365923075 21312673444830183548884613)
        ·
          refine ⟨3996126270905659415415865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21312673444830183548884613 3996126270905659415415865)
          ·
            refine ⟨2997094703179244561561899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3996126270905659415415865 2997094703179244561561899)
            ·
              refine ⟨4495642054768866842342849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997094703179244561561899 4495642054768866842342849)
              ·
                refine ⟨3371731541076650131757137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4495642054768866842342849 3371731541076650131757137)
                ·
                  refine ⟨2528798655807487598817853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3371731541076650131757137 2528798655807487598817853)
                  ·
                    refine ⟨948299495927807849556695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528798655807487598817853 948299495927807849556695)
                    ·
                      rfl

theorem cell22_2770210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_2770210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770210 prefixEnd_2770210 := by exact prefixLift 2770210
  have htrace : WordTrace (prefixWord ++ tailWord_2770210) baseStart_2770210 baseEnd_2770210 := by
    simpa [prefixWord, tailWord_2770210, baseEnd_2770210] using wordTrace_append hprefix tailTrace_2770210
  have hstable : (prefixWord ++ tailWord_2770210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770210).length < 2 ^ (prefixWord ++ tailWord_2770210).sum := by decide
  have hdescent : baseEnd_2770210 < baseStart_2770210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770309 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2770309 : Nat := 118140960795 + 2770309 * 2 ^ 59
def prefixEnd_2770309 : Nat := 4983230072969 + 3 ^ 40 * 2770309 * 2
def baseEnd_2770309 : Nat := 948333385651004591331391

theorem tailTrace_2770309 : CollatzResearch.WordTrace tailWord_2770309 prefixEnd_2770309 948333385651004591331391 := by
  unfold tailWord_2770309
  simp only [CollatzResearch.WordTrace]
  refine ⟨101041470120651098954417981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67360980080434065969611987 101041470120651098954417981)
  ·
    refine ⟨37890551295244162107906743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101041470120651098954417981 37890551295244162107906743)
    ·
      refine ⟨56835826942866243161860115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37890551295244162107906743 56835826942866243161860115)
      ·
        refine ⟨85253740414299364742790173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56835826942866243161860115 85253740414299364742790173)
        ·
          refine ⟨31970152655362261778546315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85253740414299364742790173 31970152655362261778546315)
          ·
            refine ⟨47955228983043392667819473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31970152655362261778546315 47955228983043392667819473)
            ·
              refine ⟨35966421737282544500864605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47955228983043392667819473 35966421737282544500864605)
              ·
                refine ⟨13487408151480954187824227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35966421737282544500864605 13487408151480954187824227)
                ·
                  refine ⟨20231112227221431281736341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13487408151480954187824227 20231112227221431281736341)
                  ·
                    refine ⟨948333385651004591331391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20231112227221431281736341 948333385651004591331391)
                    ·
                      rfl

theorem cell22_2770309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2770309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770309 prefixEnd_2770309 := by exact prefixLift 2770309
  have htrace : WordTrace (prefixWord ++ tailWord_2770309) baseStart_2770309 baseEnd_2770309 := by
    simpa [prefixWord, tailWord_2770309, baseEnd_2770309] using wordTrace_append hprefix tailTrace_2770309
  have hstable : (prefixWord ++ tailWord_2770309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770309).length < 2 ^ (prefixWord ++ tailWord_2770309).sum := by decide
  have hdescent : baseEnd_2770309 < baseStart_2770309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770311 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2770311 : Nat := 118140960795 + 2770311 * 2 ^ 59
def prefixEnd_2770311 : Nat := 4983230072969 + 3 ^ 40 * 2770311 * 2
def baseEnd_2770311 : Nat := 948334070291877252781385

theorem tailTrace_2770311 : CollatzResearch.WordTrace tailWord_2770311 prefixEnd_2770311 948334070291877252781385 := by
  unfold tailWord_2770311
  simp only [CollatzResearch.WordTrace]
  refine ⟨101041543066643853295990787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67361028711095902197327191 101041543066643853295990787)
  ·
    refine ⟨151562314599965779943986181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101041543066643853295990787 151562314599965779943986181)
    ·
      refine ⟨28417933987493583739497409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151562314599965779943986181 28417933987493583739497409)
      ·
        refine ⟨21313450490620187804623057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28417933987493583739497409 21313450490620187804623057)
        ·
          refine ⟨15985087867965140853467293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21313450490620187804623057 15985087867965140853467293)
          ·
            refine ⟨5994407950486927820050235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15985087867965140853467293 5994407950486927820050235)
            ·
              refine ⟨8991611925730391730075353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5994407950486927820050235 8991611925730391730075353)
              ·
                refine ⟨6743708944297793797556515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8991611925730391730075353 6743708944297793797556515)
                ·
                  refine ⟨10115563416446690696334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6743708944297793797556515 10115563416446690696334773)
                  ·
                    refine ⟨948334070291877252781385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10115563416446690696334773 948334070291877252781385)
                    ·
                      rfl

theorem cell22_2770311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2770311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770311 prefixEnd_2770311 := by exact prefixLift 2770311
  have htrace : WordTrace (prefixWord ++ tailWord_2770311) baseStart_2770311 baseEnd_2770311 := by
    simpa [prefixWord, tailWord_2770311, baseEnd_2770311] using wordTrace_append hprefix tailTrace_2770311
  have hstable : (prefixWord ++ tailWord_2770311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770311).length < 2 ^ (prefixWord ++ tailWord_2770311).sum := by decide
  have hdescent : baseEnd_2770311 < baseStart_2770311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_2770384 : Nat := 118140960795 + 2770384 * 2 ^ 59
def prefixEnd_2770384 : Nat := 4983230072969 + 3 ^ 40 * 2770384 * 2
def baseEnd_2770384 : Nat := 948359059683729395706161

theorem tailTrace_2770384 : CollatzResearch.WordTrace tailWord_2770384 prefixEnd_2770384 948359059683729395706161 := by
  unfold tailWord_2770384
  simp only [CollatzResearch.WordTrace]
  refine ⟨50522102797689693381699103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67362803730252924508932137 50522102797689693381699103)
  ·
    refine ⟨75783154196534540072548655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50522102797689693381699103 75783154196534540072548655)
    ·
      refine ⟨113674731294801810108822983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75783154196534540072548655 113674731294801810108822983)
      ·
        refine ⟨170512096942202715163234475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113674731294801810108822983 170512096942202715163234475)
        ·
          refine ⟨255768145413304072744851713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170512096942202715163234475 255768145413304072744851713)
          ·
            refine ⟨191826109059978054558638785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255768145413304072744851713 191826109059978054558638785)
            ·
              refine ⟨143869581794983540918979089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191826109059978054558638785 143869581794983540918979089)
              ·
                refine ⟨107902186346237655689234317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143869581794983540918979089 107902186346237655689234317)
                ·
                  refine ⟨40463319879839120883462869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107902186346237655689234317 40463319879839120883462869)
                  ·
                    refine ⟨948359059683729395706161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40463319879839120883462869 948359059683729395706161)
                    ·
                      rfl

theorem cell22_2770384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_2770384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770384 prefixEnd_2770384 := by exact prefixLift 2770384
  have htrace : WordTrace (prefixWord ++ tailWord_2770384) baseStart_2770384 baseEnd_2770384 := by
    simpa [prefixWord, tailWord_2770384, baseEnd_2770384] using wordTrace_append hprefix tailTrace_2770384
  have hstable : (prefixWord ++ tailWord_2770384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770384).length < 2 ^ (prefixWord ++ tailWord_2770384).sum := by decide
  have hdescent : baseEnd_2770384 < baseStart_2770384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770390 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2770390 : Nat := 118140960795 + 2770390 * 2 ^ 59
def prefixEnd_2770390 : Nat := 4983230072969 + 3 ^ 40 * 2770390 * 2
def baseEnd_2770390 : Nat := 948361113606347380056143

theorem tailTrace_2770390 : CollatzResearch.WordTrace tailWord_2770390 prefixEnd_2770390 948361113606347380056143 := by
  unfold tailWord_2770390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6315276527084853111757289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67362949622238433192077749 6315276527084853111757289)
  ·
    refine ⟨4736457395313639833817967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6315276527084853111757289 4736457395313639833817967)
    ·
      refine ⟨7104686092970459750726951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736457395313639833817967 7104686092970459750726951)
      ·
        refine ⟨10657029139455689626090427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7104686092970459750726951 10657029139455689626090427)
        ·
          refine ⟨15985543709183534439135641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10657029139455689626090427 15985543709183534439135641)
          ·
            refine ⟨11989157781887650829351731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15985543709183534439135641 11989157781887650829351731)
            ·
              refine ⟨17983736672831476244027597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11989157781887650829351731 17983736672831476244027597)
              ·
                refine ⟨6743901252311803591510349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17983736672831476244027597 6743901252311803591510349)
                ·
                  refine ⟨2528962969616926346816381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6743901252311803591510349 2528962969616926346816381)
                  ·
                    refine ⟨948361113606347380056143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2528962969616926346816381 948361113606347380056143)
                    ·
                      rfl

theorem cell22_2770390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2770390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770390 prefixEnd_2770390 := by exact prefixLift 2770390
  have htrace : WordTrace (prefixWord ++ tailWord_2770390) baseStart_2770390 baseEnd_2770390 := by
    simpa [prefixWord, tailWord_2770390, baseEnd_2770390] using wordTrace_append hprefix tailTrace_2770390
  have hstable : (prefixWord ++ tailWord_2770390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770390).length < 2 ^ (prefixWord ++ tailWord_2770390).sum := by decide
  have hdescent : baseEnd_2770390 < baseStart_2770390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770401 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2770401 : Nat := 118140960795 + 2770401 * 2 ^ 59
def prefixEnd_2770401 : Nat := 4983230072969 + 3 ^ 40 * 2770401 * 2
def baseEnd_2770401 : Nat := 948364879131147018031109

theorem tailTrace_2770401 : CollatzResearch.WordTrace tailWord_2770401 prefixEnd_2770401 948364879131147018031109 := by
  unfold tailWord_2770401
  simp only [CollatzResearch.WordTrace]
  refine ⟨101044825636317798666767057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67363217090878532444511371 101044825636317798666767057)
  ·
    refine ⟨75783619227238349000075293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101044825636317798666767057 75783619227238349000075293)
    ·
      refine ⟨28418857210214380875028235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75783619227238349000075293 28418857210214380875028235)
      ·
        refine ⟨42628285815321571312542353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28418857210214380875028235 42628285815321571312542353)
        ·
          refine ⟨31971214361491178484406765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42628285815321571312542353 31971214361491178484406765)
          ·
            refine ⟨11989205385559191931652537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31971214361491178484406765 11989205385559191931652537)
            ·
              refine ⟨8991904039169393948739403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11989205385559191931652537 8991904039169393948739403)
              ·
                refine ⟨13487856058754090923109105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8991904039169393948739403 13487856058754090923109105)
                ·
                  refine ⟨10115892044065568192331829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13487856058754090923109105 10115892044065568192331829)
                  ·
                    refine ⟨948364879131147018031109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10115892044065568192331829 948364879131147018031109)
                    ·
                      rfl

theorem cell22_2770401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2770401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770401 prefixEnd_2770401 := by exact prefixLift 2770401
  have htrace : WordTrace (prefixWord ++ tailWord_2770401) baseStart_2770401 baseEnd_2770401 := by
    simpa [prefixWord, tailWord_2770401, baseEnd_2770401] using wordTrace_append hprefix tailTrace_2770401
  have hstable : (prefixWord ++ tailWord_2770401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770401).length < 2 ^ (prefixWord ++ tailWord_2770401).sum := by decide
  have hdescent : baseEnd_2770401 < baseStart_2770401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770467 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 1, 4]
def baseStart_2770467 : Nat := 118140960795 + 2770467 * 2 ^ 59
def prefixEnd_2770467 : Nat := 4983230072969 + 3 ^ 40 * 2770467 * 2
def baseEnd_2770467 : Nat := 948387472279944845880907

theorem tailTrace_2770467 : CollatzResearch.WordTrace tailWord_2770467 prefixEnd_2770467 948387472279944845880907 := by
  unfold tailWord_2770467
  simp only [CollatzResearch.WordTrace]
  refine ⟨101047232854078691938669655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67364821902719127959113103 101047232854078691938669655)
  ·
    refine ⟨151570849281118037908004483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101047232854078691938669655 151570849281118037908004483)
    ·
      refine ⟨227356273921677056862006725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151570849281118037908004483 227356273921677056862006725)
      ·
        refine ⟨42629301360314448161626261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227356273921677056862006725 42629301360314448161626261)
        ·
          refine ⟨1998248501264739757576231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42629301360314448161626261 1998248501264739757576231)
          ·
            refine ⟨2997372751897109636364347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998248501264739757576231 2997372751897109636364347)
            ·
              refine ⟨4496059127845664454546521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997372751897109636364347 4496059127845664454546521)
              ·
                refine ⟨3372044345884248340909891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4496059127845664454546521 3372044345884248340909891)
                ·
                  refine ⟨5058066518826372511364837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372044345884248340909891 5058066518826372511364837)
                  ·
                    refine ⟨948387472279944845880907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5058066518826372511364837 948387472279944845880907)
                    ·
                      rfl

theorem cell22_2770467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 4].length) (baseStart_2770467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770467 prefixEnd_2770467 := by exact prefixLift 2770467
  have htrace : WordTrace (prefixWord ++ tailWord_2770467) baseStart_2770467 baseEnd_2770467 := by
    simpa [prefixWord, tailWord_2770467, baseEnd_2770467] using wordTrace_append hprefix tailTrace_2770467
  have hstable : (prefixWord ++ tailWord_2770467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770467).length < 2 ^ (prefixWord ++ tailWord_2770467).sum := by decide
  have hdescent : baseEnd_2770467 < baseStart_2770467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770493 : List Nat := [1, 4, 1, 3, 4, 9]
def baseStart_2770493 : Nat := 118140960795 + 2770493 * 2 ^ 59
def prefixEnd_2770493 : Nat := 4983230072969 + 3 ^ 40 * 2770493 * 2
def baseEnd_2770493 : Nat := 11708597192731968453467

theorem tailTrace_2770493 : CollatzResearch.WordTrace tailWord_2770493 prefixEnd_2770493 11708597192731968453467 := by
  unfold tailWord_2770493
  simp only [CollatzResearch.WordTrace]
  refine ⟨101048181151984498379116133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67365454101322998919410755 101048181151984498379116133)
  ·
    refine ⟨18946533965997093446084275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101048181151984498379116133 18946533965997093446084275)
    ·
      refine ⟨28419800948995640169126413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18946533965997093446084275 28419800948995640169126413)
      ·
        refine ⟨10657425355873365063422405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28419800948995640169126413 10657425355873365063422405)
        ·
          refine ⟨1998267254226255949391701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10657425355873365063422405 1998267254226255949391701)
          ·
            refine ⟨11708597192731968453467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1998267254226255949391701 11708597192731968453467)
            ·
              rfl

theorem cell22_2770493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 9].length) (baseStart_2770493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770493 prefixEnd_2770493 := by exact prefixLift 2770493
  have htrace : WordTrace (prefixWord ++ tailWord_2770493) baseStart_2770493 baseEnd_2770493 := by
    simpa [prefixWord, tailWord_2770493, baseEnd_2770493] using wordTrace_append hprefix tailTrace_2770493
  have hstable : (prefixWord ++ tailWord_2770493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770493).length < 2 ^ (prefixWord ++ tailWord_2770493).sum := by decide
  have hdescent : baseEnd_2770493 < baseStart_2770493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770506 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2770506 : Nat := 118140960795 + 2770506 * 2 ^ 59
def prefixEnd_2770506 : Nat := 4983230072969 + 3 ^ 40 * 2770506 * 2
def baseEnd_2770506 : Nat := 948400822776961744155787

theorem tailTrace_2770506 : CollatzResearch.WordTrace tailWord_2770506 prefixEnd_2770506 948400822776961744155787 := by
  unfold tailWord_2770506
  simp only [CollatzResearch.WordTrace]
  refine ⟨25262163825234350399834843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67365770200624934399559581 25262163825234350399834843)
  ·
    refine ⟨37893245737851525599752265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25262163825234350399834843 37893245737851525599752265)
    ·
      refine ⟨28419934303388644199814199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37893245737851525599752265 28419934303388644199814199)
      ·
        refine ⟨42629901455082966299721299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28419934303388644199814199 42629901455082966299721299)
        ·
          refine ⟨63944852182624449449581949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42629901455082966299721299 63944852182624449449581949)
          ·
            refine ⟨23979319568484168543593231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63944852182624449449581949 23979319568484168543593231)
            ·
              refine ⟨35968979352726252815389847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23979319568484168543593231 35968979352726252815389847)
              ·
                refine ⟨53953469029089379223084771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35968979352726252815389847 53953469029089379223084771)
                ·
                  refine ⟨80930203543634068834627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53953469029089379223084771 80930203543634068834627157)
                  ·
                    refine ⟨948400822776961744155787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80930203543634068834627157 948400822776961744155787)
                    ·
                      rfl

theorem cell22_2770506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2770506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770506 prefixEnd_2770506 := by exact prefixLift 2770506
  have htrace : WordTrace (prefixWord ++ tailWord_2770506) baseStart_2770506 baseEnd_2770506 := by
    simpa [prefixWord, tailWord_2770506, baseEnd_2770506] using wordTrace_append hprefix tailTrace_2770506
  have hstable : (prefixWord ++ tailWord_2770506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770506).length < 2 ^ (prefixWord ++ tailWord_2770506).sum := by decide
  have hdescent : baseEnd_2770506 < baseStart_2770506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770583 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 6]
def baseStart_2770583 : Nat := 118140960795 + 2770583 * 2 ^ 59
def prefixEnd_2770583 : Nat := 4983230072969 + 3 ^ 40 * 2770583 * 2
def baseEnd_2770583 : Nat := 316142393816853069993517

theorem tailTrace_2770583 : CollatzResearch.WordTrace tailWord_2770583 prefixEnd_2770583 316142393816853069993517 := by
  unfold tailWord_2770583
  simp only [CollatzResearch.WordTrace]
  refine ⟨101051463721658443749892403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67367642481105629166594935 101051463721658443749892403)
  ·
    refine ⟨151577195582487665624838605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101051463721658443749892403 151577195582487665624838605)
    ·
      refine ⟨56841448343432874609314477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151577195582487665624838605 56841448343432874609314477)
      ·
        refine ⟨21315543128787327978492929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56841448343432874609314477 21315543128787327978492929)
        ·
          refine ⟨15986657346590495983869697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21315543128787327978492929 15986657346590495983869697)
          ·
            refine ⟨11989993009942871987902273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15986657346590495983869697 11989993009942871987902273)
            ·
              refine ⟨8992494757457153990926705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11989993009942871987902273 8992494757457153990926705)
              ·
                refine ⟨6744371068092865493195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992494757457153990926705 6744371068092865493195029)
                ·
                  refine ⟨316142393816853069993517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6744371068092865493195029 316142393816853069993517)
                  ·
                    rfl

theorem cell22_2770583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_2770583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770583 prefixEnd_2770583 := by exact prefixLift 2770583
  have htrace : WordTrace (prefixWord ++ tailWord_2770583) baseStart_2770583 baseEnd_2770583 := by
    simpa [prefixWord, tailWord_2770583, baseEnd_2770583] using wordTrace_append hprefix tailTrace_2770583
  have hstable : (prefixWord ++ tailWord_2770583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770583).length < 2 ^ (prefixWord ++ tailWord_2770583).sum := by decide
  have hdescent : baseEnd_2770583 < baseStart_2770583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770615 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 4, 3]
def baseStart_2770615 : Nat := 118140960795 + 2770615 * 2 ^ 59
def prefixEnd_2770615 : Nat := 4983230072969 + 3 ^ 40 * 2770615 * 2
def baseEnd_2770615 : Nat := 948438135704521793180453

theorem tailTrace_2770615 : CollatzResearch.WordTrace tailWord_2770615 prefixEnd_2770615 948438135704521793180453 := by
  unfold tailWord_2770615
  simp only [CollatzResearch.WordTrace]
  refine ⟨101052630857542513215057299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67368420571695008810038199 101052630857542513215057299)
  ·
    refine ⟨151578946286313769822585949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101052630857542513215057299 151578946286313769822585949)
    ·
      refine ⟨56842104857367663683469731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151578946286313769822585949 56842104857367663683469731)
      ·
        refine ⟨85263157286051495525204597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56842104857367663683469731 85263157286051495525204597)
        ·
          refine ⟨7993420995567327705487931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85263157286051495525204597 7993420995567327705487931)
          ·
            refine ⟨11990131493350991558231897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7993420995567327705487931 11990131493350991558231897)
            ·
              refine ⟨8992598620013243668673923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11990131493350991558231897 8992598620013243668673923)
              ·
                refine ⟨13488897930019865503010885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8992598620013243668673923 13488897930019865503010885)
                ·
                  refine ⟨2529168361878724781814541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13488897930019865503010885 2529168361878724781814541)
                  ·
                    refine ⟨948438135704521793180453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529168361878724781814541 948438135704521793180453)
                    ·
                      rfl

theorem cell22_2770615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_2770615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770615 prefixEnd_2770615 := by exact prefixLift 2770615
  have htrace : WordTrace (prefixWord ++ tailWord_2770615) baseStart_2770615 baseEnd_2770615 := by
    simpa [prefixWord, tailWord_2770615, baseEnd_2770615] using wordTrace_append hprefix tailTrace_2770615
  have hstable : (prefixWord ++ tailWord_2770615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770615).length < 2 ^ (prefixWord ++ tailWord_2770615).sum := by decide
  have hdescent : baseEnd_2770615 < baseStart_2770615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770688 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_2770688 : Nat := 118140960795 + 2770688 * 2 ^ 59
def prefixEnd_2770688 : Nat := 4983230072969 + 3 ^ 40 * 2770688 * 2
def baseEnd_2770688 : Nat := 948463125096373936105229

theorem tailTrace_2770688 : CollatzResearch.WordTrace tailWord_2770688 prefixEnd_2770688 948463125096373936105229 := by
  unfold tailWord_2770688
  simp only [CollatzResearch.WordTrace]
  refine ⟨50527646693139023341232359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67370195590852031121643145 50527646693139023341232359)
  ·
    refine ⟨75791470039708535011848539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50527646693139023341232359 75791470039708535011848539)
    ·
      refine ⟨113687205059562802517772809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75791470039708535011848539 113687205059562802517772809)
      ·
        refine ⟨85265403794672101888329607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113687205059562802517772809 85265403794672101888329607)
        ·
          refine ⟨127898105692008152832494411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85265403794672101888329607 127898105692008152832494411)
          ·
            refine ⟨191847158538012229248741617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127898105692008152832494411 191847158538012229248741617)
            ·
              refine ⟨143885368903509171936556213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191847158538012229248741617 143885368903509171936556213)
              ·
                refine ⟨13489253334703984869052145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143885368903509171936556213 13489253334703984869052145)
                ·
                  refine ⟨10116940001027988651789109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13489253334703984869052145 10116940001027988651789109)
                  ·
                    refine ⟨948463125096373936105229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10116940001027988651789109 948463125096373936105229)
                    ·
                      rfl

theorem cell22_2770688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_2770688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770688 prefixEnd_2770688 := by exact prefixLift 2770688
  have htrace : WordTrace (prefixWord ++ tailWord_2770688) baseStart_2770688 baseEnd_2770688 := by
    simpa [prefixWord, tailWord_2770688, baseEnd_2770688] using wordTrace_append hprefix tailTrace_2770688
  have hstable : (prefixWord ++ tailWord_2770688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770688).length < 2 ^ (prefixWord ++ tailWord_2770688).sum := by decide
  have hdescent : baseEnd_2770688 < baseStart_2770688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770769 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 4]
def baseStart_2770769 : Nat := 118140960795 + 2770769 * 2 ^ 59
def prefixEnd_2770769 : Nat := 4983230072969 + 3 ^ 40 * 2770769 * 2
def baseEnd_2770769 : Nat := 316163617683905574943327

theorem tailTrace_2770769 : CollatzResearch.WordTrace tailWord_2770769 prefixEnd_2770769 316163617683905574943327 := by
  unfold tailWord_2770769
  simp only [CollatzResearch.WordTrace]
  refine ⟨101058247698984597516163361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67372165132656398344108907 101058247698984597516163361)
  ·
    refine ⟨75793685774238448137122521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101058247698984597516163361 75793685774238448137122521)
    ·
      refine ⟨56845264330678836102841891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75793685774238448137122521 56845264330678836102841891)
      ·
        refine ⟨85267896496018254154262837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56845264330678836102841891 85267896496018254154262837)
        ·
          refine ⟨7993865296501711326962141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85267896496018254154262837 7993865296501711326962141)
          ·
            refine ⟨2997699486188141747610803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7993865296501711326962141 2997699486188141747610803)
            ·
              refine ⟨4496549229282212621416205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2997699486188141747610803 4496549229282212621416205)
              ·
                refine ⟨1686205960980829733031077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4496549229282212621416205 1686205960980829733031077)
                ·
                  refine ⟨316163617683905574943327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686205960980829733031077 316163617683905574943327)
                  ·
                    rfl

theorem cell22_2770769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_2770769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770769 prefixEnd_2770769 := by exact prefixLift 2770769
  have htrace : WordTrace (prefixWord ++ tailWord_2770769) baseStart_2770769 baseEnd_2770769 := by
    simpa [prefixWord, tailWord_2770769, baseEnd_2770769] using wordTrace_append hprefix tailTrace_2770769
  have hstable : (prefixWord ++ tailWord_2770769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770769).length < 2 ^ (prefixWord ++ tailWord_2770769).sum := by decide
  have hdescent : baseEnd_2770769 < baseStart_2770769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770786 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_2770786 : Nat := 118140960795 + 2770786 * 2 ^ 59
def prefixEnd_2770786 : Nat := 4983230072969 + 3 ^ 40 * 2770786 * 2
def baseEnd_2770786 : Nat := 316165557499711449051643

theorem tailTrace_2770786 : CollatzResearch.WordTrace tailWord_2770786 prefixEnd_2770786 316165557499711449051643 := by
  unfold tailWord_2770786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25264716934980752354883053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67372578493282006279688141 25264716934980752354883053)
  ·
    refine ⟨9474268850617782133081145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25264716934980752354883053 9474268850617782133081145)
    ·
      refine ⟨7105701637963336599810859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9474268850617782133081145 7105701637963336599810859)
      ·
        refine ⟨10658552456945004899716289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7105701637963336599810859 10658552456945004899716289)
        ·
          refine ⟨7993914342708753674787217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10658552456945004899716289 7993914342708753674787217)
          ·
            refine ⟨5995435757031565256090413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7993914342708753674787217 5995435757031565256090413)
            ·
              refine ⟨2248288408886836971033905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5995435757031565256090413 2248288408886836971033905)
              ·
                refine ⟨1686216306665127728275429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248288408886836971033905 1686216306665127728275429)
                ·
                  refine ⟨316165557499711449051643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686216306665127728275429 316165557499711449051643)
                  ·
                    rfl

theorem cell22_2770786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_2770786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770786 prefixEnd_2770786 := by exact prefixLift 2770786
  have htrace : WordTrace (prefixWord ++ tailWord_2770786) baseStart_2770786 baseEnd_2770786 := by
    simpa [prefixWord, tailWord_2770786, baseEnd_2770786] using wordTrace_append hprefix tailTrace_2770786
  have hstable : (prefixWord ++ tailWord_2770786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770786).length < 2 ^ (prefixWord ++ tailWord_2770786).sum := by decide
  have hdescent : baseEnd_2770786 < baseStart_2770786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770842 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_2770842 : Nat := 118140960795 + 2770842 * 2 ^ 59
def prefixEnd_2770842 : Nat := 4983230072969 + 3 ^ 40 * 2770842 * 2
def baseEnd_2770842 : Nat := 316171947481189622584919

theorem tailTrace_2770842 : CollatzResearch.WordTrace tailWord_2770842 prefixEnd_2770842 316171947481189622584919 := by
  unfold tailWord_2770842
  simp only [CollatzResearch.WordTrace]
  refine ⟨25265227556930032745892695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67373940151813420655713853 25265227556930032745892695)
  ·
    refine ⟨37897841335395049118839043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25265227556930032745892695 37897841335395049118839043)
    ·
      refine ⟨56846762003092573678258565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37897841335395049118839043 56846762003092573678258565)
      ·
        refine ⟨10658767875579857564673481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56846762003092573678258565 10658767875579857564673481)
        ·
          refine ⟨7994075906684893173505111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10658767875579857564673481 7994075906684893173505111)
          ·
            refine ⟨11991113860027339760257667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994075906684893173505111 11991113860027339760257667)
            ·
              refine ⟨17986670790041009640386501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11991113860027339760257667 17986670790041009640386501)
              ·
                refine ⟨3372500773132689307572469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17986670790041009640386501 3372500773132689307572469)
                ·
                  refine ⟨316171947481189622584919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3372500773132689307572469 316171947481189622584919)
                  ·
                    rfl

theorem cell22_2770842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_2770842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770842 prefixEnd_2770842 := by exact prefixLift 2770842
  have htrace : WordTrace (prefixWord ++ tailWord_2770842) baseStart_2770842 baseEnd_2770842 := by
    simpa [prefixWord, tailWord_2770842, baseEnd_2770842] using wordTrace_append hprefix tailTrace_2770842
  have hstable : (prefixWord ++ tailWord_2770842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770842).length < 2 ^ (prefixWord ++ tailWord_2770842).sum := by decide
  have hdescent : baseEnd_2770842 < baseStart_2770842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770872 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_2770872 : Nat := 118140960795 + 2770872 * 2 ^ 59
def prefixEnd_2770872 : Nat := 4983230072969 + 3 ^ 40 * 2770872 * 2
def baseEnd_2770872 : Nat := 948526112056658789504665

theorem tailTrace_2770872 : CollatzResearch.WordTrace tailWord_2770872 prefixEnd_2770872 948526112056658789504665 := by
  unfold tailWord_2770872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50531002208805723053581435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67374669611740964071441913 50531002208805723053581435)
  ·
    refine ⟨75796503313208584580372153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50531002208805723053581435 75796503313208584580372153)
    ·
      refine ⟨56847377484906438435279115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75796503313208584580372153 56847377484906438435279115)
      ·
        refine ⟨85271066227359657652918673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56847377484906438435279115 85271066227359657652918673)
        ·
          refine ⟨63953299670519743239689005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85271066227359657652918673 63953299670519743239689005)
          ·
            refine ⟨23982487376444903714883377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63953299670519743239689005 23982487376444903714883377)
            ·
              refine ⟨17986865532333677786162533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23982487376444903714883377 17986865532333677786162533)
              ·
                refine ⟨3372537287312564584905475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17986865532333677786162533 3372537287312564584905475)
                ·
                  refine ⟨5058805930968846877358213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372537287312564584905475 5058805930968846877358213)
                  ·
                    refine ⟨948526112056658789504665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5058805930968846877358213 948526112056658789504665)
                    ·
                      rfl

theorem cell22_2770872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_2770872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770872 prefixEnd_2770872 := by exact prefixLift 2770872
  have htrace : WordTrace (prefixWord ++ tailWord_2770872) baseStart_2770872 baseEnd_2770872 := by
    simpa [prefixWord, tailWord_2770872, baseEnd_2770872] using wordTrace_append hprefix tailTrace_2770872
  have hstable : (prefixWord ++ tailWord_2770872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770872).length < 2 ^ (prefixWord ++ tailWord_2770872).sum := by decide
  have hdescent : baseEnd_2770872 < baseStart_2770872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770885 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2770885 : Nat := 118140960795 + 2770885 * 2 ^ 59
def prefixEnd_2770885 : Nat := 4983230072969 + 3 ^ 40 * 2770885 * 2
def baseEnd_2770885 : Nat := 948530562222331088929625

theorem tailTrace_2770885 : CollatzResearch.WordTrace tailWord_2770885 prefixEnd_2770885 948530562222331088929625 := by
  unfold tailWord_2770885
  simp only [CollatzResearch.WordTrace]
  refine ⟨101062478566564349327386109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67374985711042899551590739 101062478566564349327386109)
  ·
    refine ⟨37898429462461630997769791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101062478566564349327386109 37898429462461630997769791)
    ·
      refine ⟨56847644193692446496654687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37898429462461630997769791 56847644193692446496654687)
      ·
        refine ⟨85271466290538669744982031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56847644193692446496654687 85271466290538669744982031)
        ·
          refine ⟨127907199435808004617473047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85271466290538669744982031 127907199435808004617473047)
          ·
            refine ⟨191860799153712006926209571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127907199435808004617473047 191860799153712006926209571)
            ·
              refine ⟨287791198730568010389314357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191860799153712006926209571 287791198730568010389314357)
              ·
                refine ⟨26980424880990750973998221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 287791198730568010389314357 26980424880990750973998221)
                ·
                  refine ⟨10117659330371531615249333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26980424880990750973998221 10117659330371531615249333)
                  ·
                    refine ⟨948530562222331088929625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10117659330371531615249333 948530562222331088929625)
                    ·
                      rfl

theorem cell22_2770885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2770885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770885 prefixEnd_2770885 := by exact prefixLift 2770885
  have htrace : WordTrace (prefixWord ++ tailWord_2770885) baseStart_2770885 baseEnd_2770885 := by
    simpa [prefixWord, tailWord_2770885, baseEnd_2770885] using wordTrace_append hprefix tailTrace_2770885
  have hstable : (prefixWord ++ tailWord_2770885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770885).length < 2 ^ (prefixWord ++ tailWord_2770885).sum := by decide
  have hdescent : baseEnd_2770885 < baseStart_2770885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770947 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 5, 3]
def baseStart_2770947 : Nat := 118140960795 + 2770947 * 2 ^ 59
def prefixEnd_2770947 : Nat := 4983230072969 + 3 ^ 40 * 2770947 * 2
def baseEnd_2770947 : Nat := 948551786089383593879435

theorem tailTrace_2770947 : CollatzResearch.WordTrace tailWord_2770947 prefixEnd_2770947 948551786089383593879435 := by
  unfold tailWord_2770947
  simp only [CollatzResearch.WordTrace]
  refine ⟨101064739892339733916143095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67376493261559822610762063 101064739892339733916143095)
  ·
    refine ⟨151597109838509600874214643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101064739892339733916143095 151597109838509600874214643)
    ·
      refine ⟨227395664757764401311321965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151597109838509600874214643 227395664757764401311321965)
      ·
        refine ⟨85273374284161650491745737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227395664757764401311321965 85273374284161650491745737)
        ·
          refine ⟨63955030713121237868809303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85273374284161650491745737 63955030713121237868809303)
          ·
            refine ⟨95932546069681856803213955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63955030713121237868809303 95932546069681856803213955)
            ·
              refine ⟨143898819104522785204820933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95932546069681856803213955 143898819104522785204820933)
              ·
                refine ⟨26981028582098022225903925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143898819104522785204820933 26981028582098022225903925)
                ·
                  refine ⟨2529471429571689583678493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26981028582098022225903925 2529471429571689583678493)
                  ·
                    refine ⟨948551786089383593879435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529471429571689583678493 948551786089383593879435)
                    ·
                      rfl

theorem cell22_2770947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 5, 3].length) (baseStart_2770947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770947 prefixEnd_2770947 := by exact prefixLift 2770947
  have htrace : WordTrace (prefixWord ++ tailWord_2770947) baseStart_2770947 baseEnd_2770947 := by
    simpa [prefixWord, tailWord_2770947, baseEnd_2770947] using wordTrace_append hprefix tailTrace_2770947
  have hstable : (prefixWord ++ tailWord_2770947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770947).length < 2 ^ (prefixWord ++ tailWord_2770947).sum := by decide
  have hdescent : baseEnd_2770947 < baseStart_2770947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2770998 : List Nat := [5, 1, 2, 1, 1, 1, 2, 5, 1, 3]
def baseStart_2770998 : Nat := 118140960795 + 2770998 * 2 ^ 59
def prefixEnd_2770998 : Nat := 4983230072969 + 3 ^ 40 * 2770998 * 2
def baseEnd_2770998 : Nat := 948569244431636460854279

theorem tailTrace_2770998 : CollatzResearch.WordTrace tailWord_2770998 prefixEnd_2770998 948569244431636460854279 := by
  unfold tailWord_2770998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316662500947185601640603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67377733343436646417499765 6316662500947185601640603)
  ·
    refine ⟨9474993751420778402460905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316662500947185601640603 9474993751420778402460905)
    ·
      refine ⟨7106245313565583801845679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9474993751420778402460905 7106245313565583801845679)
      ·
        refine ⟨10659367970348375702768519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7106245313565583801845679 10659367970348375702768519)
        ·
          refine ⟨15989051955522563554152779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659367970348375702768519 15989051955522563554152779)
          ·
            refine ⟨23983577933283845331229169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15989051955522563554152779 23983577933283845331229169)
            ·
              refine ⟨17987683449962883998421877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23983577933283845331229169 17987683449962883998421877)
              ·
                refine ⟨1686345323434020374852051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17987683449962883998421877 1686345323434020374852051)
                ·
                  refine ⟨2529517985151030562278077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686345323434020374852051 2529517985151030562278077)
                  ·
                    refine ⟨948569244431636460854279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529517985151030562278077 948569244431636460854279)
                    ·
                      rfl

theorem cell22_2770998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_2770998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2770998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2770998 prefixEnd_2770998 := by exact prefixLift 2770998
  have htrace : WordTrace (prefixWord ++ tailWord_2770998) baseStart_2770998 baseEnd_2770998 := by
    simpa [prefixWord, tailWord_2770998, baseEnd_2770998] using wordTrace_append hprefix tailTrace_2770998
  have hstable : (prefixWord ++ tailWord_2770998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2770998).length < 2 ^ (prefixWord ++ tailWord_2770998).sum := by decide
  have hdescent : baseEnd_2770998 < baseStart_2770998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2770998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771054 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2771054 : Nat := 118140960795 + 2771054 * 2 ^ 59
def prefixEnd_2771054 : Nat := 4983230072969 + 3 ^ 40 * 2771054 * 2
def baseEnd_2771054 : Nat := 948588414376070981454107

theorem tailTrace_2771054 : CollatzResearch.WordTrace tailWord_2771054 prefixEnd_2771054 948588414376070981454107 := by
  unfold tailWord_2771054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633580312869011398786027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67379095001968060793525477 12633580312869011398786027)
  ·
    refine ⟨18950370469303517098179041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12633580312869011398786027 18950370469303517098179041)
    ·
      refine ⟨14212777851977637823634281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18950370469303517098179041 14212777851977637823634281)
      ·
        refine ⟨10659583388983228367725711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14212777851977637823634281 10659583388983228367725711)
        ·
          refine ⟨15989375083474842551588567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659583388983228367725711 15989375083474842551588567)
          ·
            refine ⟨23984062625212263827382851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15989375083474842551588567 23984062625212263827382851)
            ·
              refine ⟨35976093937818395741074277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23984062625212263827382851 35976093937818395741074277)
              ·
                refine ⟨6745517613340949201451427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35976093937818395741074277 6745517613340949201451427)
                ·
                  refine ⟨10118276420011423802177141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6745517613340949201451427 10118276420011423802177141)
                  ·
                    refine ⟨948588414376070981454107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10118276420011423802177141 948588414376070981454107)
                    ·
                      rfl

theorem cell22_2771054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2771054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771054 prefixEnd_2771054 := by exact prefixLift 2771054
  have htrace : WordTrace (prefixWord ++ tailWord_2771054) baseStart_2771054 baseEnd_2771054 := by
    simpa [prefixWord, tailWord_2771054, baseEnd_2771054] using wordTrace_append hprefix tailTrace_2771054
  have hstable : (prefixWord ++ tailWord_2771054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771054).length < 2 ^ (prefixWord ++ tailWord_2771054).sum := by decide
  have hdescent : baseEnd_2771054 < baseStart_2771054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771056 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_2771056 : Nat := 118140960795 + 2771056 * 2 ^ 59
def prefixEnd_2771056 : Nat := 4983230072969 + 3 ^ 40 * 2771056 * 2
def baseEnd_2771056 : Nat := 316196366338981214301367

theorem tailTrace_2771056 : CollatzResearch.WordTrace tailWord_2771056 prefixEnd_2771056 316196366338981214301367 := by
  unfold tailWord_2771056
  simp only [CollatzResearch.WordTrace]
  refine ⟨50534357724472422765930511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67379143632629897021240681 50534357724472422765930511)
  ·
    refine ⟨75801536586708634148895767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50534357724472422765930511 75801536586708634148895767)
    ·
      refine ⟨113702304880062951223343651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75801536586708634148895767 113702304880062951223343651)
      ·
        refine ⟨170553457320094426835015477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113702304880062951223343651 170553457320094426835015477)
        ·
          refine ⟨15989386623758852515782701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170553457320094426835015477 15989386623758852515782701)
          ·
            refine ⟨5996019983909569693418513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15989386623758852515782701 5996019983909569693418513)
            ·
              refine ⟨4497014987932177270063885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5996019983909569693418513 4497014987932177270063885)
              ·
                refine ⟨1686380620474566476273957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497014987932177270063885 1686380620474566476273957)
                ·
                  refine ⟨316196366338981214301367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686380620474566476273957 316196366338981214301367)
                  ·
                    rfl

theorem cell22_2771056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_2771056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771056 prefixEnd_2771056 := by exact prefixLift 2771056
  have htrace : WordTrace (prefixWord ++ tailWord_2771056) baseStart_2771056 baseEnd_2771056 := by
    simpa [prefixWord, tailWord_2771056, baseEnd_2771056] using wordTrace_append hprefix tailTrace_2771056
  have hstable : (prefixWord ++ tailWord_2771056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771056).length < 2 ^ (prefixWord ++ tailWord_2771056).sum := by decide
  have hdescent : baseEnd_2771056 < baseStart_2771056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771058 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2771058 : Nat := 118140960795 + 2771058 * 2 ^ 59
def prefixEnd_2771058 : Nat := 4983230072969 + 3 ^ 40 * 2771058 * 2
def baseEnd_2771058 : Nat := 948589783657816304354095

theorem tailTrace_2771058 : CollatzResearch.WordTrace tailWord_2771058 prefixEnd_2771058 948589783657816304354095 := by
  unfold tailWord_2771058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25267197098734399968358457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67379192263291733248955885 25267197098734399968358457)
  ·
    refine ⟨18950397824050799976268843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25267197098734399968358457 18950397824050799976268843)
    ·
      refine ⟨28425596736076199964403265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18950397824050799976268843 28425596736076199964403265)
      ·
        refine ⟨21319197552057149973302449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28425596736076199964403265 21319197552057149973302449)
        ·
          refine ⟨15989398164042862479976837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21319197552057149973302449 15989398164042862479976837)
          ·
            refine ⟨2998012155758036714995657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15989398164042862479976837 2998012155758036714995657)
            ·
              refine ⟨2248509116818527536246743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998012155758036714995657 2248509116818527536246743)
              ·
                refine ⟨3372763675227791304370115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248509116818527536246743 3372763675227791304370115)
                ·
                  refine ⟨5059145512841686956555173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3372763675227791304370115 5059145512841686956555173)
                  ·
                    refine ⟨948589783657816304354095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059145512841686956555173 948589783657816304354095)
                    ·
                      rfl

theorem cell22_2771058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2771058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771058 prefixEnd_2771058 := by exact prefixLift 2771058
  have htrace : WordTrace (prefixWord ++ tailWord_2771058) baseStart_2771058 baseEnd_2771058 := by
    simpa [prefixWord, tailWord_2771058, baseEnd_2771058] using wordTrace_append hprefix tailTrace_2771058
  have hstable : (prefixWord ++ tailWord_2771058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771058).length < 2 ^ (prefixWord ++ tailWord_2771058).sum := by decide
  have hdescent : baseEnd_2771058 < baseStart_2771058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771097 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2771097 : Nat := 118140960795 + 2771097 * 2 ^ 59
def prefixEnd_2771097 : Nat := 4983230072969 + 3 ^ 40 * 2771097 * 2
def baseEnd_2771097 : Nat := 948603134154833202628975

theorem tailTrace_2771097 : CollatzResearch.WordTrace tailWord_2771097 prefixEnd_2771097 948603134154833202628975 := by
  unfold tailWord_2771097
  simp only [CollatzResearch.WordTrace]
  refine ⟨101070210841796309534103545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67380140561197539689402363 101070210841796309534103545)
  ·
    refine ⟨75802658131347232150577659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101070210841796309534103545 75802658131347232150577659)
    ·
      refine ⟨113703987197020848225866489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75802658131347232150577659 113703987197020848225866489)
      ·
        refine ⟨85277990397765636169399867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113703987197020848225866489 85277990397765636169399867)
        ·
          refine ⟨127916985596648454254099801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85277990397765636169399867 127916985596648454254099801)
          ·
            refine ⟨95937739197486340690574851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127916985596648454254099801 95937739197486340690574851)
            ·
              refine ⟨143906608796229511035862277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95937739197486340690574851 143906608796229511035862277)
              ·
                refine ⟨26982489149293033319224177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143906608796229511035862277 26982489149293033319224177)
                ·
                  refine ⟨20236866861969774989418133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26982489149293033319224177 20236866861969774989418133)
                  ·
                    refine ⟨948603134154833202628975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20236866861969774989418133 948603134154833202628975)
                    ·
                      rfl

theorem cell22_2771097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2771097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771097 prefixEnd_2771097 := by exact prefixLift 2771097
  have htrace : WordTrace (prefixWord ++ tailWord_2771097) baseStart_2771097 baseEnd_2771097 := by
    simpa [prefixWord, tailWord_2771097, baseEnd_2771097] using wordTrace_append hprefix tailTrace_2771097
  have hstable : (prefixWord ++ tailWord_2771097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771097).length < 2 ^ (prefixWord ++ tailWord_2771097).sum := by decide
  have hdescent : baseEnd_2771097 < baseStart_2771097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771099 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 3, 3]
def baseStart_2771099 : Nat := 118140960795 + 2771099 * 2 ^ 59
def prefixEnd_2771099 : Nat := 4983230072969 + 3 ^ 40 * 2771099 * 2
def baseEnd_2771099 : Nat := 948603818795705864078969

theorem tailTrace_2771099 : CollatzResearch.WordTrace tailWord_2771099 prefixEnd_2771099 948603818795705864078969 := by
  unfold tailWord_2771099
  simp only [CollatzResearch.WordTrace]
  refine ⟨101070283787789063875676351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67380189191859375917117567 101070283787789063875676351)
  ·
    refine ⟨151605425681683595813514527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101070283787789063875676351 151605425681683595813514527)
    ·
      refine ⟨227408138522525393720271791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151605425681683595813514527 227408138522525393720271791)
      ·
        refine ⟨341112207783788090580407687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227408138522525393720271791 341112207783788090580407687)
        ·
          refine ⟨511668311675682135870611531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341112207783788090580407687 511668311675682135870611531)
          ·
            refine ⟨767502467513523203805917297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511668311675682135870611531 767502467513523203805917297)
            ·
              refine ⟨575626850635142402854437973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767502467513523203805917297 575626850635142402854437973)
              ·
                refine ⟨6745627155880575033450445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 575626850635142402854437973 6745627155880575033450445)
                ·
                  refine ⟨2529610183455215637543917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6745627155880575033450445 2529610183455215637543917)
                  ·
                    refine ⟨948603818795705864078969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529610183455215637543917 948603818795705864078969)
                    ·
                      rfl

theorem cell22_2771099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 3].length) (baseStart_2771099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771099 prefixEnd_2771099 := by exact prefixLift 2771099
  have htrace : WordTrace (prefixWord ++ tailWord_2771099) baseStart_2771099 baseEnd_2771099 := by
    simpa [prefixWord, tailWord_2771099, baseEnd_2771099] using wordTrace_append hprefix tailTrace_2771099
  have hstable : (prefixWord ++ tailWord_2771099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771099).length < 2 ^ (prefixWord ++ tailWord_2771099).sum := by decide
  have hdescent : baseEnd_2771099 < baseStart_2771099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771101 : List Nat := [1, 4, 2, 1, 1, 5, 2, 6]
def baseStart_2771101 : Nat := 118140960795 + 2771101 * 2 ^ 59
def prefixEnd_2771101 : Nat := 4983230072969 + 3 ^ 40 * 2771101 * 2
def baseEnd_2771101 : Nat := 105400500381842058392107

theorem tailTrace_2771101 : CollatzResearch.WordTrace tailWord_2771101 prefixEnd_2771101 105400500381842058392107 := by
  unfold tailWord_2771101
  simp only [CollatzResearch.WordTrace]
  refine ⟨101070356733781818217249157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67380237822521212144832771 101070356733781818217249157)
  ·
    refine ⟨18950691887584090915734217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101070356733781818217249157 18950691887584090915734217)
    ·
      refine ⟨14213018915688068186800663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18950691887584090915734217 14213018915688068186800663)
      ·
        refine ⟨21319528373532102280200995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14213018915688068186800663 21319528373532102280200995)
        ·
          refine ⟨31979292560298153420301493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21319528373532102280200995 31979292560298153420301493)
          ·
            refine ⟨2998058677527951883153265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31979292560298153420301493 2998058677527951883153265)
            ·
              refine ⟨2248544008145963912364949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998058677527951883153265 2248544008145963912364949)
              ·
                refine ⟨105400500381842058392107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2248544008145963912364949 105400500381842058392107)
                ·
                  rfl

theorem cell22_2771101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 6].length) (baseStart_2771101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771101 prefixEnd_2771101 := by exact prefixLift 2771101
  have htrace : WordTrace (prefixWord ++ tailWord_2771101) baseStart_2771101 baseEnd_2771101 := by
    simpa [prefixWord, tailWord_2771101, baseEnd_2771101] using wordTrace_append hprefix tailTrace_2771101
  have hstable : (prefixWord ++ tailWord_2771101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771101).length < 2 ^ (prefixWord ++ tailWord_2771101).sum := by decide
  have hdescent : baseEnd_2771101 < baseStart_2771101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771118 : List Nat := [4, 1, 4, 2, 1, 2, 8]
def baseStart_2771118 : Nat := 118140960795 + 2771118 * 2 ^ 59
def prefixEnd_2771118 : Nat := 4983230072969 + 3 ^ 40 * 2771118 * 2
def baseEnd_2771118 : Nat := 35133715662370227698293

theorem tailTrace_2771118 : CollatzResearch.WordTrace tailWord_2771118 prefixEnd_2771118 35133715662370227698293 := by
  unfold tailWord_2771118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633872096840028765077251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67380651183146820080412005 12633872096840028765077251)
  ·
    refine ⟨18950808145260043147615877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12633872096840028765077251 18950808145260043147615877)
    ·
      refine ⟨3553276527236258090177977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18950808145260043147615877 3553276527236258090177977)
      ·
        refine ⟨2664957395427193567633483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553276527236258090177977 2664957395427193567633483)
        ·
          refine ⟨3997436093140790351450225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664957395427193567633483 3997436093140790351450225)
          ·
            refine ⟨2998077069855592763587669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3997436093140790351450225 2998077069855592763587669)
            ·
              refine ⟨35133715662370227698293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2998077069855592763587669 35133715662370227698293)
              ·
                rfl

theorem cell22_2771118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 8].length) (baseStart_2771118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771118 prefixEnd_2771118 := by exact prefixLift 2771118
  have htrace : WordTrace (prefixWord ++ tailWord_2771118) baseStart_2771118 baseEnd_2771118 := by
    simpa [prefixWord, tailWord_2771118, baseEnd_2771118] using wordTrace_append hprefix tailTrace_2771118
  have hstable : (prefixWord ++ tailWord_2771118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771118).length < 2 ^ (prefixWord ++ tailWord_2771118).sum := by decide
  have hdescent : baseEnd_2771118 < baseStart_2771118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771124 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2771124 : Nat := 118140960795 + 2771124 * 2 ^ 59
def prefixEnd_2771124 : Nat := 4983230072969 + 3 ^ 40 * 2771124 * 2
def baseEnd_2771124 : Nat := 316204125602204710734631

theorem tailTrace_2771124 : CollatzResearch.WordTrace tailWord_2771124 prefixEnd_2771124 316204125602204710734631 := by
  unfold tailWord_2771124
  simp only [CollatzResearch.WordTrace]
  refine ⟨50535597806349246572668213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67380797075132328763557617 50535597806349246572668213)
  ·
    refine ⟨4737712294345241866187645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50535597806349246572668213 4737712294345241866187645)
    ·
      refine ⟨1776642110379465699820367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4737712294345241866187645 1776642110379465699820367)
      ·
        refine ⟨2664963165569198549730551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776642110379465699820367 2664963165569198549730551)
        ·
          refine ⟨3997444748353797824595827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664963165569198549730551 3997444748353797824595827)
          ·
            refine ⟨5996167122530696736893741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997444748353797824595827 5996167122530696736893741)
            ·
              refine ⟨2248562670949011276335153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5996167122530696736893741 2248562670949011276335153)
              ·
                refine ⟨1686422003211758457251365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248562670949011276335153 1686422003211758457251365)
                ·
                  refine ⟨316204125602204710734631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686422003211758457251365 316204125602204710734631)
                  ·
                    rfl

theorem cell22_2771124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2771124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771124 prefixEnd_2771124 := by exact prefixLift 2771124
  have htrace : WordTrace (prefixWord ++ tailWord_2771124) baseStart_2771124 baseEnd_2771124 := by
    simpa [prefixWord, tailWord_2771124, baseEnd_2771124] using wordTrace_append hprefix tailTrace_2771124
  have hstable : (prefixWord ++ tailWord_2771124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771124).length < 2 ^ (prefixWord ++ tailWord_2771124).sum := by decide
  have hdescent : baseEnd_2771124 < baseStart_2771124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771129 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 5]
def baseStart_2771129 : Nat := 118140960795 + 2771129 * 2 ^ 59
def prefixEnd_2771129 : Nat := 4983230072969 + 3 ^ 40 * 2771129 * 2
def baseEnd_2771129 : Nat := 316204696136265261942959

theorem tailTrace_2771129 : CollatzResearch.WordTrace tailWord_2771129 prefixEnd_2771129 316204696136265261942959 := by
  unfold tailWord_2771129
  simp only [CollatzResearch.WordTrace]
  refine ⟨101071377977680378999268441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67380918651786919332845627 101071377977680378999268441)
  ·
    refine ⟨75803533483260284249451331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101071377977680378999268441 75803533483260284249451331)
    ·
      refine ⟨113705300224890426374176997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75803533483260284249451331 113705300224890426374176997)
      ·
        refine ⟨21319743792166954945158187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113705300224890426374176997 21319743792166954945158187)
        ·
          refine ⟨31979615688250432417737281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21319743792166954945158187 31979615688250432417737281)
          ·
            refine ⟨23984711766187824313302961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31979615688250432417737281 23984711766187824313302961)
            ·
              refine ⟨17988533824640868234977221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23984711766187824313302961 17988533824640868234977221)
              ·
                refine ⟨3372850092120162794058229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17988533824640868234977221 3372850092120162794058229)
                ·
                  refine ⟨316204696136265261942959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3372850092120162794058229 316204696136265261942959)
                  ·
                    rfl

theorem cell22_2771129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_2771129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771129 prefixEnd_2771129 := by exact prefixLift 2771129
  have htrace : WordTrace (prefixWord ++ tailWord_2771129) baseStart_2771129 baseEnd_2771129 := by
    simpa [prefixWord, tailWord_2771129, baseEnd_2771129] using wordTrace_append hprefix tailTrace_2771129
  have hstable : (prefixWord ++ tailWord_2771129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771129).length < 2 ^ (prefixWord ++ tailWord_2771129).sum := by decide
  have hdescent : baseEnd_2771129 < baseStart_2771129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771221 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2771221 : Nat := 118140960795 + 2771221 * 2 ^ 59
def prefixEnd_2771221 : Nat := 4983230072969 + 3 ^ 40 * 2771221 * 2
def baseEnd_2771221 : Nat := 948645581888938212528595

theorem tailTrace_2771221 : CollatzResearch.WordTrace tailWord_2771221 prefixEnd_2771221 948645581888938212528595 := by
  unfold tailWord_2771221
  simp only [CollatzResearch.WordTrace]
  refine ⟨101074733493347078711617517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67383155662231385807745011 101074733493347078711617517)
  ·
    refine ⟨37903025060005154516856569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101074733493347078711617517 37903025060005154516856569)
    ·
      refine ⟨28427268795003865887642427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37903025060005154516856569 28427268795003865887642427)
      ·
        refine ⟨42640903192505798831463641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28427268795003865887642427 42640903192505798831463641)
        ·
          refine ⟨31980677394379349123597731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42640903192505798831463641 31980677394379349123597731)
          ·
            refine ⟨47971016091569023685396597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31980677394379349123597731 47971016091569023685396597)
            ·
              refine ⟨4497282758584595970505931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47971016091569023685396597 4497282758584595970505931)
              ·
                refine ⟨6745924137876893955758897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4497282758584595970505931 6745924137876893955758897)
                ·
                  refine ⟨5059443103407670466819173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6745924137876893955758897 5059443103407670466819173)
                  ·
                    refine ⟨948645581888938212528595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5059443103407670466819173 948645581888938212528595)
                    ·
                      rfl

theorem cell22_2771221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2771221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771221 prefixEnd_2771221 := by exact prefixLift 2771221
  have htrace : WordTrace (prefixWord ++ tailWord_2771221) baseStart_2771221 baseEnd_2771221 := by
    simpa [prefixWord, tailWord_2771221, baseEnd_2771221] using wordTrace_append hprefix tailTrace_2771221
  have hstable : (prefixWord ++ tailWord_2771221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771221).length < 2 ^ (prefixWord ++ tailWord_2771221).sum := by decide
  have hdescent : baseEnd_2771221 < baseStart_2771221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771279 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_2771279 : Nat := 118140960795 + 2771279 * 2 ^ 59
def prefixEnd_2771279 : Nat := 4983230072969 + 3 ^ 40 * 2771279 * 2
def baseEnd_2771279 : Nat := 948665436474245394578417

theorem tailTrace_2771279 : CollatzResearch.WordTrace tailWord_2771279 prefixEnd_2771279 948665436474245394578417 := by
  unfold tailWord_2771279
  simp only [CollatzResearch.WordTrace]
  refine ⟨101076848927136954617228891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67384565951424636411485927 101076848927136954617228891)
  ·
    refine ⟨151615273390705431925843337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101076848927136954617228891 151615273390705431925843337)
    ·
      refine ⟨113711455043029073944382503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151615273390705431925843337 113711455043029073944382503)
      ·
        refine ⟨170567182564543610916573755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113711455043029073944382503 170567182564543610916573755)
        ·
          refine ⟨255850773846815416374860633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170567182564543610916573755 255850773846815416374860633)
          ·
            refine ⟨191888080385111562281145475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255850773846815416374860633 191888080385111562281145475)
            ·
              refine ⟨287832120577667343421718213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191888080385111562281145475 287832120577667343421718213)
              ·
                refine ⟨53968522608312626891572165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287832120577667343421718213 53968522608312626891572165)
                ·
                  refine ⟨10119097989058617542169781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53968522608312626891572165 10119097989058617542169781)
                  ·
                    refine ⟨948665436474245394578417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10119097989058617542169781 948665436474245394578417)
                    ·
                      rfl

theorem cell22_2771279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_2771279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771279 prefixEnd_2771279 := by exact prefixLift 2771279
  have htrace : WordTrace (prefixWord ++ tailWord_2771279) baseStart_2771279 baseEnd_2771279 := by
    simpa [prefixWord, tailWord_2771279, baseEnd_2771279] using wordTrace_append hprefix tailTrace_2771279
  have hstable : (prefixWord ++ tailWord_2771279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771279).length < 2 ^ (prefixWord ++ tailWord_2771279).sum := by decide
  have hdescent : baseEnd_2771279 < baseStart_2771279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771360 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_2771360 : Nat := 118140960795 + 2771360 * 2 ^ 59
def prefixEnd_2771360 : Nat := 4983230072969 + 3 ^ 40 * 2771360 * 2
def baseEnd_2771360 : Nat := 316231054809862727767723

theorem tailTrace_2771360 : CollatzResearch.WordTrace tailWord_2771360 prefixEnd_2771360 316231054809862727767723 := by
  unfold tailWord_2771360
  simp only [CollatzResearch.WordTrace]
  refine ⟨50539901619921752725463767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67386535493229003633951689 50539901619921752725463767)
  ·
    refine ⟨75809852429882629088195651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50539901619921752725463767 75809852429882629088195651)
    ·
      refine ⟨113714778644823943632293477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75809852429882629088195651 113714778644823943632293477)
      ·
        refine ⟨21321520995904489431055027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113714778644823943632293477 21321520995904489431055027)
        ·
          refine ⟨31982281493856734146582541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21321520995904489431055027 31982281493856734146582541)
          ·
            refine ⟨11993355560196275304968453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31982281493856734146582541 11993355560196275304968453)
            ·
              refine ⟨2248754167536801619681585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11993355560196275304968453 2248754167536801619681585)
              ·
                refine ⟨1686565625652601214761189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2248754167536801619681585 1686565625652601214761189)
                ·
                  refine ⟨316231054809862727767723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686565625652601214761189 316231054809862727767723)
                  ·
                    rfl

theorem cell22_2771360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_2771360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771360 prefixEnd_2771360 := by exact prefixLift 2771360
  have htrace : WordTrace (prefixWord ++ tailWord_2771360) baseStart_2771360 baseEnd_2771360 := by
    simpa [prefixWord, tailWord_2771360, baseEnd_2771360] using wordTrace_append hprefix tailTrace_2771360
  have hstable : (prefixWord ++ tailWord_2771360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771360).length < 2 ^ (prefixWord ++ tailWord_2771360).sum := by decide
  have hdescent : baseEnd_2771360 < baseStart_2771360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771426 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2771426 : Nat := 118140960795 + 2771426 * 2 ^ 59
def prefixEnd_2771426 : Nat := 4983230072969 + 3 ^ 40 * 2771426 * 2
def baseEnd_2771426 : Nat := 948715757578386011152967

theorem tailTrace_2771426 : CollatzResearch.WordTrace tailWord_2771426 prefixEnd_2771426 948715757578386011152967 := by
  unfold tailWord_2771426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25270552614401099680707533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67388140305069599148553421 25270552614401099680707533)
  ·
    refine ⟨9476457230400412380265325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25270552614401099680707533 9476457230400412380265325)
    ·
      refine ⟨3553671461400154642599497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9476457230400412380265325 3553671461400154642599497)
      ·
        refine ⟨2665253596050115981949623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553671461400154642599497 2665253596050115981949623)
        ·
          refine ⟨3997880394075173972924435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665253596050115981949623 3997880394075173972924435)
          ·
            refine ⟨5996820591112760959386653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997880394075173972924435 5996820591112760959386653)
            ·
              refine ⟨2248807721667285359769995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5996820591112760959386653 2248807721667285359769995)
              ·
                refine ⟨3373211582500928039654993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248807721667285359769995 3373211582500928039654993)
                ·
                  refine ⟨2529908686875696029741245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3373211582500928039654993 2529908686875696029741245)
                  ·
                    refine ⟨948715757578386011152967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2529908686875696029741245 948715757578386011152967)
                    ·
                      rfl

theorem cell22_2771426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2771426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771426 prefixEnd_2771426 := by exact prefixLift 2771426
  have htrace : WordTrace (prefixWord ++ tailWord_2771426) baseStart_2771426 baseEnd_2771426 := by
    simpa [prefixWord, tailWord_2771426, baseEnd_2771426] using wordTrace_append hprefix tailTrace_2771426
  have hstable : (prefixWord ++ tailWord_2771426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771426).length < 2 ^ (prefixWord ++ tailWord_2771426).sum := by decide
  have hdescent : baseEnd_2771426 < baseStart_2771426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771461 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 8]
def baseStart_2771461 : Nat := 118140960795 + 2771461 * 2 ^ 59
def prefixEnd_2771461 : Nat := 4983230072969 + 3 ^ 40 * 2771461 * 2
def baseEnd_2771461 : Nat := 316242579597885862175953

theorem tailTrace_2771461 : CollatzResearch.WordTrace tailWord_2771461 prefixEnd_2771461 316242579597885862175953 := by
  unfold tailWord_2771461
  simp only [CollatzResearch.WordTrace]
  refine ⟨101083487012477599700354237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67388991341651733133569491 101083487012477599700354237)
  ·
    refine ⟨37906307629679099887632839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101083487012477599700354237 37906307629679099887632839)
    ·
      refine ⟨56859461444518649831449259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37906307629679099887632839 56859461444518649831449259)
      ·
        refine ⟨85289192166777974747173889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56859461444518649831449259 85289192166777974747173889)
        ·
          refine ⟨63966894125083481060380417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85289192166777974747173889 63966894125083481060380417)
          ·
            refine ⟨47975170593812610795285313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63966894125083481060380417 47975170593812610795285313)
            ·
              refine ⟨35981377945359458096463985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47975170593812610795285313 35981377945359458096463985)
              ·
                refine ⟨26986033459019593572347989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35981377945359458096463985 26986033459019593572347989)
                ·
                  refine ⟨316242579597885862175953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26986033459019593572347989 316242579597885862175953)
                  ·
                    rfl

theorem cell22_2771461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_2771461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771461 prefixEnd_2771461 := by exact prefixLift 2771461
  have htrace : WordTrace (prefixWord ++ tailWord_2771461) baseStart_2771461 baseEnd_2771461 := by
    simpa [prefixWord, tailWord_2771461, baseEnd_2771461] using wordTrace_append hprefix tailTrace_2771461
  have hstable : (prefixWord ++ tailWord_2771461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771461).length < 2 ^ (prefixWord ++ tailWord_2771461).sum := by decide
  have hdescent : baseEnd_2771461 < baseStart_2771461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771510 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_2771510 : Nat := 118140960795 + 2771510 * 2 ^ 59
def prefixEnd_2771510 : Nat := 4983230072969 + 3 ^ 40 * 2771510 * 2
def baseEnd_2771510 : Nat := 948744512495037792052709

theorem tailTrace_2771510 : CollatzResearch.WordTrace tailWord_2771510 prefixEnd_2771510 948744512495037792052709 := by
  unfold tailWord_2771510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317829636831255066805499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67390182792866720712591989 6317829636831255066805499)
  ·
    refine ⟨9476744455246882600208249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317829636831255066805499 9476744455246882600208249)
    ·
      refine ⟨7107558341435161950156187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9476744455246882600208249 7107558341435161950156187)
      ·
        refine ⟨10661337512152742925234281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7107558341435161950156187 10661337512152742925234281)
        ·
          refine ⟨7996003134114557193925711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10661337512152742925234281 7996003134114557193925711)
          ·
            refine ⟨11994004701171835790888567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996003134114557193925711 11994004701171835790888567)
            ·
              refine ⟨17991007051757753686332851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11994004701171835790888567 17991007051757753686332851)
              ·
                refine ⟨26986510577636630529499277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17991007051757753686332851 26986510577636630529499277)
                ·
                  refine ⟨10119941466613736448562229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26986510577636630529499277 10119941466613736448562229)
                  ·
                    refine ⟨948744512495037792052709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10119941466613736448562229 948744512495037792052709)
                    ·
                      rfl

theorem cell22_2771510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_2771510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771510 prefixEnd_2771510 := by exact prefixLift 2771510
  have htrace : WordTrace (prefixWord ++ tailWord_2771510) baseStart_2771510 baseEnd_2771510 := by
    simpa [prefixWord, tailWord_2771510, baseEnd_2771510] using wordTrace_append hprefix tailTrace_2771510
  have hstable : (prefixWord ++ tailWord_2771510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771510).length < 2 ^ (prefixWord ++ tailWord_2771510).sum := by decide
  have hdescent : baseEnd_2771510 < baseStart_2771510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771527 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 2, 3]
def baseStart_2771527 : Nat := 118140960795 + 2771527 * 2 ^ 59
def prefixEnd_2771527 : Nat := 4983230072969 + 3 ^ 40 * 2771527 * 2
def baseEnd_2771527 : Nat := 948750331942455414377657

theorem tailTrace_2771527 : CollatzResearch.WordTrace tailWord_2771527 prefixEnd_2771527 948750331942455414377657 := by
  unfold tailWord_2771527
  simp only [CollatzResearch.WordTrace]
  refine ⟨101085894230238492972256835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67390596153492328648171223 101085894230238492972256835)
  ·
    refine ⟨151628841345357739458385253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101085894230238492972256835 151628841345357739458385253)
    ·
      refine ⟨28430407752254576148447235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151628841345357739458385253 28430407752254576148447235)
      ·
        refine ⟨42645611628381864222670853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28430407752254576148447235 42645611628381864222670853)
        ·
          refine ⟨7996052180321599541750785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42645611628381864222670853 7996052180321599541750785)
          ·
            refine ⟨5997039135241199656313089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7996052180321599541750785 5997039135241199656313089)
            ·
              refine ⟨4497779351430899742234817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5997039135241199656313089 4497779351430899742234817)
              ·
                refine ⟨3373334513573174806676113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4497779351430899742234817 3373334513573174806676113)
                ·
                  refine ⟨2530000885179881105007085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3373334513573174806676113 2530000885179881105007085)
                  ·
                    refine ⟨948750331942455414377657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530000885179881105007085 948750331942455414377657)
                    ·
                      rfl

theorem cell22_2771527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_2771527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771527 prefixEnd_2771527 := by exact prefixLift 2771527
  have htrace : WordTrace (prefixWord ++ tailWord_2771527) baseStart_2771527 baseEnd_2771527 := by
    simpa [prefixWord, tailWord_2771527, baseEnd_2771527] using wordTrace_append hprefix tailTrace_2771527
  have hstable : (prefixWord ++ tailWord_2771527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771527).length < 2 ^ (prefixWord ++ tailWord_2771527).sum := by decide
  have hdescent : baseEnd_2771527 < baseStart_2771527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771540 : List Nat := [2, 4, 1, 1, 1, 5, 1, 7]
def baseStart_2771540 : Nat := 118140960795 + 2771540 * 2 ^ 59
def prefixEnd_2771540 : Nat := 4983230072969 + 3 ^ 40 * 2771540 * 2
def baseEnd_2771540 : Nat := 105417198012014190422513

theorem tailTrace_2771540 : CollatzResearch.WordTrace tailWord_2771540 prefixEnd_2771540 105417198012014190422513 := by
  unfold tailWord_2771540
  simp only [CollatzResearch.WordTrace]
  refine ⟨50543184189595698096240037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67390912252794264128320049 50543184189595698096240037)
  ·
    refine ⟨9476847035549193393045007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50543184189595698096240037 9476847035549193393045007)
    ·
      refine ⟨14215270553323790089567511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9476847035549193393045007 14215270553323790089567511)
      ·
        refine ⟨21322905829985685134351267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14215270553323790089567511 21322905829985685134351267)
        ·
          refine ⟨31984358744978527701526901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21322905829985685134351267 31984358744978527701526901)
          ·
            refine ⟨2998533632341736972018147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31984358744978527701526901 2998533632341736972018147)
            ·
              refine ⟨4497800448512605458027221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998533632341736972018147 4497800448512605458027221)
              ·
                refine ⟨105417198012014190422513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4497800448512605458027221 105417198012014190422513)
                ·
                  rfl

theorem cell22_2771540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_2771540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771540 prefixEnd_2771540 := by exact prefixLift 2771540
  have htrace : WordTrace (prefixWord ++ tailWord_2771540) baseStart_2771540 baseEnd_2771540 := by
    simpa [prefixWord, tailWord_2771540, baseEnd_2771540] using wordTrace_append hprefix tailTrace_2771540
  have hstable : (prefixWord ++ tailWord_2771540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771540).length < 2 ^ (prefixWord ++ tailWord_2771540).sum := by decide
  have hdescent : baseEnd_2771540 < baseStart_2771540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771555 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 3, 3]
def baseStart_2771555 : Nat := 118140960795 + 2771555 * 2 ^ 59
def prefixEnd_2771555 : Nat := 4983230072969 + 3 ^ 40 * 2771555 * 2
def baseEnd_2771555 : Nat := 948759916914672674677571

theorem tailTrace_2771555 : CollatzResearch.WordTrace tailWord_2771555 prefixEnd_2771555 948759916914672674677571 := by
  unfold tailWord_2771555
  simp only [CollatzResearch.WordTrace]
  refine ⟨101086915474137053754276119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67391276982758035836184079 101086915474137053754276119)
  ·
    refine ⟨151630373211205580631414179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101086915474137053754276119 151630373211205580631414179)
    ·
      refine ⟨227445559816808370947121269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151630373211205580631414179 227445559816808370947121269)
      ·
        refine ⟨21323021232825784776292619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 227445559816808370947121269 21323021232825784776292619)
        ·
          refine ⟨31984531849238677164438929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21323021232825784776292619 31984531849238677164438929)
          ·
            refine ⟨23988398886929007873329197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31984531849238677164438929 23988398886929007873329197)
            ·
              refine ⟨8995649582598377952498449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23988398886929007873329197 8995649582598377952498449)
              ·
                refine ⟨6746737186948783464373837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8995649582598377952498449 6746737186948783464373837)
                ·
                  refine ⟨2530026445105793799140189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6746737186948783464373837 2530026445105793799140189)
                  ·
                    refine ⟨948759916914672674677571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530026445105793799140189 948759916914672674677571)
                    ·
                      rfl

theorem cell22_2771555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 3, 3].length) (baseStart_2771555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771555 prefixEnd_2771555 := by exact prefixLift 2771555
  have htrace : WordTrace (prefixWord ++ tailWord_2771555) baseStart_2771555 baseEnd_2771555 := by
    simpa [prefixWord, tailWord_2771555, baseEnd_2771555] using wordTrace_append hprefix tailTrace_2771555
  have hstable : (prefixWord ++ tailWord_2771555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771555).length < 2 ^ (prefixWord ++ tailWord_2771555).sum := by decide
  have hdescent : baseEnd_2771555 < baseStart_2771555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771623 : List Nat := [1, 1, 6, 3, 1, 2, 1, 3, 1, 3]
def baseStart_2771623 : Nat := 118140960795 + 2771623 * 2 ^ 59
def prefixEnd_2771623 : Nat := 4983230072969 + 3 ^ 40 * 2771623 * 2
def baseEnd_2771623 : Nat := 948783194704343163977363

theorem tailTrace_2771623 : CollatzResearch.WordTrace tailWord_2771623 prefixEnd_2771623 948783194704343163977363 := by
  unfold tailWord_2771623
  simp only [CollatzResearch.WordTrace]
  refine ⟨101089395637890701367751523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67392930425260467578501015 101089395637890701367751523)
  ·
    refine ⟨151634093456836052051627285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101089395637890701367751523 151634093456836052051627285)
    ·
      refine ⟨7107848130789189939920029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151634093456836052051627285 7107848130789189939920029)
      ·
        refine ⟨2665443049045946227470011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7107848130789189939920029 2665443049045946227470011)
        ·
          refine ⟨3998164573568919341205017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665443049045946227470011 3998164573568919341205017)
          ·
            refine ⟨2998623430176689505903763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3998164573568919341205017 2998623430176689505903763)
            ·
              refine ⟨4497935145265034258855645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998623430176689505903763 4497935145265034258855645)
              ·
                refine ⟨1686725679474387847070867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4497935145265034258855645 1686725679474387847070867)
                ·
                  refine ⟨2530088519211581770606301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686725679474387847070867 2530088519211581770606301)
                  ·
                    refine ⟨948783194704343163977363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530088519211581770606301 948783194704343163977363)
                    ·
                      rfl

theorem cell22_2771623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_2771623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771623 prefixEnd_2771623 := by exact prefixLift 2771623
  have htrace : WordTrace (prefixWord ++ tailWord_2771623) baseStart_2771623 baseEnd_2771623 := by
    simpa [prefixWord, tailWord_2771623, baseEnd_2771623] using wordTrace_append hprefix tailTrace_2771623
  have hstable : (prefixWord ++ tailWord_2771623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771623).length < 2 ^ (prefixWord ++ tailWord_2771623).sum := by decide
  have hdescent : baseEnd_2771623 < baseStart_2771623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771666 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_2771666 : Nat := 118140960795 + 2771666 * 2 ^ 59
def prefixEnd_2771666 : Nat := 4983230072969 + 3 ^ 40 * 2771666 * 2
def baseEnd_2771666 : Nat := 948797914483105385152231

theorem tailTrace_2771666 : CollatzResearch.WordTrace tailWord_2771666 prefixEnd_2771666 948797914483105385152231 := by
  unfold tailWord_2771666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25272740994183729927891713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67393975984489946474377901 25272740994183729927891713)
  ·
    refine ⟨18954555745637797445918785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25272740994183729927891713 18954555745637797445918785)
    ·
      refine ⟨14215916809228348084439089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18954555745637797445918785 14215916809228348084439089)
      ·
        refine ⟨10661937606921261063329317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14215916809228348084439089 10661937606921261063329317)
        ·
          refine ⟨1999113301297736449374247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10661937606921261063329317 1999113301297736449374247)
          ·
            refine ⟨2998669951946604674061371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999113301297736449374247 2998669951946604674061371)
            ·
              refine ⟨4498004927919907011092057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998669951946604674061371 4498004927919907011092057)
              ·
                refine ⟨3373503695939930258319043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4498004927919907011092057 3373503695939930258319043)
                ·
                  refine ⟨5060255543909895387478565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373503695939930258319043 5060255543909895387478565)
                  ·
                    refine ⟨948797914483105385152231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060255543909895387478565 948797914483105385152231)
                    ·
                      rfl

theorem cell22_2771666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_2771666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771666 prefixEnd_2771666 := by exact prefixLift 2771666
  have htrace : WordTrace (prefixWord ++ tailWord_2771666) baseStart_2771666 baseEnd_2771666 := by
    simpa [prefixWord, tailWord_2771666, baseEnd_2771666] using wordTrace_append hprefix tailTrace_2771666
  have hstable : (prefixWord ++ tailWord_2771666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771666).length < 2 ^ (prefixWord ++ tailWord_2771666).sum := by decide
  have hdescent : baseEnd_2771666 < baseStart_2771666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771754 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_2771754 : Nat := 118140960795 + 2771754 * 2 ^ 59
def prefixEnd_2771754 : Nat := 4983230072969 + 3 ^ 40 * 2771754 * 2
def baseEnd_2771754 : Nat := 316276012893834162983987

theorem tailTrace_2771754 : CollatzResearch.WordTrace tailWord_2771754 prefixEnd_2771754 316276012893834162983987 := by
  unfold tailWord_2771754
  simp only [CollatzResearch.WordTrace]
  refine ⟨25273543400104027685192579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67396115733610740493846877 25273543400104027685192579)
  ·
    refine ⟨37910315100156041527788869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25273543400104027685192579 37910315100156041527788869)
    ·
      refine ⟨7108184081279257786460413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37910315100156041527788869 7108184081279257786460413)
      ·
        refine ⟨2665569030479721669922655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7108184081279257786460413 2665569030479721669922655)
        ·
          refine ⟨3998353545719582504883983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2665569030479721669922655 3998353545719582504883983)
          ·
            refine ⟨5997530318579373757325975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3998353545719582504883983 5997530318579373757325975)
            ·
              refine ⟨8996295477869060635988963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997530318579373757325975 8996295477869060635988963)
              ·
                refine ⟨13494443216803590953983445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8996295477869060635988963 13494443216803590953983445)
                ·
                  refine ⟨316276012893834162983987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13494443216803590953983445 316276012893834162983987)
                  ·
                    rfl

theorem cell22_2771754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_2771754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771754 prefixEnd_2771754 := by exact prefixLift 2771754
  have htrace : WordTrace (prefixWord ++ tailWord_2771754) baseStart_2771754 baseEnd_2771754 := by
    simpa [prefixWord, tailWord_2771754, baseEnd_2771754] using wordTrace_append hprefix tailTrace_2771754
  have hstable : (prefixWord ++ tailWord_2771754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771754).length < 2 ^ (prefixWord ++ tailWord_2771754).sum := by decide
  have hdescent : baseEnd_2771754 < baseStart_2771754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_2771795 : Nat := 118140960795 + 2771795 * 2 ^ 59
def prefixEnd_2771795 : Nat := 4983230072969 + 3 ^ 40 * 2771795 * 2
def baseEnd_2771795 : Nat := 948842073819392048676835

theorem tailTrace_2771795 : CollatzResearch.WordTrace tailWord_2771795 prefixEnd_2771795 948842073819392048676835 := by
  unfold tailWord_2771795
  simp only [CollatzResearch.WordTrace]
  refine ⟨101095668993267574743012839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67397112662178383162008559 101095668993267574743012839)
  ·
    refine ⟨151643503489901362114519259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101095668993267574743012839 151643503489901362114519259)
    ·
      refine ⟨227465255234852043171778889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151643503489901362114519259 227465255234852043171778889)
      ·
        refine ⟨170598941426139032378834167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227465255234852043171778889 170598941426139032378834167)
        ·
          refine ⟨255898412139208548568251251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170598941426139032378834167 255898412139208548568251251)
          ·
            refine ⟨383847618208812822852376877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255898412139208548568251251 383847618208812822852376877)
            ·
              refine ⟨143942856828304808569641329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383847618208812822852376877 143942856828304808569641329)
              ·
                refine ⟨107957142621228606427230997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143942856828304808569641329 107957142621228606427230997)
                ·
                  refine ⟨5060491060370090926276453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107957142621228606427230997 5060491060370090926276453)
                  ·
                    refine ⟨948842073819392048676835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060491060370090926276453 948842073819392048676835)
                    ·
                      rfl

theorem cell22_2771795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_2771795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771795 prefixEnd_2771795 := by exact prefixLift 2771795
  have htrace : WordTrace (prefixWord ++ tailWord_2771795) baseStart_2771795 baseEnd_2771795 := by
    simpa [prefixWord, tailWord_2771795, baseEnd_2771795] using wordTrace_append hprefix tailTrace_2771795
  have hstable : (prefixWord ++ tailWord_2771795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771795).length < 2 ^ (prefixWord ++ tailWord_2771795).sum := by decide
  have hdescent : baseEnd_2771795 < baseStart_2771795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771797 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2771797 : Nat := 118140960795 + 2771797 * 2 ^ 59
def prefixEnd_2771797 : Nat := 4983230072969 + 3 ^ 40 * 2771797 * 2
def baseEnd_2771797 : Nat := 948842758460264710126829

theorem tailTrace_2771797 : CollatzResearch.WordTrace tailWord_2771797 prefixEnd_2771797 948842758460264710126829 := by
  unfold tailWord_2771797
  simp only [CollatzResearch.WordTrace]
  refine ⟨101095741939260329084585645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67397161292840219389723763 101095741939260329084585645)
  ·
    refine ⟨37910903227222623406719617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101095741939260329084585645 37910903227222623406719617)
    ·
      refine ⟨28433177420416967555039713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37910903227222623406719617 28433177420416967555039713)
      ·
        refine ⟨21324883065312725666279785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28433177420416967555039713 21324883065312725666279785)
        ·
          refine ⟨15993662298984544249709839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21324883065312725666279785 15993662298984544249709839)
          ·
            refine ⟨23990493448476816374564759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15993662298984544249709839 23990493448476816374564759)
            ·
              refine ⟨35985740172715224561847139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23990493448476816374564759 35985740172715224561847139)
              ·
                refine ⟨53978610259072836842770709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35985740172715224561847139 53978610259072836842770709)
                ·
                  refine ⟨2530247355894039227004877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 53978610259072836842770709 2530247355894039227004877)
                  ·
                    refine ⟨948842758460264710126829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530247355894039227004877 948842758460264710126829)
                    ·
                      rfl

theorem cell22_2771797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2771797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771797 prefixEnd_2771797 := by exact prefixLift 2771797
  have htrace : WordTrace (prefixWord ++ tailWord_2771797) baseStart_2771797 baseEnd_2771797 := by
    simpa [prefixWord, tailWord_2771797, baseEnd_2771797] using wordTrace_append hprefix tailTrace_2771797
  have hstable : (prefixWord ++ tailWord_2771797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771797).length < 2 ^ (prefixWord ++ tailWord_2771797).sum := by decide
  have hdescent : baseEnd_2771797 < baseStart_2771797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771799 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 4]
def baseStart_2771799 : Nat := 118140960795 + 2771799 * 2 ^ 59
def prefixEnd_2771799 : Nat := 4983230072969 + 3 ^ 40 * 2771799 * 2
def baseEnd_2771799 : Nat := 316281147700379123858941

theorem tailTrace_2771799 : CollatzResearch.WordTrace tailWord_2771799 prefixEnd_2771799 316281147700379123858941 := by
  unfold tailWord_2771799
  simp only [CollatzResearch.WordTrace]
  refine ⟨101095814885253083426158451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67397209923502055617438967 101095814885253083426158451)
  ·
    refine ⟨151643722327879625139237677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101095814885253083426158451 151643722327879625139237677)
    ·
      refine ⟨56866395872954859427214129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151643722327879625139237677 56866395872954859427214129)
      ·
        refine ⟨42649796904716144570410597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56866395872954859427214129 42649796904716144570410597)
        ·
          refine ⟨7996836919634277106951987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42649796904716144570410597 7996836919634277106951987)
          ·
            refine ⟨11995255379451415660427981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996836919634277106951987 11995255379451415660427981)
            ·
              refine ⟨4498220767294280872660493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11995255379451415660427981 4498220767294280872660493)
              ·
                refine ⟨1686832787735355327247685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4498220767294280872660493 1686832787735355327247685)
                ·
                  refine ⟨316281147700379123858941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686832787735355327247685 316281147700379123858941)
                  ·
                    rfl

theorem cell22_2771799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 4].length) (baseStart_2771799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771799 prefixEnd_2771799 := by exact prefixLift 2771799
  have htrace : WordTrace (prefixWord ++ tailWord_2771799) baseStart_2771799 baseEnd_2771799 := by
    simpa [prefixWord, tailWord_2771799, baseEnd_2771799] using wordTrace_append hprefix tailTrace_2771799
  have hstable : (prefixWord ++ tailWord_2771799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771799).length < 2 ^ (prefixWord ++ tailWord_2771799).sum := by decide
  have hdescent : baseEnd_2771799 < baseStart_2771799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771812 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2771812 : Nat := 118140960795 + 2771812 * 2 ^ 59
def prefixEnd_2771812 : Nat := 4983230072969 + 3 ^ 40 * 2771812 * 2
def baseEnd_2771812 : Nat := 948847893266809671001783

theorem tailTrace_2771812 : CollatzResearch.WordTrace tailWord_2771812 prefixEnd_2771812 948847893266809671001783 := by
  unfold tailWord_2771812
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548144517102993323190845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67397526022803991097587793 50548144517102993323190845)
  ·
    refine ⟨18955554193913622496196567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50548144517102993323190845 18955554193913622496196567)
    ·
      refine ⟨28433331290870433744294851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18955554193913622496196567 28433331290870433744294851)
      ·
        refine ⟨42649996936305650616442277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28433331290870433744294851 42649996936305650616442277)
        ·
          refine ⟨7996874425557309490582927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42649996936305650616442277 7996874425557309490582927)
          ·
            refine ⟨11995311638335964235874391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7996874425557309490582927 11995311638335964235874391)
            ·
              refine ⟨17992967457503946353811587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11995311638335964235874391 17992967457503946353811587)
              ·
                refine ⟨26989451186255919530717381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17992967457503946353811587 26989451186255919530717381)
                ·
                  refine ⟨5060522097422984912009509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26989451186255919530717381 5060522097422984912009509)
                  ·
                    refine ⟨948847893266809671001783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060522097422984912009509 948847893266809671001783)
                    ·
                      rfl

theorem cell22_2771812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2771812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771812 prefixEnd_2771812 := by exact prefixLift 2771812
  have htrace : WordTrace (prefixWord ++ tailWord_2771812) baseStart_2771812 baseEnd_2771812 := by
    simpa [prefixWord, tailWord_2771812, baseEnd_2771812] using wordTrace_append hprefix tailTrace_2771812
  have hstable : (prefixWord ++ tailWord_2771812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771812).length < 2 ^ (prefixWord ++ tailWord_2771812).sum := by decide
  have hdescent : baseEnd_2771812 < baseStart_2771812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771816 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_2771816 : Nat := 118140960795 + 2771816 * 2 ^ 59
def prefixEnd_2771816 : Nat := 4983230072969 + 3 ^ 40 * 2771816 * 2
def baseEnd_2771816 : Nat := 316283087516184997967257

theorem tailTrace_2771816 : CollatzResearch.WordTrace tailWord_2771816 prefixEnd_2771816 316283087516184997967257 := by
  unfold tailWord_2771816
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548217463095747664763651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67397623284127663553018201 50548217463095747664763651)
  ·
    refine ⟨75822326194643621497145477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50548217463095747664763651 75822326194643621497145477)
    ·
      refine ⟨14216686161495679030714777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75822326194643621497145477 14216686161495679030714777)
      ·
        refine ⟨10662514621121759273036083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14216686161495679030714777 10662514621121759273036083)
        ·
          refine ⟨15993771931682638909554125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10662514621121759273036083 15993771931682638909554125)
          ·
            refine ⟨5997664474380989591082797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15993771931682638909554125 5997664474380989591082797)
            ·
              refine ⟨2249124177892871096656049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5997664474380989591082797 2249124177892871096656049)
              ·
                refine ⟨1686843133419653322492037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249124177892871096656049 1686843133419653322492037)
                ·
                  refine ⟨316283087516184997967257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1686843133419653322492037 316283087516184997967257)
                  ·
                    rfl

theorem cell22_2771816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_2771816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771816 prefixEnd_2771816 := by exact prefixLift 2771816
  have htrace : WordTrace (prefixWord ++ tailWord_2771816) baseStart_2771816 baseEnd_2771816 := by
    simpa [prefixWord, tailWord_2771816, baseEnd_2771816] using wordTrace_append hprefix tailTrace_2771816
  have hstable : (prefixWord ++ tailWord_2771816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771816).length < 2 ^ (prefixWord ++ tailWord_2771816).sum := by decide
  have hdescent : baseEnd_2771816 < baseStart_2771816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771840 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_2771840 : Nat := 118140960795 + 2771840 * 2 ^ 59
def prefixEnd_2771840 : Nat := 4983230072969 + 3 ^ 40 * 2771840 * 2
def baseEnd_2771840 : Nat := 948857478239026931301697

theorem tailTrace_2771840 : CollatzResearch.WordTrace tailWord_2771840 prefixEnd_2771840 948857478239026931301697 := by
  unfold tailWord_2771840
  simp only [CollatzResearch.WordTrace]
  refine ⟨50548655139052273714200487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67398206852069698285600649 50548655139052273714200487)
  ·
    refine ⟨75822982708578410571300731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50548655139052273714200487 75822982708578410571300731)
    ·
      refine ⟨113734474062867615856951097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75822982708578410571300731 113734474062867615856951097)
      ·
        refine ⟨85300855547150711892713323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113734474062867615856951097 85300855547150711892713323)
        ·
          refine ⟨127951283320726067839069985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85300855547150711892713323 127951283320726067839069985)
          ·
            refine ⟨95963462490544550879302489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127951283320726067839069985 95963462490544550879302489)
            ·
              refine ⟨71972596867908413159476867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95963462490544550879302489 71972596867908413159476867)
              ·
                refine ⟨107958895301862619739215301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71972596867908413159476867 107958895301862619739215301)
                ·
                  refine ⟨20242292869099241201102869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107958895301862619739215301 20242292869099241201102869)
                  ·
                    refine ⟨948857478239026931301697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20242292869099241201102869 948857478239026931301697)
                    ·
                      rfl

theorem cell22_2771840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_2771840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771840 prefixEnd_2771840 := by exact prefixLift 2771840
  have htrace : WordTrace (prefixWord ++ tailWord_2771840) baseStart_2771840 baseEnd_2771840 := by
    simpa [prefixWord, tailWord_2771840, baseEnd_2771840] using wordTrace_append hprefix tailTrace_2771840
  have hstable : (prefixWord ++ tailWord_2771840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771840).length < 2 ^ (prefixWord ++ tailWord_2771840).sum := by decide
  have hdescent : baseEnd_2771840 < baseStart_2771840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771872 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_2771872 : Nat := 118140960795 + 2771872 * 2 ^ 59
def prefixEnd_2771872 : Nat := 4983230072969 + 3 ^ 40 * 2771872 * 2
def baseEnd_2771872 : Nat := 316289477497663171500533

theorem tailTrace_2771872 : CollatzResearch.WordTrace tailWord_2771872 prefixEnd_2771872 316289477497663171500533 := by
  unfold tailWord_2771872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50549238706994308446782935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67398984942659077929043913 50549238706994308446782935)
  ·
    refine ⟨75823858060491462670174403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50549238706994308446782935 75823858060491462670174403)
    ·
      refine ⟨113735787090737194005261605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75823858060491462670174403 113735787090737194005261605)
      ·
        refine ⟨21325460079513223875986551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113735787090737194005261605 21325460079513223875986551)
        ·
          refine ⟨31988190119269835813979827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21325460079513223875986551 31988190119269835813979827)
          ·
            refine ⟨47982285178904753720969741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31988190119269835813979827 47982285178904753720969741)
            ·
              refine ⟨17993356942089282645363653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47982285178904753720969741 17993356942089282645363653)
              ·
                refine ⟨3373754426641740496005685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17993356942089282645363653 3373754426641740496005685)
                ·
                  refine ⟨316289477497663171500533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373754426641740496005685 316289477497663171500533)
                  ·
                    rfl

theorem cell22_2771872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_2771872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771872 prefixEnd_2771872 := by exact prefixLift 2771872
  have htrace : WordTrace (prefixWord ++ tailWord_2771872) baseStart_2771872 baseEnd_2771872 := by
    simpa [prefixWord, tailWord_2771872, baseEnd_2771872] using wordTrace_append hprefix tailTrace_2771872
  have hstable : (prefixWord ++ tailWord_2771872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771872).length < 2 ^ (prefixWord ++ tailWord_2771872).sum := by decide
  have hdescent : baseEnd_2771872 < baseStart_2771872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771876 : List Nat := [2, 3, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_2771876 : Nat := 118140960795 + 2771876 * 2 ^ 59
def prefixEnd_2771876 : Nat := 4983230072969 + 3 ^ 40 * 2771876 * 2
def baseEnd_2771876 : Nat := 948869801774734837401587

theorem tailTrace_2771876 : CollatzResearch.WordTrace tailWord_2771876 prefixEnd_2771876 948869801774734837401587 := by
  unfold tailWord_2771876
  simp only [CollatzResearch.WordTrace]
  refine ⟨50549311652987062788355741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67399082203982750384474321 50549311652987062788355741)
  ·
    refine ⟨18955991869870148545633403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50549311652987062788355741 18955991869870148545633403)
    ·
      refine ⟨28433987804805222818450105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18955991869870148545633403 28433987804805222818450105)
      ·
        refine ⟨21325490853603917113837579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28433987804805222818450105 21325490853603917113837579)
        ·
          refine ⟨31988236280405875670756369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21325490853603917113837579 31988236280405875670756369)
          ·
            refine ⟨23991177210304406753067277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31988236280405875670756369 23991177210304406753067277)
            ·
              refine ⟨8996691453864152532400229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23991177210304406753067277 8996691453864152532400229)
              ·
                refine ⟨1686879647599528599825043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8996691453864152532400229 1686879647599528599825043)
                ·
                  refine ⟨2530319471399292899737565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686879647599528599825043 2530319471399292899737565)
                  ·
                    refine ⟨948869801774734837401587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530319471399292899737565 948869801774734837401587)
                    ·
                      rfl

theorem cell22_2771876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_2771876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771876 prefixEnd_2771876 := by exact prefixLift 2771876
  have htrace : WordTrace (prefixWord ++ tailWord_2771876) baseStart_2771876 baseEnd_2771876 := by
    simpa [prefixWord, tailWord_2771876, baseEnd_2771876] using wordTrace_append hprefix tailTrace_2771876
  have hstable : (prefixWord ++ tailWord_2771876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771876).length < 2 ^ (prefixWord ++ tailWord_2771876).sum := by decide
  have hdescent : baseEnd_2771876 < baseStart_2771876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2771919 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 1, 4]
def baseStart_2771919 : Nat := 118140960795 + 2771919 * 2 ^ 59
def prefixEnd_2771919 : Nat := 4983230072969 + 3 ^ 40 * 2771919 * 2
def baseEnd_2771919 : Nat := 948884521553497058576455

theorem tailTrace_2771919 : CollatzResearch.WordTrace tailWord_2771919 prefixEnd_2771919 948884521553497058576455 := by
  unfold tailWord_2771919
  simp only [CollatzResearch.WordTrace]
  refine ⟨101100191644818343920526811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67400127763212229280351207 101100191644818343920526811)
  ·
    refine ⟨151650287467227515880790217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101100191644818343920526811 151650287467227515880790217)
    ·
      refine ⟨113737715600420636910592663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151650287467227515880790217 113737715600420636910592663)
      ·
        refine ⟨170606573400630955365888995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113737715600420636910592663 170606573400630955365888995)
        ·
          refine ⟨255909860100946433048833493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170606573400630955365888995 255909860100946433048833493)
          ·
            refine ⟨5997887346115932024582035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 255909860100946433048833493 5997887346115932024582035)
            ·
              refine ⟨8996831019173898036873053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5997887346115932024582035 8996831019173898036873053)
              ·
                refine ⟨3373811632190211763827395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8996831019173898036873053 3373811632190211763827395)
                ·
                  refine ⟨5060717448285317645741093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3373811632190211763827395 5060717448285317645741093)
                  ·
                    refine ⟨948884521553497058576455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5060717448285317645741093 948884521553497058576455)
                    ·
                      rfl

theorem cell22_2771919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_2771919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2771919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2771919 prefixEnd_2771919 := by exact prefixLift 2771919
  have htrace : WordTrace (prefixWord ++ tailWord_2771919) baseStart_2771919 baseEnd_2771919 := by
    simpa [prefixWord, tailWord_2771919, baseEnd_2771919] using wordTrace_append hprefix tailTrace_2771919
  have hstable : (prefixWord ++ tailWord_2771919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2771919).length < 2 ^ (prefixWord ++ tailWord_2771919).sum := by decide
  have hdescent : baseEnd_2771919 < baseStart_2771919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2771919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772045 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_2772045 : Nat := 118140960795 + 2772045 * 2 ^ 59
def prefixEnd_2772045 : Nat := 4983230072969 + 3 ^ 40 * 2772045 * 2
def baseEnd_2772045 : Nat := 948927653928474729926069

theorem tailTrace_2772045 : CollatzResearch.WordTrace tailWord_2772045 prefixEnd_2772045 948927653928474729926069 := by
  unfold tailWord_2772045
  simp only [CollatzResearch.WordTrace]
  refine ⟨101104787242361867439613589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67403191494907911626409059 101104787242361867439613589)
  ·
    refine ⟨4739286901985712536231887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101104787242361867439613589 4739286901985712536231887)
    ·
      refine ⟨7108930352978568804347831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739286901985712536231887 7108930352978568804347831)
      ·
        refine ⟨10663395529467853206521747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7108930352978568804347831 10663395529467853206521747)
        ·
          refine ⟨15995093294201779809782621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10663395529467853206521747 15995093294201779809782621)
          ·
            refine ⟨5998159985325667428668483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15995093294201779809782621 5998159985325667428668483)
            ·
              refine ⟨8997239977988501143002725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998159985325667428668483 8997239977988501143002725)
              ·
                refine ⟨1686982495872843964313011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8997239977988501143002725 1686982495872843964313011)
                ·
                  refine ⟨2530473743809265946469517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1686982495872843964313011 2530473743809265946469517)
                  ·
                    refine ⟨948927653928474729926069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530473743809265946469517 948927653928474729926069)
                    ·
                      rfl

theorem cell22_2772045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_2772045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772045 prefixEnd_2772045 := by exact prefixLift 2772045
  have htrace : WordTrace (prefixWord ++ tailWord_2772045) baseStart_2772045 baseEnd_2772045 := by
    simpa [prefixWord, tailWord_2772045, baseEnd_2772045] using wordTrace_append hprefix tailTrace_2772045
  have hstable : (prefixWord ++ tailWord_2772045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772045).length < 2 ^ (prefixWord ++ tailWord_2772045).sum := by decide
  have hdescent : baseEnd_2772045 < baseStart_2772045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772069 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 6]
def baseStart_2772069 : Nat := 118140960795 + 2772069 * 2 ^ 59
def prefixEnd_2772069 : Nat := 4983230072969 + 3 ^ 40 * 2772069 * 2
def baseEnd_2772069 : Nat := 316311956539648889108665

theorem tailTrace_2772069 : CollatzResearch.WordTrace tailWord_2772069 prefixEnd_2772069 316311956539648889108665 := by
  unfold tailWord_2772069
  simp only [CollatzResearch.WordTrace]
  refine ⟨101105662594274919538487261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67403775062849946358991507 101105662594274919538487261)
  ·
    refine ⟨37914623472853094826932723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101105662594274919538487261 37914623472853094826932723)
    ·
      refine ⟨56871935209279642240399085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37914623472853094826932723 56871935209279642240399085)
      ·
        refine ⟨21326975703479865840149657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56871935209279642240399085 21326975703479865840149657)
        ·
          refine ⟨15995231777609899380112243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21326975703479865840149657 15995231777609899380112243)
          ·
            refine ⟨23992847666414849070168365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15995231777609899380112243 23992847666414849070168365)
            ·
              refine ⟨8997317874905568401313137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23992847666414849070168365 8997317874905568401313137)
              ·
                refine ⟨6747988406179176300984853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8997317874905568401313137 6747988406179176300984853)
                ·
                  refine ⟨316311956539648889108665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6747988406179176300984853 316311956539648889108665)
                  ·
                    rfl

theorem cell22_2772069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_2772069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772069 prefixEnd_2772069 := by exact prefixLift 2772069
  have htrace : WordTrace (prefixWord ++ tailWord_2772069) baseStart_2772069 baseEnd_2772069 := by
    simpa [prefixWord, tailWord_2772069, baseEnd_2772069] using wordTrace_append hprefix tailTrace_2772069
  have hstable : (prefixWord ++ tailWord_2772069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772069).length < 2 ^ (prefixWord ++ tailWord_2772069).sum := by decide
  have hdescent : baseEnd_2772069 < baseStart_2772069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772099 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_2772099 : Nat := 118140960795 + 2772099 * 2 ^ 59
def prefixEnd_2772099 : Nat := 4983230072969 + 3 ^ 40 * 2772099 * 2
def baseEnd_2772099 : Nat := 948946139232036589075903

theorem tailTrace_2772099 : CollatzResearch.WordTrace tailWord_2772099 prefixEnd_2772099 948946139232036589075903 := by
  unfold tailWord_2772099
  simp only [CollatzResearch.WordTrace]
  refine ⟨101106756784166234662079351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67404504522777489774719567 101106756784166234662079351)
  ·
    refine ⟨151660135176249351993119027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101106756784166234662079351 151660135176249351993119027)
    ·
      refine ⟨227490202764374027989678541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151660135176249351993119027 227490202764374027989678541)
      ·
        refine ⟨85308826036640260496129453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227490202764374027989678541 85308826036640260496129453)
        ·
          refine ⟨31990809763740097686048545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85308826036640260496129453 31990809763740097686048545)
          ·
            refine ⟨23993107322805073264536409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31990809763740097686048545 23993107322805073264536409)
            ·
              refine ⟨17994830492103804948402307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23993107322805073264536409 17994830492103804948402307)
              ·
                refine ⟨26992245738155707422603461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17994830492103804948402307 26992245738155707422603461)
                ·
                  refine ⟨5061046075904195141738149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26992245738155707422603461 5061046075904195141738149)
                  ·
                    refine ⟨948946139232036589075903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5061046075904195141738149 948946139232036589075903)
                    ·
                      rfl

theorem cell22_2772099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_2772099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772099 prefixEnd_2772099 := by exact prefixLift 2772099
  have htrace : WordTrace (prefixWord ++ tailWord_2772099) baseStart_2772099 baseEnd_2772099 := by
    simpa [prefixWord, tailWord_2772099, baseEnd_2772099] using wordTrace_append hprefix tailTrace_2772099
  have hstable : (prefixWord ++ tailWord_2772099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772099).length < 2 ^ (prefixWord ++ tailWord_2772099).sum := by decide
  have hdescent : baseEnd_2772099 < baseStart_2772099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772129 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2772129 : Nat := 118140960795 + 2772129 * 2 ^ 59
def prefixEnd_2772129 : Nat := 4983230072969 + 3 ^ 40 * 2772129 * 2
def baseEnd_2772129 : Nat := 948956408845126510825811

theorem tailTrace_2772129 : CollatzResearch.WordTrace tailWord_2772129 prefixEnd_2772129 948956408845126510825811 := by
  unfold tailWord_2772129
  simp only [CollatzResearch.WordTrace]
  refine ⟨101107850974057549785671441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67405233982705033190447627 101107850974057549785671441)
  ·
    refine ⟨75830888230543162339253581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101107850974057549785671441 75830888230543162339253581)
    ·
      refine ⟨28436583086453685877220093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75830888230543162339253581 28436583086453685877220093)
      ·
        refine ⟨10663718657420132203957535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28436583086453685877220093 10663718657420132203957535)
        ·
          refine ⟨15995577986130198305936303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10663718657420132203957535 15995577986130198305936303)
          ·
            refine ⟨23993366979195297458904455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15995577986130198305936303 23993366979195297458904455)
            ·
              refine ⟨35990050468792946188356683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23993366979195297458904455 35990050468792946188356683)
              ·
                refine ⟨53985075703189419282535025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35990050468792946188356683 53985075703189419282535025)
                ·
                  refine ⟨40488806777392064461901269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53985075703189419282535025 40488806777392064461901269)
                  ·
                    refine ⟨948956408845126510825811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40488806777392064461901269 948956408845126510825811)
                    ·
                      rfl

theorem cell22_2772129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2772129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772129 prefixEnd_2772129 := by exact prefixLift 2772129
  have htrace : WordTrace (prefixWord ++ tailWord_2772129) baseStart_2772129 baseEnd_2772129 := by
    simpa [prefixWord, tailWord_2772129, baseEnd_2772129] using wordTrace_append hprefix tailTrace_2772129
  have hstable : (prefixWord ++ tailWord_2772129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772129).length < 2 ^ (prefixWord ++ tailWord_2772129).sum := by decide
  have hdescent : baseEnd_2772129 < baseStart_2772129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772159 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 7]
def baseStart_2772159 : Nat := 118140960795 + 2772159 * 2 ^ 59
def prefixEnd_2772159 : Nat := 4983230072969 + 3 ^ 40 * 2772159 * 2
def baseEnd_2772159 : Nat := 316322226152738810858573

theorem tailTrace_2772159 : CollatzResearch.WordTrace tailWord_2772159 prefixEnd_2772159 316322226152738810858573 := by
  unfold tailWord_2772159
  simp only [CollatzResearch.WordTrace]
  refine ⟨101108945163948864909263531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67405963442632576606175687 101108945163948864909263531)
  ·
    refine ⟨151663417745923297363895297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101108945163948864909263531 151663417745923297363895297)
    ·
      refine ⟨113747563309442473022921473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151663417745923297363895297 113747563309442473022921473)
      ·
        refine ⟨85310672482081854767191105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113747563309442473022921473 85310672482081854767191105)
        ·
          refine ⟨63983004361561391075393329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85310672482081854767191105 63983004361561391075393329)
          ·
            refine ⟨47987253271171043306544997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63983004361561391075393329 47987253271171043306544997)
            ·
              refine ⟨8997609988344570619977187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47987253271171043306544997 8997609988344570619977187)
              ·
                refine ⟨13496414982516855929965781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8997609988344570619977187 13496414982516855929965781)
                ·
                  refine ⟨316322226152738810858573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13496414982516855929965781 316322226152738810858573)
                  ·
                    rfl

theorem cell22_2772159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_2772159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772159 prefixEnd_2772159 := by exact prefixLift 2772159
  have htrace : WordTrace (prefixWord ++ tailWord_2772159) baseStart_2772159 baseEnd_2772159 := by
    simpa [prefixWord, tailWord_2772159, baseEnd_2772159] using wordTrace_append hprefix tailTrace_2772159
  have hstable : (prefixWord ++ tailWord_2772159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772159).length < 2 ^ (prefixWord ++ tailWord_2772159).sum := by decide
  have hdescent : baseEnd_2772159 < baseStart_2772159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772236 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_2772236 : Nat := 118140960795 + 2772236 * 2 ^ 59
def prefixEnd_2772236 : Nat := 4983230072969 + 3 ^ 40 * 2772236 * 2
def baseEnd_2772236 : Nat := 948993037131813898400483

theorem tailTrace_2772236 : CollatzResearch.WordTrace tailWord_2772236 prefixEnd_2772236 948993037131813898400483 := by
  unfold tailWord_2772236
  simp only [CollatzResearch.WordTrace]
  refine ⟨50555876792334953529908281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67407835723113271373211041 50555876792334953529908281)
  ·
    refine ⟨37916907594251215147431211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50555876792334953529908281 37916907594251215147431211)
    ·
      refine ⟨56875361391376822721146817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37916907594251215147431211 56875361391376822721146817)
      ·
        refine ⟨42656521043532617040860113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56875361391376822721146817 42656521043532617040860113)
        ·
          refine ⟨31992390782649462780645085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42656521043532617040860113 31992390782649462780645085)
          ·
            refine ⟨11997146543493548542741907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31992390782649462780645085 11997146543493548542741907)
            ·
              refine ⟨17995719815240322814112861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11997146543493548542741907 17995719815240322814112861)
              ·
                refine ⟨6748394930715121055292323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17995719815240322814112861 6748394930715121055292323)
                ·
                  refine ⟨10122592396072681582938485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748394930715121055292323 10122592396072681582938485)
                  ·
                    refine ⟨948993037131813898400483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10122592396072681582938485 948993037131813898400483)
                    ·
                      rfl

theorem cell22_2772236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_2772236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772236 prefixEnd_2772236 := by exact prefixLift 2772236
  have htrace : WordTrace (prefixWord ++ tailWord_2772236) baseStart_2772236 baseEnd_2772236 := by
    simpa [prefixWord, tailWord_2772236, baseEnd_2772236] using wordTrace_append hprefix tailTrace_2772236
  have hstable : (prefixWord ++ tailWord_2772236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772236).length < 2 ^ (prefixWord ++ tailWord_2772236).sum := by decide
  have hdescent : baseEnd_2772236 < baseStart_2772236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772253 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2772253 : Nat := 118140960795 + 2772253 * 2 ^ 59
def prefixEnd_2772253 : Nat := 4983230072969 + 3 ^ 40 * 2772253 * 2
def baseEnd_2772253 : Nat := 948998856579231520725431

theorem tailTrace_2772253 : CollatzResearch.WordTrace tailWord_2772253 prefixEnd_2772253 948998856579231520725431 := by
  unfold tailWord_2772253
  simp only [CollatzResearch.WordTrace]
  refine ⟨101112373625608318963185413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67408249083738879308790275 101112373625608318963185413)
  ·
    refine ⟨18958570054801559805597265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101112373625608318963185413 18958570054801559805597265)
    ·
      refine ⟨14218927541101169854197949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18958570054801559805597265 14218927541101169854197949)
      ·
        refine ⟨5332097827912938695324231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14218927541101169854197949 5332097827912938695324231)
        ·
          refine ⟨7998146741869408042986347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332097827912938695324231 7998146741869408042986347)
          ·
            refine ⟨11997220112804112064479521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998146741869408042986347 11997220112804112064479521)
            ·
              refine ⟨8997915084603084048359641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11997220112804112064479521 8997915084603084048359641)
              ·
                refine ⟨6748436313452313036269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8997915084603084048359641 6748436313452313036269731)
                ·
                  refine ⟨10122654470178469554404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748436313452313036269731 10122654470178469554404597)
                  ·
                    refine ⟨948998856579231520725431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10122654470178469554404597 948998856579231520725431)
                    ·
                      rfl

theorem cell22_2772253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2772253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772253 prefixEnd_2772253 := by exact prefixLift 2772253
  have htrace : WordTrace (prefixWord ++ tailWord_2772253) baseStart_2772253 baseEnd_2772253 := by
    simpa [prefixWord, tailWord_2772253, baseEnd_2772253] using wordTrace_append hprefix tailTrace_2772253
  have hstable : (prefixWord ++ tailWord_2772253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772253).length < 2 ^ (prefixWord ++ tailWord_2772253).sum := by decide
  have hdescent : baseEnd_2772253 < baseStart_2772253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772255 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 4]
def baseStart_2772255 : Nat := 118140960795 + 2772255 * 2 ^ 59
def prefixEnd_2772255 : Nat := 4983230072969 + 3 ^ 40 * 2772255 * 2
def baseEnd_2772255 : Nat := 316333180406701394058475

theorem tailTrace_2772255 : CollatzResearch.WordTrace tailWord_2772255 prefixEnd_2772255 316333180406701394058475 := by
  unfold tailWord_2772255
  simp only [CollatzResearch.WordTrace]
  refine ⟨101112446571601073304758219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67408297714400715536505479 101112446571601073304758219)
  ·
    refine ⟨151668669857401609957137329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101112446571601073304758219 151668669857401609957137329)
    ·
      refine ⟨113751502393051207467852997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151668669857401609957137329 113751502393051207467852997)
      ·
        refine ⟨21328406698697101400222437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113751502393051207467852997 21328406698697101400222437)
        ·
          refine ⟨3999076256005706512541707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21328406698697101400222437 3999076256005706512541707)
          ·
            refine ⟨5998614384008559768812561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999076256005706512541707 5998614384008559768812561)
            ·
              refine ⟨4498960788006419826609421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5998614384008559768812561 4498960788006419826609421)
              ·
                refine ⟨1687110295502407434978533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4498960788006419826609421 1687110295502407434978533)
                ·
                  refine ⟨316333180406701394058475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1687110295502407434978533 316333180406701394058475)
                  ·
                    rfl

theorem cell22_2772255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 4].length) (baseStart_2772255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772255 prefixEnd_2772255 := by exact prefixLift 2772255
  have htrace : WordTrace (prefixWord ++ tailWord_2772255) baseStart_2772255 baseEnd_2772255 := by
    simpa [prefixWord, tailWord_2772255, baseEnd_2772255] using wordTrace_append hprefix tailTrace_2772255
  have hstable : (prefixWord ++ tailWord_2772255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772255).length < 2 ^ (prefixWord ++ tailWord_2772255).sum := by decide
  have hdescent : baseEnd_2772255 < baseStart_2772255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772311 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 7]
def baseStart_2772311 : Nat := 118140960795 + 2772311 * 2 ^ 59
def prefixEnd_2772311 : Nat := 4983230072969 + 3 ^ 40 * 2772311 * 2
def baseEnd_2772311 : Nat := 316339570388179567591751

theorem tailTrace_2772311 : CollatzResearch.WordTrace tailWord_2772311 prefixEnd_2772311 316339570388179567591751 := by
  unfold tailWord_2772311
  simp only [CollatzResearch.WordTrace]
  refine ⟨101114489059398194868796787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67409659372932129912531191 101114489059398194868796787)
  ·
    refine ⟨151671733589097292303195181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101114489059398194868796787 151671733589097292303195181)
    ·
      refine ⟨56876900095911484613698193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151671733589097292303195181 56876900095911484613698193)
      ·
        refine ⟨42657675071933613460273645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56876900095911484613698193 42657675071933613460273645)
        ·
          refine ⟨15996628151975105047602617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42657675071933613460273645 15996628151975105047602617)
          ·
            refine ⟨11997471113981328785701963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15996628151975105047602617 11997471113981328785701963)
            ·
              refine ⟨17996206670971993178552945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11997471113981328785701963 17996206670971993178552945)
              ·
                refine ⟨13497155003228994883914709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17996206670971993178552945 13497155003228994883914709)
                ·
                  refine ⟨316339570388179567591751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13497155003228994883914709 316339570388179567591751)
                  ·
                    rfl

theorem cell22_2772311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_2772311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772311 prefixEnd_2772311 := by exact prefixLift 2772311
  have htrace : WordTrace (prefixWord ++ tailWord_2772311) baseStart_2772311 baseEnd_2772311 := by
    simpa [prefixWord, tailWord_2772311, baseEnd_2772311] using wordTrace_append hprefix tailTrace_2772311
  have hstable : (prefixWord ++ tailWord_2772311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772311).length < 2 ^ (prefixWord ++ tailWord_2772311).sum := by decide
  have hdescent : baseEnd_2772311 < baseStart_2772311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772317 : List Nat := [1, 4, 5, 1, 1, 2, 8]
def baseStart_2772317 : Nat := 118140960795 + 2772317 * 2 ^ 59
def prefixEnd_2772317 : Nat := 4983230072969 + 3 ^ 40 * 2772317 * 2
def baseEnd_2772317 : Nat := 35148917225450247671305

theorem tailTrace_2772317 : CollatzResearch.WordTrace tailWord_2772317 prefixEnd_2772317 35148917225450247671305 := by
  unfold tailWord_2772317
  simp only [CollatzResearch.WordTrace]
  refine ⟨101114707897376457893515205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67409805264917638595676803 101114707897376457893515205)
  ·
    refine ⟨18959007730758085855034101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101114707897376457893515205 18959007730758085855034101)
    ·
      refine ⟨1777406974758570548909447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18959007730758085855034101 1777406974758570548909447)
      ·
        refine ⟨2666110462137855823364171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777406974758570548909447 2666110462137855823364171)
        ·
          refine ⟨3999165693206783735046257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666110462137855823364171 3999165693206783735046257)
          ·
            refine ⟨2999374269905087801284693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999165693206783735046257 2999374269905087801284693)
            ·
              refine ⟨35148917225450247671305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2999374269905087801284693 35148917225450247671305)
              ·
                rfl

theorem cell22_2772317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 8].length) (baseStart_2772317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772317 prefixEnd_2772317 := by exact prefixLift 2772317
  have htrace : WordTrace (prefixWord ++ tailWord_2772317) baseStart_2772317 baseEnd_2772317 := by
    simpa [prefixWord, tailWord_2772317, baseEnd_2772317] using wordTrace_append hprefix tailTrace_2772317
  have hstable : (prefixWord ++ tailWord_2772317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772317).length < 2 ^ (prefixWord ++ tailWord_2772317).sum := by decide
  have hdescent : baseEnd_2772317 < baseStart_2772317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772405 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2772405 : Nat := 118140960795 + 2772405 * 2 ^ 59
def prefixEnd_2772405 : Nat := 4983230072969 + 3 ^ 40 * 2772405 * 2
def baseEnd_2772405 : Nat := 949050889285553790924965

theorem tailTrace_2772405 : CollatzResearch.WordTrace tailWord_2772405 prefixEnd_2772405 949050889285553790924965 := by
  unfold tailWord_2772405
  simp only [CollatzResearch.WordTrace]
  refine ⟨101117917521057648922718669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67411945014038432615145779 101117917521057648922718669)
  ·
    refine ⟨37919219070396618346019501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101117917521057648922718669 37919219070396618346019501)
    ·
      refine ⟨14219707151398731879757313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37919219070396618346019501 14219707151398731879757313)
      ·
        refine ⟨10664780363549048909817985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14219707151398731879757313 10664780363549048909817985)
        ·
          refine ⟨7998585272661786682363489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10664780363549048909817985 7998585272661786682363489)
          ·
            refine ⟨5998938954496340011772617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7998585272661786682363489 5998938954496340011772617)
            ·
              refine ⟨4499204215872255008829463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5998938954496340011772617 4499204215872255008829463)
              ·
                refine ⟨6748806323808382513244195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499204215872255008829463 6748806323808382513244195)
                ·
                  refine ⟨10123209485712573769866293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6748806323808382513244195 10123209485712573769866293)
                  ·
                    refine ⟨949050889285553790924965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10123209485712573769866293 949050889285553790924965)
                    ·
                      rfl

theorem cell22_2772405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2772405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772405 prefixEnd_2772405 := by exact prefixLift 2772405
  have htrace : WordTrace (prefixWord ++ tailWord_2772405) baseStart_2772405 baseEnd_2772405 := by
    simpa [prefixWord, tailWord_2772405, baseEnd_2772405] using wordTrace_append hprefix tailTrace_2772405
  have hstable : (prefixWord ++ tailWord_2772405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772405).length < 2 ^ (prefixWord ++ tailWord_2772405).sum := by decide
  have hdescent : baseEnd_2772405 < baseStart_2772405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772420 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2772420 : Nat := 118140960795 + 2772420 * 2 ^ 59
def prefixEnd_2772420 : Nat := 4983230072969 + 3 ^ 40 * 2772420 * 2
def baseEnd_2772420 : Nat := 949056024092098751799919

theorem tailTrace_2772420 : CollatzResearch.WordTrace tailWord_2772420 prefixEnd_2772420 949056024092098751799919 := by
  unfold tailWord_2772420
  simp only [CollatzResearch.WordTrace]
  refine ⟨50559232308001653242257357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67412309744002204323009809 50559232308001653242257357)
  ·
    refine ⟨18959712115500619965846509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50559232308001653242257357 18959712115500619965846509)
    ·
      refine ⟨7109892043312732487192441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18959712115500619965846509 7109892043312732487192441)
      ·
        refine ⟨5332419032484549365394331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7109892043312732487192441 5332419032484549365394331)
        ·
          refine ⟨7998628548726824048091497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5332419032484549365394331 7998628548726824048091497)
          ·
            refine ⟨5998971411545118036068623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7998628548726824048091497 5998971411545118036068623)
            ·
              refine ⟨8998457117317677054102935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998971411545118036068623 8998457117317677054102935)
              ·
                refine ⟨13497685675976515581154403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8998457117317677054102935 13497685675976515581154403)
                ·
                  refine ⟨20246528513964773371731605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13497685675976515581154403 20246528513964773371731605)
                  ·
                    refine ⟨949056024092098751799919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20246528513964773371731605 949056024092098751799919)
                    ·
                      rfl

theorem cell22_2772420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2772420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772420 prefixEnd_2772420 := by exact prefixLift 2772420
  have htrace : WordTrace (prefixWord ++ tailWord_2772420) baseStart_2772420 baseEnd_2772420 := by
    simpa [prefixWord, tailWord_2772420, baseEnd_2772420] using wordTrace_append hprefix tailTrace_2772420
  have hstable : (prefixWord ++ tailWord_2772420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772420).length < 2 ^ (prefixWord ++ tailWord_2772420).sum := by decide
  have hdescent : baseEnd_2772420 < baseStart_2772420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772463 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 5]
def baseStart_2772463 : Nat := 118140960795 + 2772463 * 2 ^ 59
def prefixEnd_2772463 : Nat := 4983230072969 + 3 ^ 40 * 2772463 * 2
def baseEnd_2772463 : Nat := 316356914623620324324929

theorem tailTrace_2772463 : CollatzResearch.WordTrace tailWord_2772463 prefixEnd_2772463 316356914623620324324929 := by
  unfold tailWord_2772463
  simp only [CollatzResearch.WordTrace]
  refine ⟨101120032954847524828330043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67413355303231683218886695 101120032954847524828330043)
  ·
    refine ⟨151680049432271287242495065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101120032954847524828330043 151680049432271287242495065)
    ·
      refine ⟨113760037074203465431871299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151680049432271287242495065 113760037074203465431871299)
      ·
        refine ⟨170640055611305198147806949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113760037074203465431871299 170640055611305198147806949)
        ·
          refine ⟨31995010427119724652713803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170640055611305198147806949 31995010427119724652713803)
          ·
            refine ⟨47992515640679586979070705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31995010427119724652713803 47992515640679586979070705)
            ·
              refine ⟨35994386730509690234303029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47992515640679586979070705 35994386730509690234303029)
              ·
                refine ⟨3374473755985283459465909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35994386730509690234303029 3374473755985283459465909)
                ·
                  refine ⟨316356914623620324324929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3374473755985283459465909 316356914623620324324929)
                  ·
                    rfl

theorem cell22_2772463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 5].length) (baseStart_2772463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772463 prefixEnd_2772463 := by exact prefixLift 2772463
  have htrace : WordTrace (prefixWord ++ tailWord_2772463) baseStart_2772463 baseEnd_2772463 := by
    simpa [prefixWord, tailWord_2772463, baseEnd_2772463] using wordTrace_append hprefix tailTrace_2772463
  have hstable : (prefixWord ++ tailWord_2772463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772463).length < 2 ^ (prefixWord ++ tailWord_2772463).sum := by decide
  have hdescent : baseEnd_2772463 < baseStart_2772463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772486 : List Nat := [6, 2, 1, 1, 3, 1, 8]
def baseStart_2772486 : Nat := 118140960795 + 2772486 * 2 ^ 59
def prefixEnd_2772486 : Nat := 4983230072969 + 3 ^ 40 * 2772486 * 2
def baseEnd_2772486 : Nat := 35151059897810984431471

theorem tailTrace_2772486 : CollatzResearch.WordTrace tailWord_2772486 prefixEnd_2772486 35151059897810984431471 := by
  unfold tailWord_2772486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160027244805131242388041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67413914555842799837611541 3160027244805131242388041)
  ·
    refine ⟨2370020433603848431791031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160027244805131242388041 2370020433603848431791031)
    ·
      refine ⟨3555030650405772647686547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370020433603848431791031 3555030650405772647686547)
      ·
        refine ⟨5332545975608658971529821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555030650405772647686547 5332545975608658971529821)
        ·
          refine ⟨1999704740853247114323683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332545975608658971529821 1999704740853247114323683)
          ·
            refine ⟨2999557111279870671485525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999704740853247114323683 2999557111279870671485525)
            ·
              refine ⟨35151059897810984431471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2999557111279870671485525 35151059897810984431471)
              ·
                rfl

theorem cell22_2772486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 8].length) (baseStart_2772486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772486 prefixEnd_2772486 := by exact prefixLift 2772486
  have htrace : WordTrace (prefixWord ++ tailWord_2772486) baseStart_2772486 baseEnd_2772486 := by
    simpa [prefixWord, tailWord_2772486, baseEnd_2772486] using wordTrace_append hprefix tailTrace_2772486
  have hstable : (prefixWord ++ tailWord_2772486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772486).length < 2 ^ (prefixWord ++ tailWord_2772486).sum := by decide
  have hdescent : baseEnd_2772486 < baseStart_2772486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772568 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_2772568 : Nat := 118140960795 + 2772568 * 2 ^ 59
def prefixEnd_2772568 : Nat := 4983230072969 + 3 ^ 40 * 2772568 * 2
def baseEnd_2772568 : Nat := 949106687516675699099465

theorem tailTrace_2772568 : CollatzResearch.WordTrace tailWord_2772568 prefixEnd_2772568 949106687516675699099465 := by
  unfold tailWord_2772568
  simp only [CollatzResearch.WordTrace]
  refine ⟨50561931309733563880451179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67415908412978085173934905 50561931309733563880451179)
  ·
    refine ⟨75842896964600345820676769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50561931309733563880451179 75842896964600345820676769)
    ·
      refine ⟨56882172723450259365507577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75842896964600345820676769 56882172723450259365507577)
      ·
        refine ⟨42661629542587694524130683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56882172723450259365507577 42661629542587694524130683)
        ·
          refine ⟨63992444313881541786196025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42661629542587694524130683 63992444313881541786196025)
          ·
            refine ⟨47994333235411156339647019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63992444313881541786196025 47994333235411156339647019)
            ·
              refine ⟨71991499853116734509470529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47994333235411156339647019 71991499853116734509470529)
              ·
                refine ⟨53993624889837550882102897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71991499853116734509470529 53993624889837550882102897)
                ·
                  refine ⟨40495218667378163161577173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53993624889837550882102897 40495218667378163161577173)
                  ·
                    refine ⟨949106687516675699099465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40495218667378163161577173 949106687516675699099465)
                    ·
                      rfl

theorem cell22_2772568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_2772568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772568 prefixEnd_2772568 := by exact prefixLift 2772568
  have htrace : WordTrace (prefixWord ++ tailWord_2772568) baseStart_2772568 baseEnd_2772568 := by
    simpa [prefixWord, tailWord_2772568, baseEnd_2772568] using wordTrace_append hprefix tailTrace_2772568
  have hstable : (prefixWord ++ tailWord_2772568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772568).length < 2 ^ (prefixWord ++ tailWord_2772568).sum := by decide
  have hdescent : baseEnd_2772568 < baseStart_2772568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772585 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 5, 3]
def baseStart_2772585 : Nat := 118140960795 + 2772585 * 2 ^ 59
def prefixEnd_2772585 : Nat := 4983230072969 + 3 ^ 40 * 2772585 * 2
def baseEnd_2772585 : Nat := 949112506964093321424413

theorem tailTrace_2772585 : CollatzResearch.WordTrace tailWord_2772585 prefixEnd_2772585 949112506964093321424413 := by
  unfold tailWord_2772585
  simp only [CollatzResearch.WordTrace]
  refine ⟨101124482660405539664271209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67416321773603693109514139 101124482660405539664271209)
  ·
    refine ⟨75843361995304154748203407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101124482660405539664271209 75843361995304154748203407)
    ·
      refine ⟨113765042992956232122305111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75843361995304154748203407 113765042992956232122305111)
      ·
        refine ⟨170647564489434348183457667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113765042992956232122305111 170647564489434348183457667)
        ·
          refine ⟨255971346734151522275186501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170647564489434348183457667 255971346734151522275186501)
          ·
            refine ⟨47994627512653410426597469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255971346734151522275186501 47994627512653410426597469)
            ·
              refine ⟨17997985317245028909974051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47994627512653410426597469 17997985317245028909974051)
              ·
                refine ⟨26996977975867543364961077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17997985317245028909974051 26996977975867543364961077)
                ·
                  refine ⟨2530966685237582190465101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26996977975867543364961077 2530966685237582190465101)
                  ·
                    refine ⟨949112506964093321424413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2530966685237582190465101 949112506964093321424413)
                    ·
                      rfl

theorem cell22_2772585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 3].length) (baseStart_2772585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772585 prefixEnd_2772585 := by exact prefixLift 2772585
  have htrace : WordTrace (prefixWord ++ tailWord_2772585) baseStart_2772585 baseEnd_2772585 := by
    simpa [prefixWord, tailWord_2772585, baseEnd_2772585] using wordTrace_append hprefix tailTrace_2772585
  have hstable : (prefixWord ++ tailWord_2772585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772585).length < 2 ^ (prefixWord ++ tailWord_2772585).sum := by decide
  have hdescent : baseEnd_2772585 < baseStart_2772585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772589 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2772589 : Nat := 118140960795 + 2772589 * 2 ^ 59
def prefixEnd_2772589 : Nat := 4983230072969 + 3 ^ 40 * 2772589 * 2
def baseEnd_2772589 : Nat := 949113876245838644324401

theorem tailTrace_2772589 : CollatzResearch.WordTrace tailWord_2772589 prefixEnd_2772589 949113876245838644324401 := by
  unfold tailWord_2772589
  simp only [CollatzResearch.WordTrace]
  refine ⟨101124628552391048347416821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67416419034927365564944547 101124628552391048347416821)
  ·
    refine ⟨9480433926786660782570327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101124628552391048347416821 9480433926786660782570327)
    ·
      refine ⟨14220650890179991173855491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9480433926786660782570327 14220650890179991173855491)
      ·
        refine ⟨21330976335269986760783237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14220650890179991173855491 21330976335269986760783237)
        ·
          refine ⟨3999558062863122517646857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21330976335269986760783237 3999558062863122517646857)
          ·
            refine ⟨2999668547147341888235143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3999558062863122517646857 2999668547147341888235143)
            ·
              refine ⟨4499502820721012832352715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999668547147341888235143 4499502820721012832352715)
              ·
                refine ⟨6749254231081519248529073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499502820721012832352715 6749254231081519248529073)
                ·
                  refine ⟨5061940673311139436396805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6749254231081519248529073 5061940673311139436396805)
                  ·
                    refine ⟨949113876245838644324401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5061940673311139436396805 949113876245838644324401)
                    ·
                      rfl

theorem cell22_2772589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2772589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772589 prefixEnd_2772589 := by exact prefixLift 2772589
  have htrace : WordTrace (prefixWord ++ tailWord_2772589) baseStart_2772589 baseEnd_2772589 := by
    simpa [prefixWord, tailWord_2772589, baseEnd_2772589] using wordTrace_append hprefix tailTrace_2772589
  have hstable : (prefixWord ++ tailWord_2772589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772589).length < 2 ^ (prefixWord ++ tailWord_2772589).sum := by decide
  have hdescent : baseEnd_2772589 < baseStart_2772589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772615 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 7]
def baseStart_2772615 : Nat := 118140960795 + 2772615 * 2 ^ 59
def prefixEnd_2772615 : Nat := 4983230072969 + 3 ^ 40 * 2772615 * 2
def baseEnd_2772615 : Nat := 316374258859061081058107

theorem tailTrace_2772615 : CollatzResearch.WordTrace tailWord_2772615 prefixEnd_2772615 316374258859061081058107 := by
  unfold tailWord_2772615
  simp only [CollatzResearch.WordTrace]
  refine ⟨101125576850296854787863299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67417051233531236525242199 101125576850296854787863299)
  ·
    refine ⟨151688365275445282181794949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101125576850296854787863299 151688365275445282181794949)
    ·
      refine ⟨28441568489145990409086553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151688365275445282181794949 28441568489145990409086553)
      ·
        refine ⟨21331176366859492806814915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28441568489145990409086553 21331176366859492806814915)
        ·
          refine ⟨31996764550289239210222373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21331176366859492806814915 31996764550289239210222373)
          ·
            refine ⟨5999393353179232351916695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31996764550289239210222373 5999393353179232351916695)
            ·
              refine ⟨8999090029768848527875043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5999393353179232351916695 8999090029768848527875043)
              ·
                refine ⟨13498635044653272791812565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8999090029768848527875043 13498635044653272791812565)
                ·
                  refine ⟨316374258859061081058107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13498635044653272791812565 316374258859061081058107)
                  ·
                    rfl

theorem cell22_2772615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_2772615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772615 prefixEnd_2772615 := by exact prefixLift 2772615
  have htrace : WordTrace (prefixWord ++ tailWord_2772615) baseStart_2772615 baseEnd_2772615 := by
    simpa [prefixWord, tailWord_2772615, baseEnd_2772615] using wordTrace_append hprefix tailTrace_2772615
  have hstable : (prefixWord ++ tailWord_2772615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772615).length < 2 ^ (prefixWord ++ tailWord_2772615).sum := by decide
  have hdescent : baseEnd_2772615 < baseStart_2772615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772645 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_2772645 : Nat := 118140960795 + 2772645 * 2 ^ 59
def prefixEnd_2772645 : Nat := 4983230072969 + 3 ^ 40 * 2772645 * 2
def baseEnd_2772645 : Nat := 949133046190273164924229

theorem tailTrace_2772645 : CollatzResearch.WordTrace tailWord_2772645 prefixEnd_2772645 949133046190273164924229 := by
  unfold tailWord_2772645
  simp only [CollatzResearch.WordTrace]
  refine ⟨101126671040188169911455389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67417780693458779940970259 101126671040188169911455389)
  ·
    refine ⟨37922501640070563716795771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101126671040188169911455389 37922501640070563716795771)
    ·
      refine ⟨56883752460105845575193657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37922501640070563716795771 56883752460105845575193657)
      ·
        refine ⟨42662814345079384181395243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56883752460105845575193657 42662814345079384181395243)
        ·
          refine ⟨63994221517619076272092865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42662814345079384181395243 63994221517619076272092865)
          ·
            refine ⟨47995666138214307204069649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63994221517619076272092865 47995666138214307204069649)
            ·
              refine ⟨35996749603660730403052237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47995666138214307204069649 35996749603660730403052237)
              ·
                refine ⟨13498781101372773901144589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35996749603660730403052237 13498781101372773901144589)
                ·
                  refine ⟨5062042913014790212929221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13498781101372773901144589 5062042913014790212929221)
                  ·
                    refine ⟨949133046190273164924229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062042913014790212929221 949133046190273164924229)
                    ·
                      rfl

theorem cell22_2772645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_2772645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772645 prefixEnd_2772645 := by exact prefixLift 2772645
  have htrace : WordTrace (prefixWord ++ tailWord_2772645) baseStart_2772645 baseEnd_2772645 := by
    simpa [prefixWord, tailWord_2772645, baseEnd_2772645] using wordTrace_append hprefix tailTrace_2772645
  have hstable : (prefixWord ++ tailWord_2772645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772645).length < 2 ^ (prefixWord ++ tailWord_2772645).sum := by decide
  have hdescent : baseEnd_2772645 < baseStart_2772645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772726 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 2, 3]
def baseStart_2772726 : Nat := 118140960795 + 2772726 * 2 ^ 59
def prefixEnd_2772726 : Nat := 4983230072969 + 3 ^ 40 * 2772726 * 2
def baseEnd_2772726 : Nat := 949160774145615953648981

theorem tailTrace_2772726 : CollatzResearch.WordTrace tailWord_2772726 prefixEnd_2772726 949160774145615953648981 := by
  unfold tailWord_2772726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320601584555920046572127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67419750235263147163436021 6320601584555920046572127)
  ·
    refine ⟨9480902376833880069858191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6320601584555920046572127 9480902376833880069858191)
    ·
      refine ⟨14221353565250820104787287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9480902376833880069858191 14221353565250820104787287)
      ·
        refine ⟨21332030347876230157180931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14221353565250820104787287 21332030347876230157180931)
        ·
          refine ⟨31998045521814345235771397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21332030347876230157180931 31998045521814345235771397)
          ·
            refine ⟨5999633535340189731707137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31998045521814345235771397 5999633535340189731707137)
            ·
              refine ⟨4499725151505142298780353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999633535340189731707137 4499725151505142298780353)
              ·
                refine ⟨3374793863628856724085265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499725151505142298780353 3374793863628856724085265)
                ·
                  refine ⟨2531095397721642543063949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374793863628856724085265 2531095397721642543063949)
                  ·
                    refine ⟨949160774145615953648981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531095397721642543063949 949160774145615953648981)
                    ·
                      rfl

theorem cell22_2772726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_2772726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772726 prefixEnd_2772726 := by exact prefixLift 2772726
  have htrace : WordTrace (prefixWord ++ tailWord_2772726) baseStart_2772726 baseEnd_2772726 := by
    simpa [prefixWord, tailWord_2772726, baseEnd_2772726] using wordTrace_append hprefix tailTrace_2772726
  have hstable : (prefixWord ++ tailWord_2772726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772726).length < 2 ^ (prefixWord ++ tailWord_2772726).sum := by decide
  have hdescent : baseEnd_2772726 < baseStart_2772726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772735 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_2772735 : Nat := 118140960795 + 2772735 * 2 ^ 59
def prefixEnd_2772735 : Nat := 4983230072969 + 3 ^ 40 * 2772735 * 2
def baseEnd_2772735 : Nat := 949163855029542930173953

theorem tailTrace_2772735 : CollatzResearch.WordTrace tailWord_2772735 prefixEnd_2772735 949163855029542930173953 := by
  unfold tailWord_2772735
  simp only [CollatzResearch.WordTrace]
  refine ⟨101129953609862115282231659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67419969073241410188154439 101129953609862115282231659)
  ·
    refine ⟨151694930414793172923347489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101129953609862115282231659 151694930414793172923347489)
    ·
      refine ⟨113771197811094879692510617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151694930414793172923347489 113771197811094879692510617)
      ·
        refine ⟨85328398358321159769382963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113771197811094879692510617 85328398358321159769382963)
        ·
          refine ⟨127992597537481739654074445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85328398358321159769382963 127992597537481739654074445)
          ·
            refine ⟨47997224076555652370277917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127992597537481739654074445 47997224076555652370277917)
            ·
              refine ⟨17998959028708369638854219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47997224076555652370277917 17998959028708369638854219)
              ·
                refine ⟨26998438543062554458281329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17998959028708369638854219 26998438543062554458281329)
                ·
                  refine ⟨20248828907296915843710997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26998438543062554458281329 20248828907296915843710997)
                  ·
                    refine ⟨949163855029542930173953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20248828907296915843710997 949163855029542930173953)
                    ·
                      rfl

theorem cell22_2772735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_2772735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772735 prefixEnd_2772735 := by exact prefixLift 2772735
  have htrace : WordTrace (prefixWord ++ tailWord_2772735) baseStart_2772735 baseEnd_2772735 := by
    simpa [prefixWord, tailWord_2772735, baseEnd_2772735] using wordTrace_append hprefix tailTrace_2772735
  have hstable : (prefixWord ++ tailWord_2772735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772735).length < 2 ^ (prefixWord ++ tailWord_2772735).sum := by decide
  have hdescent : baseEnd_2772735 < baseStart_2772735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772788 : List Nat := [2, 5, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2772788 : Nat := 118140960795 + 2772788 * 2 ^ 59
def prefixEnd_2772788 : Nat := 4983230072969 + 3 ^ 40 * 2772788 * 2
def baseEnd_2772788 : Nat := 949181998012668458598791

theorem tailTrace_2772788 : CollatzResearch.WordTrace tailWord_2772788 prefixEnd_2772788 949181998012668458598791 := by
  unfold tailWord_2772788
  simp only [CollatzResearch.WordTrace]
  refine ⟨50565943339335052666955509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67421257785780070222607345 50565943339335052666955509)
  ·
    refine ⟨4740557188062661187527079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50565943339335052666955509 4740557188062661187527079)
    ·
      refine ⟨7110835782093991781290619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740557188062661187527079 7110835782093991781290619)
      ·
        refine ⟨10666253673140987671935929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110835782093991781290619 10666253673140987671935929)
        ·
          refine ⟨7999690254855740753951947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10666253673140987671935929 7999690254855740753951947)
          ·
            refine ⟨11999535382283611130927921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999690254855740753951947 11999535382283611130927921)
            ·
              refine ⟨8999651536712708348195941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11999535382283611130927921 8999651536712708348195941)
              ·
                refine ⟨1687434663133632815286739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8999651536712708348195941 1687434663133632815286739)
                ·
                  refine ⟨2531151994700449222930109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687434663133632815286739 2531151994700449222930109)
                  ·
                    refine ⟨949181998012668458598791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531151994700449222930109 949181998012668458598791)
                    ·
                      rfl

theorem cell22_2772788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2772788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772788 prefixEnd_2772788 := by exact prefixLift 2772788
  have htrace : WordTrace (prefixWord ++ tailWord_2772788) baseStart_2772788 baseEnd_2772788 := by
    simpa [prefixWord, tailWord_2772788, baseEnd_2772788] using wordTrace_append hprefix tailTrace_2772788
  have hstable : (prefixWord ++ tailWord_2772788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772788).length < 2 ^ (prefixWord ++ tailWord_2772788).sum := by decide
  have hdescent : baseEnd_2772788 < baseStart_2772788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772844 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_2772844 : Nat := 118140960795 + 2772844 * 2 ^ 59
def prefixEnd_2772844 : Nat := 4983230072969 + 3 ^ 40 * 2772844 * 2
def baseEnd_2772844 : Nat := 949201167957102979198619

theorem tailTrace_2772844 : CollatzResearch.WordTrace tailWord_2772844 prefixEnd_2772844 949201167957102979198619 := by
  unfold tailWord_2772844
  simp only [CollatzResearch.WordTrace]
  refine ⟨50566964583233613448974793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67422619444311484598633057 50566964583233613448974793)
  ·
    refine ⟨37925223437425210086731095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50566964583233613448974793 37925223437425210086731095)
    ·
      refine ⟨56887835156137815130096643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37925223437425210086731095 56887835156137815130096643)
      ·
        refine ⟨85331752734206722695144965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56887835156137815130096643 85331752734206722695144965)
        ·
          refine ⟨15999703637663760505339681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85331752734206722695144965 15999703637663760505339681)
          ·
            refine ⟨11999777728247820379004761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15999703637663760505339681 11999777728247820379004761)
            ·
              refine ⟨8999833296185865284253571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11999777728247820379004761 8999833296185865284253571)
              ·
                refine ⟨13499749944278797926380357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8999833296185865284253571 13499749944278797926380357)
                ·
                  refine ⟨2531203114552274611196317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13499749944278797926380357 2531203114552274611196317)
                  ·
                    refine ⟨949201167957102979198619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531203114552274611196317 949201167957102979198619)
                    ·
                      rfl

theorem cell22_2772844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_2772844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772844 prefixEnd_2772844 := by exact prefixLift 2772844
  have htrace : WordTrace (prefixWord ++ tailWord_2772844) baseStart_2772844 baseEnd_2772844 := by
    simpa [prefixWord, tailWord_2772844, baseEnd_2772844] using wordTrace_append hprefix tailTrace_2772844
  have hstable : (prefixWord ++ tailWord_2772844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772844).length < 2 ^ (prefixWord ++ tailWord_2772844).sum := by decide
  have hdescent : baseEnd_2772844 < baseStart_2772844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772846 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_2772846 : Nat := 118140960795 + 2772846 * 2 ^ 59
def prefixEnd_2772846 : Nat := 4983230072969 + 3 ^ 40 * 2772846 * 2
def baseEnd_2772846 : Nat := 316400617532658546882871

theorem tailTrace_2772846 : CollatzResearch.WordTrace tailWord_2772846 prefixEnd_2772846 316400617532658546882871 := by
  unfold tailWord_2772846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641750264057497654940299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67422668074973320826348261 12641750264057497654940299)
  ·
    refine ⟨18962625396086246482410449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641750264057497654940299 18962625396086246482410449)
    ·
      refine ⟨14221969047064684861807837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18962625396086246482410449 14221969047064684861807837)
      ·
        refine ⟨5333238392649256823177939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14221969047064684861807837 5333238392649256823177939)
        ·
          refine ⟨7999857588973885234766909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333238392649256823177939 7999857588973885234766909)
          ·
            refine ⟨2999946595865206963037591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7999857588973885234766909 2999946595865206963037591)
            ·
              refine ⟨4499919893797810444556387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999946595865206963037591 4499919893797810444556387)
              ·
                refine ⟨6749879840696715666834581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4499919893797810444556387 6749879840696715666834581)
                ·
                  refine ⟨316400617532658546882871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6749879840696715666834581 316400617532658546882871)
                  ·
                    rfl

theorem cell22_2772846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_2772846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772846 prefixEnd_2772846 := by exact prefixLift 2772846
  have htrace : WordTrace (prefixWord ++ tailWord_2772846) baseStart_2772846 baseEnd_2772846 := by
    simpa [prefixWord, tailWord_2772846, baseEnd_2772846] using wordTrace_append hprefix tailTrace_2772846
  have hstable : (prefixWord ++ tailWord_2772846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772846).length < 2 ^ (prefixWord ++ tailWord_2772846).sum := by decide
  have hdescent : baseEnd_2772846 < baseStart_2772846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772857 : List Nat := [1, 2, 1, 3, 2, 2, 4, 7]
def baseStart_2772857 : Nat := 118140960795 + 2772857 * 2 ^ 59
def prefixEnd_2772857 : Nat := 4983230072969 + 3 ^ 40 * 2772857 * 2
def baseEnd_2772857 : Nat := 105467290902530586513731

theorem tailTrace_2772857 : CollatzResearch.WordTrace tailWord_2772857 prefixEnd_2772857 105467290902530586513731 := by
  unfold tailWord_2772857
  simp only [CollatzResearch.WordTrace]
  refine ⟨101134403315420130118172825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67422935543613420078781883 101134403315420130118172825)
  ·
    refine ⟨75850802486565097588629619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101134403315420130118172825 75850802486565097588629619)
    ·
      refine ⟨113776203729847646382944429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75850802486565097588629619 113776203729847646382944429)
      ·
        refine ⟨42666076398692867393604161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113776203729847646382944429 42666076398692867393604161)
        ·
          refine ⟨31999557299019650545203121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42666076398692867393604161 31999557299019650545203121)
          ·
            refine ⟨23999667974264737908902341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31999557299019650545203121 23999667974264737908902341)
            ·
              refine ⟨4499937745174638357919189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23999667974264737908902341 4499937745174638357919189)
              ·
                refine ⟨105467290902530586513731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4499937745174638357919189 105467290902530586513731)
                ·
                  rfl

theorem cell22_2772857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 7].length) (baseStart_2772857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772857 prefixEnd_2772857 := by exact prefixLift 2772857
  have htrace : WordTrace (prefixWord ++ tailWord_2772857) baseStart_2772857 baseEnd_2772857 := by
    simpa [prefixWord, tailWord_2772857, baseEnd_2772857] using wordTrace_append hprefix tailTrace_2772857
  have hstable : (prefixWord ++ tailWord_2772857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772857).length < 2 ^ (prefixWord ++ tailWord_2772857).sum := by decide
  have hdescent : baseEnd_2772857 < baseStart_2772857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772865 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2772865 : Nat := 118140960795 + 2772865 * 2 ^ 59
def prefixEnd_2772865 : Nat := 4983230072969 + 3 ^ 40 * 2772865 * 2
def baseEnd_2772865 : Nat := 949208356686265924423555

theorem tailTrace_2772865 : CollatzResearch.WordTrace tailWord_2772865 prefixEnd_2772865 949208356686265924423555 := by
  unfold tailWord_2772865
  simp only [CollatzResearch.WordTrace]
  refine ⟨101134695099391147484464049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67423130066260764989642699 101134695099391147484464049)
  ·
    refine ⟨75851021324543360613348037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101134695099391147484464049 75851021324543360613348037)
    ·
      refine ⟨14222066498351880115002757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75851021324543360613348037 14222066498351880115002757)
      ·
        refine ⟨2666637468440977521563017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14222066498351880115002757 2666637468440977521563017)
        ·
          refine ⟨1999978101330733141172263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2666637468440977521563017 1999978101330733141172263)
          ·
            refine ⟨2999967151996099711758395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999978101330733141172263 2999967151996099711758395)
            ·
              refine ⟨4499950727994149567637593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2999967151996099711758395 4499950727994149567637593)
              ·
                refine ⟨3374963045995612175728195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499950727994149567637593 3374963045995612175728195)
                ·
                  refine ⟨5062444568993418263592293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374963045995612175728195 5062444568993418263592293)
                  ·
                    refine ⟨949208356686265924423555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062444568993418263592293 949208356686265924423555)
                    ·
                      rfl

theorem cell22_2772865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2772865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772865 prefixEnd_2772865 := by exact prefixLift 2772865
  have htrace : WordTrace (prefixWord ++ tailWord_2772865) baseStart_2772865 baseEnd_2772865 := by
    simpa [prefixWord, tailWord_2772865, baseEnd_2772865] using wordTrace_append hprefix tailTrace_2772865
  have hstable : (prefixWord ++ tailWord_2772865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772865).length < 2 ^ (prefixWord ++ tailWord_2772865).sum := by decide
  have hdescent : baseEnd_2772865 < baseStart_2772865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772953 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 5]
def baseStart_2772953 : Nat := 118140960795 + 2772953 * 2 ^ 59
def prefixEnd_2772953 : Nat := 4983230072969 + 3 ^ 40 * 2772953 * 2
def baseEnd_2772953 : Nat := 316412826961554342741095

theorem tailTrace_2772953 : CollatzResearch.WordTrace tailWord_2772953 prefixEnd_2772953 316412826961554342741095 := by
  unfold tailWord_2772953
  simp only [CollatzResearch.WordTrace]
  refine ⟨101137904723072338513667513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67425269815381559009111675 101137904723072338513667513)
  ·
    refine ⟨75853428542304253885250635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101137904723072338513667513 75853428542304253885250635)
    ·
      refine ⟨113780142813456380827875953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75853428542304253885250635 113780142813456380827875953)
      ·
        refine ⟨85335107110092285620906965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113780142813456380827875953 85335107110092285620906965)
        ·
          refine ⟨2000041572892787944240007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 85335107110092285620906965 2000041572892787944240007)
          ·
            refine ⟨3000062359339181916360011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000041572892787944240007 3000062359339181916360011)
            ·
              refine ⟨4500093539008772874540017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000062359339181916360011 4500093539008772874540017)
              ·
                refine ⟨3375070154256579655905013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500093539008772874540017 3375070154256579655905013)
                ·
                  refine ⟨316412826961554342741095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375070154256579655905013 316412826961554342741095)
                  ·
                    rfl

theorem cell22_2772953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 5].length) (baseStart_2772953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772953 prefixEnd_2772953 := by exact prefixLift 2772953
  have htrace : WordTrace (prefixWord ++ tailWord_2772953) baseStart_2772953 baseEnd_2772953 := by
    simpa [prefixWord, tailWord_2772953, baseEnd_2772953] using wordTrace_append hprefix tailTrace_2772953
  have hstable : (prefixWord ++ tailWord_2772953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772953).length < 2 ^ (prefixWord ++ tailWord_2772953).sum := by decide
  have hdescent : baseEnd_2772953 < baseStart_2772953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2772964 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_2772964 : Nat := 118140960795 + 2772964 * 2 ^ 59
def prefixEnd_2772964 : Nat := 4983230072969 + 3 ^ 40 * 2772964 * 2
def baseEnd_2772964 : Nat := 316414082136487555399417

theorem tailTrace_2772964 : CollatzResearch.WordTrace tailWord_2772964 prefixEnd_2772964 316414082136487555399417 := by
  unfold tailWord_2772964
  simp only [CollatzResearch.WordTrace]
  refine ⟨50569152963016243696158973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67425537284021658261545297 50569152963016243696158973)
  ·
    refine ⟨18963432361131091386059615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50569152963016243696158973 18963432361131091386059615)
    ·
      refine ⟨28445148541696637079089423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18963432361131091386059615 28445148541696637079089423)
      ·
        refine ⟨42667722812544955618634135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28445148541696637079089423 42667722812544955618634135)
        ·
          refine ⟨64001584218817433427951203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42667722812544955618634135 64001584218817433427951203)
          ·
            refine ⟨96002376328226150141926805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64001584218817433427951203 96002376328226150141926805)
            ·
              refine ⟨4500111390385600787902819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96002376328226150141926805 4500111390385600787902819)
              ·
                refine ⟨6750167085578401181854229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500111390385600787902819 6750167085578401181854229)
                ·
                  refine ⟨316414082136487555399417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6750167085578401181854229 316414082136487555399417)
                  ·
                    rfl

theorem cell22_2772964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_2772964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2772964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2772964 prefixEnd_2772964 := by exact prefixLift 2772964
  have htrace : WordTrace (prefixWord ++ tailWord_2772964) baseStart_2772964 baseEnd_2772964 := by
    simpa [prefixWord, tailWord_2772964, baseEnd_2772964] using wordTrace_append hprefix tailTrace_2772964
  have hstable : (prefixWord ++ tailWord_2772964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2772964).length < 2 ^ (prefixWord ++ tailWord_2772964).sum := by decide
  have hdescent : baseEnd_2772964 < baseStart_2772964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2772964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773015 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 4]
def baseStart_2773015 : Nat := 118140960795 + 2773015 * 2 ^ 59
def prefixEnd_2773015 : Nat := 4983230072969 + 3 ^ 40 * 2773015 * 2
def baseEnd_2773015 : Nat := 316419901583905177724365

theorem tailTrace_2773015 : CollatzResearch.WordTrace tailWord_2773015 prefixEnd_2773015 316419901583905177724365 := by
  unfold tailWord_2773015
  simp only [CollatzResearch.WordTrace]
  refine ⟨101140166048847723102424499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67426777365898482068282999 101140166048847723102424499)
  ·
    refine ⟨151710249073271584653636749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101140166048847723102424499 151710249073271584653636749)
    ·
      refine ⟨56891343402476844245113781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151710249073271584653636749 56891343402476844245113781)
      ·
        refine ⟨5333563443982204147979417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56891343402476844245113781 5333563443982204147979417)
        ·
          refine ⟨4000172582986653110984563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5333563443982204147979417 4000172582986653110984563)
          ·
            refine ⟨6000258874479979666476845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000172582986653110984563 6000258874479979666476845)
            ·
              refine ⟨2250097077929992374928817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6000258874479979666476845 2250097077929992374928817)
              ·
                refine ⟨1687572808447494281196613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250097077929992374928817 1687572808447494281196613)
                ·
                  refine ⟨316419901583905177724365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1687572808447494281196613 316419901583905177724365)
                  ·
                    rfl

theorem cell22_2773015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 4].length) (baseStart_2773015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773015 prefixEnd_2773015 := by exact prefixLift 2773015
  have htrace : WordTrace (prefixWord ++ tailWord_2773015) baseStart_2773015 baseEnd_2773015 := by
    simpa [prefixWord, tailWord_2773015, baseEnd_2773015] using wordTrace_append hprefix tailTrace_2773015
  have hstable : (prefixWord ++ tailWord_2773015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773015).length < 2 ^ (prefixWord ++ tailWord_2773015).sum := by decide
  have hdescent : baseEnd_2773015 < baseStart_2773015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773101 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2773101 : Nat := 118140960795 + 2773101 * 2 ^ 59
def prefixEnd_2773101 : Nat := 4983230072969 + 3 ^ 40 * 2773101 * 2
def baseEnd_2773101 : Nat := 949289144309239975522831

theorem tailTrace_2773101 : CollatzResearch.WordTrace tailWord_2773101 prefixEnd_2773101 949289144309239975522831 := by
  unfold tailWord_2773101
  simp only [CollatzResearch.WordTrace]
  refine ⟨101143302726536159790055157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67428868484357439860036771 101143302726536159790055157)
  ·
    refine ⟨9482184630612764980317671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101143302726536159790055157 9482184630612764980317671)
    ·
      refine ⟨14223276945919147470476507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9482184630612764980317671 14223276945919147470476507)
      ·
        refine ⟨21334915418878721205714761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14223276945919147470476507 21334915418878721205714761)
        ·
          refine ⟨16001186564159040904286071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21334915418878721205714761 16001186564159040904286071)
          ·
            refine ⟨24001779846238561356429107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16001186564159040904286071 24001779846238561356429107)
            ·
              refine ⟨36002669769357842034643661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24001779846238561356429107 36002669769357842034643661)
              ·
                refine ⟨13501001163509190762991373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36002669769357842034643661 13501001163509190762991373)
                ·
                  refine ⟨5062875436315946536121765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13501001163509190762991373 5062875436315946536121765)
                  ·
                    refine ⟨949289144309239975522831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5062875436315946536121765 949289144309239975522831)
                    ·
                      rfl

theorem cell22_2773101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2773101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773101 prefixEnd_2773101 := by exact prefixLift 2773101
  have htrace : WordTrace (prefixWord ++ tailWord_2773101) baseStart_2773101 baseEnd_2773101 := by
    simpa [prefixWord, tailWord_2773101, baseEnd_2773101] using wordTrace_append hprefix tailTrace_2773101
  have hstable : (prefixWord ++ tailWord_2773101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773101).length < 2 ^ (prefixWord ++ tailWord_2773101).sum := by decide
  have hdescent : baseEnd_2773101 < baseStart_2773101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773244 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_2773244 : Nat := 118140960795 + 2773244 * 2 ^ 59
def prefixEnd_2773244 : Nat := 4983230072969 + 3 ^ 40 * 2773244 * 2
def baseEnd_2773244 : Nat := 949338096131635269197393

theorem tailTrace_2773244 : CollatzResearch.WordTrace tailWord_2773244 prefixEnd_2773244 949338096131635269197393 := by
  unfold tailWord_2773244
  simp only [CollatzResearch.WordTrace]
  refine ⟨50574259182509047606255393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67432345576678730141673857 50574259182509047606255393)
  ·
    refine ⟨37930694386881785704691545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50574259182509047606255393 37930694386881785704691545)
    ·
      refine ⟨28448020790161339278518659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37930694386881785704691545 28448020790161339278518659)
      ·
        refine ⟨42672031185242008917777989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28448020790161339278518659 42672031185242008917777989)
        ·
          refine ⟨8001005847232876672083373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42672031185242008917777989 8001005847232876672083373)
          ·
            refine ⟨3000377192712328752031265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8001005847232876672083373 3000377192712328752031265)
            ·
              refine ⟨2250282894534246564023449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000377192712328752031265 2250282894534246564023449)
              ·
                refine ⟨1687712170900684923017587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250282894534246564023449 1687712170900684923017587)
                ·
                  refine ⟨2531568256351027384526381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1687712170900684923017587 2531568256351027384526381)
                  ·
                    refine ⟨949338096131635269197393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531568256351027384526381 949338096131635269197393)
                    ·
                      rfl

theorem cell22_2773244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_2773244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773244 prefixEnd_2773244 := by exact prefixLift 2773244
  have htrace : WordTrace (prefixWord ++ tailWord_2773244) baseStart_2773244 baseEnd_2773244 := by
    simpa [prefixWord, tailWord_2773244, baseEnd_2773244] using wordTrace_append hprefix tailTrace_2773244
  have hstable : (prefixWord ++ tailWord_2773244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773244).length < 2 ^ (prefixWord ++ tailWord_2773244).sum := by decide
  have hdescent : baseEnd_2773244 < baseStart_2773244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773251 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 6]
def baseStart_2773251 : Nat := 118140960795 + 2773251 * 2 ^ 59
def prefixEnd_2773251 : Nat := 4983230072969 + 3 ^ 40 * 2773251 * 2
def baseEnd_2773251 : Nat := 316446830791563194757457

theorem tailTrace_2773251 : CollatzResearch.WordTrace tailWord_2773251 prefixEnd_2773251 316446830791563194757457 := by
  unfold tailWord_2773251
  simp only [CollatzResearch.WordTrace]
  refine ⟨101148773675992735408015607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67432515783995156938677071 101148773675992735408015607)
  ·
    refine ⟨151723160513989103112023411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101148773675992735408015607 151723160513989103112023411)
    ·
      refine ⟨227584740770983654668035117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151723160513989103112023411 227584740770983654668035117)
      ·
        refine ⟨85344277789118870500513169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227584740770983654668035117 85344277789118870500513169)
        ·
          refine ⟨64008208341839152875384877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85344277789118870500513169 64008208341839152875384877)
          ·
            refine ⟨24003078128189682328269329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64008208341839152875384877 24003078128189682328269329)
            ·
              refine ⟨18002308596142261746201997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24003078128189682328269329 18002308596142261746201997)
              ·
                refine ⟨6750865723553348154825749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18002308596142261746201997 6750865723553348154825749)
                ·
                  refine ⟨316446830791563194757457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6750865723553348154825749 316446830791563194757457)
                  ·
                    rfl

theorem cell22_2773251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 6].length) (baseStart_2773251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773251 prefixEnd_2773251 := by exact prefixLift 2773251
  have htrace : WordTrace (prefixWord ++ tailWord_2773251) baseStart_2773251 baseEnd_2773251 := by
    simpa [prefixWord, tailWord_2773251, baseEnd_2773251] using wordTrace_append hprefix tailTrace_2773251
  have hstable : (prefixWord ++ tailWord_2773251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773251).length < 2 ^ (prefixWord ++ tailWord_2773251).sum := by decide
  have hdescent : baseEnd_2773251 < baseStart_2773251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773255 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 2, 5]
def baseStart_2773255 : Nat := 118140960795 + 2773255 * 2 ^ 59
def prefixEnd_2773255 : Nat := 4983230072969 + 3 ^ 40 * 2773255 * 2
def baseEnd_2773255 : Nat := 949341861656434907172359

theorem tailTrace_2773255 : CollatzResearch.WordTrace tailWord_2773255 prefixEnd_2773255 949341861656434907172359 := by
  unfold tailWord_2773255
  simp only [CollatzResearch.WordTrace]
  refine ⟨101148919567978244091161219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67432613045318829394107479 101148919567978244091161219)
  ·
    refine ⟨151723379351967366136741829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101148919567978244091161219 151723379351967366136741829)
    ·
      refine ⟨28448133628493881150639093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151723379351967366136741829 28448133628493881150639093)
      ·
        refine ⟨2667012527671301357872415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28448133628493881150639093 2667012527671301357872415)
        ·
          refine ⟨4000518791506952036808623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667012527671301357872415 4000518791506952036808623)
          ·
            refine ⟨6000778187260428055212935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000518791506952036808623 6000778187260428055212935)
            ·
              refine ⟨9001167280890642082819403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000778187260428055212935 9001167280890642082819403)
              ·
                refine ⟨13501750921335963124229105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9001167280890642082819403 13501750921335963124229105)
                ·
                  refine ⟨10126313191001972343171829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13501750921335963124229105 10126313191001972343171829)
                  ·
                    refine ⟨949341861656434907172359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10126313191001972343171829 949341861656434907172359)
                    ·
                      rfl

theorem cell22_2773255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_2773255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773255 prefixEnd_2773255 := by exact prefixLift 2773255
  have htrace : WordTrace (prefixWord ++ tailWord_2773255) baseStart_2773255 baseEnd_2773255 := by
    simpa [prefixWord, tailWord_2773255, baseEnd_2773255] using wordTrace_append hprefix tailTrace_2773255
  have hstable : (prefixWord ++ tailWord_2773255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773255).length < 2 ^ (prefixWord ++ tailWord_2773255).sum := by decide
  have hdescent : baseEnd_2773255 < baseStart_2773255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773283 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 4, 3]
def baseStart_2773283 : Nat := 118140960795 + 2773283 * 2 ^ 59
def prefixEnd_2773283 : Nat := 4983230072969 + 3 ^ 40 * 2773283 * 2
def baseEnd_2773283 : Nat := 949351446628652167472273

theorem tailTrace_2773283 : CollatzResearch.WordTrace tailWord_2773283 prefixEnd_2773283 949351446628652167472273 := by
  unfold tailWord_2773283
  simp only [CollatzResearch.WordTrace]
  refine ⟨101149940811876804873180503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67433293874584536582120335 101149940811876804873180503)
  ·
    refine ⟨151724911217815207309770755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101149940811876804873180503 151724911217815207309770755)
    ·
      refine ⟨227587366826722810964656133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151724911217815207309770755 227587366826722810964656133)
      ·
        refine ⟨42672631280010527055873025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227587366826722810964656133 42672631280010527055873025)
        ·
          refine ⟨32004473460007895291904769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42672631280010527055873025 32004473460007895291904769)
          ·
            refine ⟨24003355095005921468928577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32004473460007895291904769 24003355095005921468928577)
            ·
              refine ⟨18002516321254441101696433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24003355095005921468928577 18002516321254441101696433)
              ·
                refine ⟨13501887240940830826272325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18002516321254441101696433 13501887240940830826272325)
                ·
                  refine ⟨2531603857676405779926061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13501887240940830826272325 2531603857676405779926061)
                  ·
                    refine ⟨949351446628652167472273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531603857676405779926061 949351446628652167472273)
                    ·
                      rfl

theorem cell22_2773283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 3].length) (baseStart_2773283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773283 prefixEnd_2773283 := by exact prefixLift 2773283
  have htrace : WordTrace (prefixWord ++ tailWord_2773283) baseStart_2773283 baseEnd_2773283 := by
    simpa [prefixWord, tailWord_2773283, baseEnd_2773283] using wordTrace_append hprefix tailTrace_2773283
  have hstable : (prefixWord ++ tailWord_2773283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773283).length < 2 ^ (prefixWord ++ tailWord_2773283).sum := by decide
  have hdescent : baseEnd_2773283 < baseStart_2773283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773362 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2773362 : Nat := 118140960795 + 2773362 * 2 ^ 59
def prefixEnd_2773362 : Nat := 4983230072969 + 3 ^ 40 * 2773362 * 2
def baseEnd_2773362 : Nat := 949378489943122294747031

theorem tailTrace_2773362 : CollatzResearch.WordTrace tailWord_2773362 prefixEnd_2773362 949378489943122294747031 := by
  unfold tailWord_2773362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25288205544647650341326585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67435214785727067576870893 25288205544647650341326585)
  ·
    refine ⟨18966154158485737755994939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25288205544647650341326585 18966154158485737755994939)
    ·
      refine ⟨28449231237728606633992409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18966154158485737755994939 28449231237728606633992409)
      ·
        refine ⟨21336923428296454975494307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28449231237728606633992409 21336923428296454975494307)
        ·
          refine ⟨32005385142444682463241461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21336923428296454975494307 32005385142444682463241461)
          ·
            refine ⟨3000504857104188980928887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32005385142444682463241461 3000504857104188980928887)
            ·
              refine ⟨4500757285656283471393331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000504857104188980928887 4500757285656283471393331)
              ·
                refine ⟨6751135928484425207089997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500757285656283471393331 6751135928484425207089997)
                ·
                  refine ⟨2531675973181659452658749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6751135928484425207089997 2531675973181659452658749)
                  ·
                    refine ⟨949378489943122294747031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2531675973181659452658749 949378489943122294747031)
                    ·
                      rfl

theorem cell22_2773362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2773362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773362 prefixEnd_2773362 := by exact prefixLift 2773362
  have htrace : WordTrace (prefixWord ++ tailWord_2773362) baseStart_2773362 baseEnd_2773362 := by
    simpa [prefixWord, tailWord_2773362, baseEnd_2773362] using wordTrace_append hprefix tailTrace_2773362
  have hstable : (prefixWord ++ tailWord_2773362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773362).length < 2 ^ (prefixWord ++ tailWord_2773362).sum := by decide
  have hdescent : baseEnd_2773362 < baseStart_2773362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773544 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_2773544 : Nat := 118140960795 + 2773544 * 2 ^ 59
def prefixEnd_2773544 : Nat := 4983230072969 + 3 ^ 40 * 2773544 * 2
def baseEnd_2773544 : Nat := 316480264087511495565491

theorem tailTrace_2773544 : CollatzResearch.WordTrace tailWord_2773544 prefixEnd_2773544 316480264087511495565491 := by
  unfold tailWord_2773544
  simp only [CollatzResearch.WordTrace]
  refine ⟨50579730131965623224215843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67439640175954164298954457 50579730131965623224215843)
  ·
    refine ⟨75869595197948434836323765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50579730131965623224215843 75869595197948434836323765)
    ·
      refine ⟨7112774549807665765905353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75869595197948434836323765 7112774549807665765905353)
      ·
        refine ⟨5334580912355749324429015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7112774549807665765905353 5334580912355749324429015)
        ·
          refine ⟨8001871368533623986643523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5334580912355749324429015 8001871368533623986643523)
          ·
            refine ⟨12002807052800435979965285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8001871368533623986643523 12002807052800435979965285)
            ·
              refine ⟨2250526322400081746243491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12002807052800435979965285 2250526322400081746243491)
              ·
                refine ⟨3375789483600122619365237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250526322400081746243491 3375789483600122619365237)
                ·
                  refine ⟨316480264087511495565491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3375789483600122619365237 316480264087511495565491)
                  ·
                    rfl

theorem cell22_2773544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_2773544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773544 prefixEnd_2773544 := by exact prefixLift 2773544
  have htrace : WordTrace (prefixWord ++ tailWord_2773544) baseStart_2773544 baseEnd_2773544 := by
    simpa [prefixWord, tailWord_2773544, baseEnd_2773544] using wordTrace_append hprefix tailTrace_2773544
  have hstable : (prefixWord ++ tailWord_2773544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773544).length < 2 ^ (prefixWord ++ tailWord_2773544).sum := by decide
  have hdescent : baseEnd_2773544 < baseStart_2773544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773589 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 4]
def baseStart_2773589 : Nat := 118140960795 + 2773589 * 2 ^ 59
def prefixEnd_2773589 : Nat := 4983230072969 + 3 ^ 40 * 2773589 * 2
def baseEnd_2773589 : Nat := 316485398894056456440445

theorem tailTrace_2773589 : CollatzResearch.WordTrace tailWord_2773589 prefixEnd_2773589 316485398894056456440445 := by
  unfold tailWord_2773589
  simp only [CollatzResearch.WordTrace]
  refine ⟨101161101548768219133819821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67440734365845479422546547 101161101548768219133819821)
  ·
    refine ⟨37935413080788082175182433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101161101548768219133819821 37935413080788082175182433)
    ·
      refine ⟨28451559810591061631386825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37935413080788082175182433 28451559810591061631386825)
      ·
        refine ⟨21338669857943296223540119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28451559810591061631386825 21338669857943296223540119)
        ·
          refine ⟨32008004786914944335310179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21338669857943296223540119 32008004786914944335310179)
          ·
            refine ⟨48012007180372416502965269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32008004786914944335310179 48012007180372416502965269)
            ·
              refine ⟨2250562836579957023576497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48012007180372416502965269 2250562836579957023576497)
              ·
                refine ⟨1687922127434967767682373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250562836579957023576497 1687922127434967767682373)
                ·
                  refine ⟨316485398894056456440445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1687922127434967767682373 316485398894056456440445)
                  ·
                    rfl

theorem cell22_2773589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_2773589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773589 prefixEnd_2773589 := by exact prefixLift 2773589
  have htrace : WordTrace (prefixWord ++ tailWord_2773589) baseStart_2773589 baseEnd_2773589 := by
    simpa [prefixWord, tailWord_2773589, baseEnd_2773589] using wordTrace_append hprefix tailTrace_2773589
  have hstable : (prefixWord ++ tailWord_2773589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773589).length < 2 ^ (prefixWord ++ tailWord_2773589).sum := by decide
  have hdescent : baseEnd_2773589 < baseStart_2773589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773600 : List Nat := [2, 1, 1, 3, 2, 1, 5, 7]
def baseStart_2773600 : Nat := 118140960795 + 2773600 * 2 ^ 59
def prefixEnd_2773600 : Nat := 4983230072969 + 3 ^ 40 * 2773600 * 2
def baseEnd_2773600 : Nat := 105495551356329889699589

theorem tailTrace_2773600 : CollatzResearch.WordTrace tailWord_2773600 prefixEnd_2773600 105495551356329889699589 := by
  unfold tailWord_2773600
  simp only [CollatzResearch.WordTrace]
  refine ⟨50580751375864184006235127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67441001834485578674980169 50580751375864184006235127)
  ·
    refine ⟨75871127063796276009352691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50580751375864184006235127 75871127063796276009352691)
    ·
      refine ⟨113806690595694414014029037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75871127063796276009352691 113806690595694414014029037)
      ·
        refine ⟨42677508973385405255260889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113806690595694414014029037 42677508973385405255260889)
        ·
          refine ⟨32008131730039053941445667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42677508973385405255260889 32008131730039053941445667)
          ·
            refine ⟨48012197595058580912168501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32008131730039053941445667 48012197595058580912168501)
            ·
              refine ⟨4501143524536741960515797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48012197595058580912168501 4501143524536741960515797)
              ·
                refine ⟨105495551356329889699589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4501143524536741960515797 105495551356329889699589)
                ·
                  rfl

theorem cell22_2773600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_2773600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773600 prefixEnd_2773600 := by exact prefixLift 2773600
  have htrace : WordTrace (prefixWord ++ tailWord_2773600) baseStart_2773600 baseEnd_2773600 := by
    simpa [prefixWord, tailWord_2773600, baseEnd_2773600] using wordTrace_append hprefix tailTrace_2773600
  have hstable : (prefixWord ++ tailWord_2773600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773600).length < 2 ^ (prefixWord ++ tailWord_2773600).sum := by decide
  have hdescent : baseEnd_2773600 < baseStart_2773600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773722 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_2773722 : Nat := 118140960795 + 2773722 * 2 ^ 59
def prefixEnd_2773722 : Nat := 4983230072969 + 3 ^ 40 * 2773722 * 2
def baseEnd_2773722 : Nat := 949501725300201355745927

theorem tailTrace_2773722 : CollatzResearch.WordTrace tailWord_2773722 prefixEnd_2773722 949501725300201355745927 := by
  unfold tailWord_2773722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25291488114321595712102855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67443968304857588565607613 25291488114321595712102855)
  ·
    refine ⟨37937232171482393568154283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25291488114321595712102855 37937232171482393568154283)
    ·
      refine ⟨56905848257223590352231425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37937232171482393568154283 56905848257223590352231425)
      ·
        refine ⟨42679386192917692764173569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56905848257223590352231425 42679386192917692764173569)
        ·
          refine ⟨32009539644688269573130177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42679386192917692764173569 32009539644688269573130177)
          ·
            refine ⟨24007154733516202179847633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32009539644688269573130177 24007154733516202179847633)
            ·
              refine ⟨18005366050137151634885725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24007154733516202179847633 18005366050137151634885725)
              ·
                refine ⟨6752012268801431863082147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18005366050137151634885725 6752012268801431863082147)
                ·
                  refine ⟨10128018403202147794623221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752012268801431863082147 10128018403202147794623221)
                  ·
                    refine ⟨949501725300201355745927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10128018403202147794623221 949501725300201355745927)
                    ·
                      rfl

theorem cell22_2773722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_2773722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773722 prefixEnd_2773722 := by exact prefixLift 2773722
  have htrace : WordTrace (prefixWord ++ tailWord_2773722) baseStart_2773722 baseEnd_2773722 := by
    simpa [prefixWord, tailWord_2773722, baseEnd_2773722] using wordTrace_append hprefix tailTrace_2773722
  have hstable : (prefixWord ++ tailWord_2773722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773722).length < 2 ^ (prefixWord ++ tailWord_2773722).sum := by decide
  have hdescent : baseEnd_2773722 < baseStart_2773722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773737 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 2, 4]
def baseStart_2773737 : Nat := 118140960795 + 2773737 * 2 ^ 59
def prefixEnd_2773737 : Nat := 4983230072969 + 3 ^ 40 * 2773737 * 2
def baseEnd_2773737 : Nat := 949506860106746316620881

theorem tailTrace_2773737 : CollatzResearch.WordTrace tailWord_2773737 prefixEnd_2773737 949506860106746316620881 := by
  unfold tailWord_2773737
  simp only [CollatzResearch.WordTrace]
  refine ⟨101166499552232040410207465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67444333034821360273471643 101166499552232040410207465)
  ·
    refine ⟨75874874664174030307655599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101166499552232040410207465 75874874664174030307655599)
    ·
      refine ⟨113812311996261045461483399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75874874664174030307655599 113812311996261045461483399)
      ·
        refine ⟨170718467994391568192225099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113812311996261045461483399 170718467994391568192225099)
        ·
          refine ⟨256077701991587352288337649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170718467994391568192225099 256077701991587352288337649)
          ·
            refine ⟨192058276493690514216253237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256077701991587352288337649 192058276493690514216253237)
            ·
              refine ⟨18005463421283485707773741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192058276493690514216253237 18005463421283485707773741)
              ·
                refine ⟨6752048782981307140415153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18005463421283485707773741 6752048782981307140415153)
                ·
                  refine ⟨5064036587235980355311365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6752048782981307140415153 5064036587235980355311365)
                  ·
                    refine ⟨949506860106746316620881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5064036587235980355311365 949506860106746316620881)
                    ·
                      rfl

theorem cell22_2773737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 4].length) (baseStart_2773737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773737 prefixEnd_2773737 := by exact prefixLift 2773737
  have htrace : WordTrace (prefixWord ++ tailWord_2773737) baseStart_2773737 baseEnd_2773737 := by
    simpa [prefixWord, tailWord_2773737, baseEnd_2773737] using wordTrace_append hprefix tailTrace_2773737
  have hstable : (prefixWord ++ tailWord_2773737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773737).length < 2 ^ (prefixWord ++ tailWord_2773737).sum := by decide
  have hdescent : baseEnd_2773737 < baseStart_2773737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773756 : List Nat := [2, 2, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_2773756 : Nat := 118140960795 + 2773756 * 2 ^ 59
def prefixEnd_2773756 : Nat := 4983230072969 + 3 ^ 40 * 2773756 * 2
def baseEnd_2773756 : Nat := 949513364195036600395823

theorem tailTrace_2773756 : CollatzResearch.WordTrace tailWord_2773756 prefixEnd_2773756 949513364195036600395823 := by
  unfold tailWord_2773756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50583596269581603327574561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67444795026108804436766081 50583596269581603327574561)
  ·
    refine ⟨37937697202186202495680921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50583596269581603327574561 37937697202186202495680921)
    ·
      refine ⟨28453272901639651871760691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37937697202186202495680921 28453272901639651871760691)
      ·
        refine ⟨42679909352459477807641037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28453272901639651871760691 42679909352459477807641037)
        ·
          refine ⟨16004966007172304177865389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42679909352459477807641037 16004966007172304177865389)
          ·
            refine ⟨6001862252689614066699521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16004966007172304177865389 6001862252689614066699521)
            ·
              refine ⟨4501396689517210550024641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001862252689614066699521 4501396689517210550024641)
              ·
                refine ⟨3376047517137907912518481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501396689517210550024641 3376047517137907912518481)
                ·
                  refine ⟨2532035637853430934388861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376047517137907912518481 2532035637853430934388861)
                  ·
                    refine ⟨949513364195036600395823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532035637853430934388861 949513364195036600395823)
                    ·
                      rfl

theorem cell22_2773756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_2773756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773756 prefixEnd_2773756 := by exact prefixLift 2773756
  have htrace : WordTrace (prefixWord ++ tailWord_2773756) baseStart_2773756 baseEnd_2773756 := by
    simpa [prefixWord, tailWord_2773756, baseEnd_2773756] using wordTrace_append hprefix tailTrace_2773756
  have hstable : (prefixWord ++ tailWord_2773756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773756).length < 2 ^ (prefixWord ++ tailWord_2773756).sum := by decide
  have hdescent : baseEnd_2773756 < baseStart_2773756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773758 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_2773758 : Nat := 118140960795 + 2773758 * 2 ^ 59
def prefixEnd_2773758 : Nat := 4983230072969 + 3 ^ 40 * 2773758 * 2
def baseEnd_2773758 : Nat := 316504682945303087281939

theorem tailTrace_2773758 : CollatzResearch.WordTrace tailWord_2773758 prefixEnd_2773758 316504682945303087281939 := by
  unfold tailWord_2773758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12645908185644495124590241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67444843656770640664481285 12645908185644495124590241)
  ·
    refine ⟨9484431139233371343442681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12645908185644495124590241 9484431139233371343442681)
    ·
      refine ⟨7113323354425028507582011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9484431139233371343442681 7113323354425028507582011)
      ·
        refine ⟨10669985031637542761373017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113323354425028507582011 10669985031637542761373017)
        ·
          refine ⟨8002488773728157071029763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10669985031637542761373017 8002488773728157071029763)
          ·
            refine ⟨12003733160592235606544645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8002488773728157071029763 12003733160592235606544645)
            ·
              refine ⟨2250699967611044176227121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12003733160592235606544645 2250699967611044176227121)
              ·
                refine ⟨1688024975708283132170341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250699967611044176227121 1688024975708283132170341)
                ·
                  refine ⟨316504682945303087281939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688024975708283132170341 316504682945303087281939)
                  ·
                    rfl

theorem cell22_2773758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_2773758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773758 prefixEnd_2773758 := by exact prefixLift 2773758
  have htrace : WordTrace (prefixWord ++ tailWord_2773758) baseStart_2773758 baseEnd_2773758 := by
    simpa [prefixWord, tailWord_2773758, baseEnd_2773758] using wordTrace_append hprefix tailTrace_2773758
  have hstable : (prefixWord ++ tailWord_2773758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773758).length < 2 ^ (prefixWord ++ tailWord_2773758).sum := by decide
  have hdescent : baseEnd_2773758 < baseStart_2773758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773797 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 7]
def baseStart_2773797 : Nat := 118140960795 + 2773797 * 2 ^ 59
def prefixEnd_2773797 : Nat := 4983230072969 + 3 ^ 40 * 2773797 * 2
def baseEnd_2773797 : Nat := 316509133110975386706899

theorem tailTrace_2773797 : CollatzResearch.WordTrace tailWord_2773797 prefixEnd_2773797 316509133110975386706899 := by
  unfold tailWord_2773797
  simp only [CollatzResearch.WordTrace]
  refine ⟨101168687932014670657391645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67445791954676447104927763 101168687932014670657391645)
  ·
    refine ⟨37938257974505501496521867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101168687932014670657391645 37938257974505501496521867)
    ·
      refine ⟨56907386961758252244782801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37938257974505501496521867 56907386961758252244782801)
      ·
        refine ⟨42680540221318689183587101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56907386961758252244782801 42680540221318689183587101)
        ·
          refine ⟨16005202582994508443845163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42680540221318689183587101 16005202582994508443845163)
          ·
            refine ⟨24007803874491762665767745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005202582994508443845163 24007803874491762665767745)
            ·
              refine ⟨18005852905868821999325809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24007803874491762665767745 18005852905868821999325809)
              ·
                refine ⟨13504389679401616499494357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18005852905868821999325809 13504389679401616499494357)
                ·
                  refine ⟨316509133110975386706899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13504389679401616499494357 316509133110975386706899)
                  ·
                    rfl

theorem cell22_2773797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_2773797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773797 prefixEnd_2773797 := by exact prefixLift 2773797
  have htrace : WordTrace (prefixWord ++ tailWord_2773797) baseStart_2773797 baseEnd_2773797 := by
    simpa [prefixWord, tailWord_2773797, baseEnd_2773797] using wordTrace_append hprefix tailTrace_2773797
  have hstable : (prefixWord ++ tailWord_2773797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773797).length < 2 ^ (prefixWord ++ tailWord_2773797).sum := by decide
  have hdescent : baseEnd_2773797 < baseStart_2773797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773887 : List Nat := [1, 1, 2, 2, 1, 1, 5, 9]
def baseStart_2773887 : Nat := 118140960795 + 2773887 * 2 ^ 59
def prefixEnd_2773887 : Nat := 4983230072969 + 3 ^ 40 * 2773887 * 2
def baseEnd_2773887 : Nat := 105506467574688436152269

theorem tailTrace_2773887 : CollatzResearch.WordTrace tailWord_2773887 prefixEnd_2773887 105506467574688436152269 := by
  unfold tailWord_2773887
  simp only [CollatzResearch.WordTrace]
  refine ⟨101171970501688616028167915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67447980334459077352111943 101171970501688616028167915)
  ·
    refine ⟨151757955752532924042251873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101171970501688616028167915 151757955752532924042251873)
    ·
      refine ⟨113818466814399693031688905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151757955752532924042251873 113818466814399693031688905)
      ·
        refine ⟨85363850110799769773766679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113818466814399693031688905 85363850110799769773766679)
        ·
          refine ⟨128045775166199654660650019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85363850110799769773766679 128045775166199654660650019)
          ·
            refine ⟨192068662749299481990975029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128045775166199654660650019 192068662749299481990975029)
            ·
              refine ⟨18006437132746826436653909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 192068662749299481990975029 18006437132746826436653909)
              ·
                refine ⟨105506467574688436152269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18006437132746826436653909 105506467574688436152269)
                ·
                  rfl

theorem cell22_2773887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 9].length) (baseStart_2773887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773887 prefixEnd_2773887 := by exact prefixLift 2773887
  have htrace : WordTrace (prefixWord ++ tailWord_2773887) baseStart_2773887 baseEnd_2773887 := by
    simpa [prefixWord, tailWord_2773887, baseEnd_2773887] using wordTrace_append hprefix tailTrace_2773887
  have hstable : (prefixWord ++ tailWord_2773887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773887).length < 2 ^ (prefixWord ++ tailWord_2773887).sum := by decide
  have hdescent : baseEnd_2773887 < baseStart_2773887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773891 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 2, 3]
def baseStart_2773891 : Nat := 118140960795 + 2773891 * 2 ^ 59
def prefixEnd_2773891 : Nat := 4983230072969 + 3 ^ 40 * 2773891 * 2
def baseEnd_2773891 : Nat := 949559577453941248270409

theorem tailTrace_2773891 : CollatzResearch.WordTrace tailWord_2773891 prefixEnd_2773891 949559577453941248270409 := by
  unfold tailWord_2773891
  simp only [CollatzResearch.WordTrace]
  refine ⟨101172116393674124711313527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67448077595782749807542351 101172116393674124711313527)
  ·
    refine ⟨151758174590511187066970291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101172116393674124711313527 151758174590511187066970291)
    ·
      refine ⟨227637261885766780600455437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151758174590511187066970291 227637261885766780600455437)
      ·
        refine ⟨85363973207162542725170789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227637261885766780600455437 85363973207162542725170789)
        ·
          refine ⟨16005744976342976760969523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85363973207162542725170789 16005744976342976760969523)
          ·
            refine ⟨24008617464514465141454285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16005744976342976760969523 24008617464514465141454285)
            ·
              refine ⟨9003231549192924428045357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24008617464514465141454285 9003231549192924428045357)
              ·
                refine ⟨3376211830947346660517009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9003231549192924428045357 3376211830947346660517009)
                ·
                  refine ⟨2532158873210509995387757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376211830947346660517009 2532158873210509995387757)
                  ·
                    refine ⟨949559577453941248270409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532158873210509995387757 949559577453941248270409)
                    ·
                      rfl

theorem cell22_2773891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3].length) (baseStart_2773891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773891 prefixEnd_2773891 := by exact prefixLift 2773891
  have htrace : WordTrace (prefixWord ++ tailWord_2773891) baseStart_2773891 baseEnd_2773891 := by
    simpa [prefixWord, tailWord_2773891, baseEnd_2773891] using wordTrace_append hprefix tailTrace_2773891
  have hstable : (prefixWord ++ tailWord_2773891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773891).length < 2 ^ (prefixWord ++ tailWord_2773891).sum := by decide
  have hdescent : baseEnd_2773891 < baseStart_2773891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773927 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 4]
def baseStart_2773927 : Nat := 118140960795 + 2773927 * 2 ^ 59
def prefixEnd_2773927 : Nat := 4983230072969 + 3 ^ 40 * 2773927 * 2
def baseEnd_2773927 : Nat := 316523966996549718123433

theorem tailTrace_2773927 : CollatzResearch.WordTrace tailWord_2773927 prefixEnd_2773927 316523966996549718123433 := by
  unfold tailWord_2773927
  simp only [CollatzResearch.WordTrace]
  refine ⟨101173429421543702859624035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67448952947695801906416023 101173429421543702859624035)
  ·
    refine ⟨151760144132315554289436053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101173429421543702859624035 151760144132315554289436053)
    ·
      refine ⟨7113756756202291607317315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151760144132315554289436053 7113756756202291607317315)
      ·
        refine ⟨10670635134303437410975973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113756756202291607317315 10670635134303437410975973)
        ·
          refine ⟨2000744087681894514557995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10670635134303437410975973 2000744087681894514557995)
          ·
            refine ⟨3001116131522841771836993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000744087681894514557995 3001116131522841771836993)
            ·
              refine ⟨2250837098642131328877745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001116131522841771836993 2250837098642131328877745)
              ·
                refine ⟨1688127823981598496658309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2250837098642131328877745 1688127823981598496658309)
                ·
                  refine ⟨316523966996549718123433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688127823981598496658309 316523966996549718123433)
                  ·
                    rfl

theorem cell22_2773927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 4].length) (baseStart_2773927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773927 prefixEnd_2773927 := by exact prefixLift 2773927
  have htrace : WordTrace (prefixWord ++ tailWord_2773927) baseStart_2773927 baseEnd_2773927 := by
    simpa [prefixWord, tailWord_2773927, baseEnd_2773927] using wordTrace_append hprefix tailTrace_2773927
  have hstable : (prefixWord ++ tailWord_2773927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773927).length < 2 ^ (prefixWord ++ tailWord_2773927).sum := by decide
  have hdescent : baseEnd_2773927 < baseStart_2773927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773942 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2773942 : Nat := 118140960795 + 2773942 * 2 ^ 59
def prefixEnd_2773942 : Nat := 4983230072969 + 3 ^ 40 * 2773942 * 2
def baseEnd_2773942 : Nat := 949577035796194115245253

theorem tailTrace_2773942 : CollatzResearch.WordTrace tailWord_2773942 prefixEnd_2773942 949577035796194115245253 := by
  unfold tailWord_2773942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323373532280585026338755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67449317677659573614280053 6323373532280585026338755)
  ·
    refine ⟨9485060298420877539508133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323373532280585026338755 9485060298420877539508133)
    ·
      refine ⟨1778448805953914538657775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9485060298420877539508133 1778448805953914538657775)
      ·
        refine ⟨2667673208930871807986663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778448805953914538657775 2667673208930871807986663)
        ·
          refine ⟨4001509813396307711979995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2667673208930871807986663 4001509813396307711979995)
          ·
            refine ⟨6002264720094461567969993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001509813396307711979995 6002264720094461567969993)
            ·
              refine ⟨4501698540070846175977495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6002264720094461567969993 4501698540070846175977495)
              ·
                refine ⟨6752547810106269263966243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501698540070846175977495 6752547810106269263966243)
                ·
                  refine ⟨10128821715159403895949365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6752547810106269263966243 10128821715159403895949365)
                  ·
                    refine ⟨949577035796194115245253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10128821715159403895949365 949577035796194115245253)
                    ·
                      rfl

theorem cell22_2773942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2773942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773942 prefixEnd_2773942 := by exact prefixLift 2773942
  have htrace : WordTrace (prefixWord ++ tailWord_2773942) baseStart_2773942 baseEnd_2773942 := by
    simpa [prefixWord, tailWord_2773942, baseEnd_2773942] using wordTrace_append hprefix tailTrace_2773942
  have hstable : (prefixWord ++ tailWord_2773942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773942).length < 2 ^ (prefixWord ++ tailWord_2773942).sum := by decide
  have hdescent : baseEnd_2773942 < baseStart_2773942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773964 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_2773964 : Nat := 118140960795 + 2773964 * 2 ^ 59
def prefixEnd_2773964 : Nat := 4983230072969 + 3 ^ 40 * 2773964 * 2
def baseEnd_2773964 : Nat := 949584566845793391195185

theorem tailTrace_2773964 : CollatzResearch.WordTrace tailWord_2773964 prefixEnd_2773964 949584566845793391195185 := by
  unfold tailWord_2773964
  simp only [CollatzResearch.WordTrace]
  refine ⟨50587389461204829089360473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67449852614939772119147297 50587389461204829089360473)
  ·
    refine ⟨37940542095903621817020355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50587389461204829089360473 37940542095903621817020355)
    ·
      refine ⟨56910813143855432725530533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37940542095903621817020355 56910813143855432725530533)
      ·
        refine ⟨10670777464472893636036975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56910813143855432725530533 10670777464472893636036975)
        ·
          refine ⟨16006166196709340454055463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10670777464472893636036975 16006166196709340454055463)
          ·
            refine ⟨24009249295064010681083195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16006166196709340454055463 24009249295064010681083195)
            ·
              refine ⟨36013873942596016021624793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24009249295064010681083195 36013873942596016021624793)
              ·
                refine ⟨27010405456947012016218595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36013873942596016021624793 27010405456947012016218595)
                ·
                  refine ⟨40515608185420518024327893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27010405456947012016218595 40515608185420518024327893)
                  ·
                    refine ⟨949584566845793391195185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40515608185420518024327893 949584566845793391195185)
                    ·
                      rfl

theorem cell22_2773964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_2773964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773964 prefixEnd_2773964 := by exact prefixLift 2773964
  have htrace : WordTrace (prefixWord ++ tailWord_2773964) baseStart_2773964 baseEnd_2773964 := by
    simpa [prefixWord, tailWord_2773964, baseEnd_2773964] using wordTrace_append hprefix tailTrace_2773964
  have hstable : (prefixWord ++ tailWord_2773964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773964).length < 2 ^ (prefixWord ++ tailWord_2773964).sum := by decide
  have hdescent : baseEnd_2773964 < baseStart_2773964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773970 : List Nat := [3, 2, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2773970 : Nat := 118140960795 + 2773970 * 2 ^ 59
def prefixEnd_2773970 : Nat := 4983230072969 + 3 ^ 40 * 2773970 * 2
def baseEnd_2773970 : Nat := 949586620768411375545167

theorem tailTrace_2773970 : CollatzResearch.WordTrace tailWord_2773970 prefixEnd_2773970 949586620768411375545167 := by
  unfold tailWord_2773970
  simp only [CollatzResearch.WordTrace]
  refine ⟨25293749440096980300859841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67449998506925280802292909 25293749440096980300859841)
  ·
    refine ⟨18970312080072735225644881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25293749440096980300859841 18970312080072735225644881)
    ·
      refine ⟨14227734060054551419233661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18970312080072735225644881 14227734060054551419233661)
      ·
        refine ⟨5335400272520456782212623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14227734060054551419233661 5335400272520456782212623)
        ·
          refine ⟨8003100408780685173318935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335400272520456782212623 8003100408780685173318935)
          ·
            refine ⟨12004650613171027759978403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003100408780685173318935 12004650613171027759978403)
            ·
              refine ⟨18006975919756541639967605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004650613171027759978403 18006975919756541639967605)
              ·
                refine ⟨1688153992477175778746963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18006975919756541639967605 1688153992477175778746963)
                ·
                  refine ⟨2532230988715763668120445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688153992477175778746963 2532230988715763668120445)
                  ·
                    refine ⟨949586620768411375545167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532230988715763668120445 949586620768411375545167)
                    ·
                      rfl

theorem cell22_2773970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2773970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773970 prefixEnd_2773970 := by exact prefixLift 2773970
  have htrace : WordTrace (prefixWord ++ tailWord_2773970) baseStart_2773970 baseEnd_2773970 := by
    simpa [prefixWord, tailWord_2773970, baseEnd_2773970] using wordTrace_append hprefix tailTrace_2773970
  have hstable : (prefixWord ++ tailWord_2773970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773970).length < 2 ^ (prefixWord ++ tailWord_2773970).sum := by decide
  have hdescent : baseEnd_2773970 < baseStart_2773970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773981 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2773981 : Nat := 118140960795 + 2773981 * 2 ^ 59
def prefixEnd_2773981 : Nat := 4983230072969 + 3 ^ 40 * 2773981 * 2
def baseEnd_2773981 : Nat := 949590386293211013520133

theorem tailTrace_2773981 : CollatzResearch.WordTrace tailWord_2773981 prefixEnd_2773981 949590386293211013520133 := by
  unfold tailWord_2773981
  simp only [CollatzResearch.WordTrace]
  refine ⟨101175398963348070082089797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67450265975565380054726531 101175398963348070082089797)
  ·
    refine ⟨18970387305627763140391837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101175398963348070082089797 18970387305627763140391837)
    ·
      refine ⟨7113895239610411177646939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18970387305627763140391837 7113895239610411177646939)
      ·
        refine ⟨10670842859415616766470409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7113895239610411177646939 10670842859415616766470409)
        ·
          refine ⟨8003132144561712574852807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10670842859415616766470409 8003132144561712574852807)
          ·
            refine ⟨12004698216842568862279211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003132144561712574852807 12004698216842568862279211)
            ·
              refine ⟨18007047325263853293418817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12004698216842568862279211 18007047325263853293418817)
              ·
                refine ⟨13505285493947889970064113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18007047325263853293418817 13505285493947889970064113)
                ·
                  refine ⟨10128964120460917477548085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13505285493947889970064113 10128964120460917477548085)
                  ·
                    refine ⟨949590386293211013520133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10128964120460917477548085 949590386293211013520133)
                    ·
                      rfl

theorem cell22_2773981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2773981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773981 prefixEnd_2773981 := by exact prefixLift 2773981
  have htrace : WordTrace (prefixWord ++ tailWord_2773981) baseStart_2773981 baseEnd_2773981 := by
    simpa [prefixWord, tailWord_2773981, baseEnd_2773981] using wordTrace_append hprefix tailTrace_2773981
  have hstable : (prefixWord ++ tailWord_2773981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773981).length < 2 ^ (prefixWord ++ tailWord_2773981).sum := by decide
  have hdescent : baseEnd_2773981 < baseStart_2773981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2773983 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 5]
def baseStart_2773983 : Nat := 118140960795 + 2773983 * 2 ^ 59
def prefixEnd_2773983 : Nat := 4983230072969 + 3 ^ 40 * 2773983 * 2
def baseEnd_2773983 : Nat := 316530356978027891656709

theorem tailTrace_2773983 : CollatzResearch.WordTrace tailWord_2773983 prefixEnd_2773983 316530356978027891656709 := by
  unfold tailWord_2773983
  simp only [CollatzResearch.WordTrace]
  refine ⟨101175471909340824423662603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67450314606227216282441735 101175471909340824423662603)
  ·
    refine ⟨151763207864011236635493905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101175471909340824423662603 151763207864011236635493905)
    ·
      refine ⟨113822405898008427476620429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151763207864011236635493905 113822405898008427476620429)
      ·
        refine ⟨42683402211753160303732661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113822405898008427476620429 42683402211753160303732661)
        ·
          refine ⟨4001568957351858778474937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42683402211753160303732661 4001568957351858778474937)
          ·
            refine ⟨3001176718013894083856203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001568957351858778474937 3001176718013894083856203)
            ·
              refine ⟨4501765077020841125784305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001176718013894083856203 4501765077020841125784305)
              ·
                refine ⟨3376323807765630844338229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4501765077020841125784305 3376323807765630844338229)
                ·
                  refine ⟨316530356978027891656709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3376323807765630844338229 316530356978027891656709)
                  ·
                    rfl

theorem cell22_2773983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 5].length) (baseStart_2773983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2773983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2773983 prefixEnd_2773983 := by exact prefixLift 2773983
  have htrace : WordTrace (prefixWord ++ tailWord_2773983) baseStart_2773983 baseEnd_2773983 := by
    simpa [prefixWord, tailWord_2773983, baseEnd_2773983] using wordTrace_append hprefix tailTrace_2773983
  have hstable : (prefixWord ++ tailWord_2773983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2773983).length < 2 ^ (prefixWord ++ tailWord_2773983).sum := by decide
  have hdescent : baseEnd_2773983 < baseStart_2773983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2773983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774028 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_2774028 : Nat := 118140960795 + 2774028 * 2 ^ 59
def prefixEnd_2774028 : Nat := 4983230072969 + 3 ^ 40 * 2774028 * 2
def baseEnd_2774028 : Nat := 316535491784572852531663

theorem tailTrace_2774028 : CollatzResearch.WordTrace tailWord_2774028 prefixEnd_2774028 316535491784572852531663 := by
  unfold tailWord_2774028
  simp only [CollatzResearch.WordTrace]
  refine ⟨50588556597088898554525369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67451408796118531406033825 50588556597088898554525369)
  ·
    refine ⟨37941417447816673915894027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50588556597088898554525369 37941417447816673915894027)
    ·
      refine ⟨56912126171725010873841041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37941417447816673915894027 56912126171725010873841041)
      ·
        refine ⟨42684094628793758155380781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56912126171725010873841041 42684094628793758155380781)
        ·
          refine ⟨16006535485797659308267793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42684094628793758155380781 16006535485797659308267793)
          ·
            refine ⟨12004901614348244481200845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16006535485797659308267793 12004901614348244481200845)
            ·
              refine ⟨4501838105380591680450317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12004901614348244481200845 4501838105380591680450317)
              ·
                refine ⟨1688189289517721880168869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4501838105380591680450317 1688189289517721880168869)
                ·
                  refine ⟨316535491784572852531663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688189289517721880168869 316535491784572852531663)
                  ·
                    rfl

theorem cell22_2774028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_2774028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774028 prefixEnd_2774028 := by exact prefixLift 2774028
  have htrace : WordTrace (prefixWord ++ tailWord_2774028) baseStart_2774028 baseEnd_2774028 := by
    simpa [prefixWord, tailWord_2774028, baseEnd_2774028] using wordTrace_append hprefix tailTrace_2774028
  have hstable : (prefixWord ++ tailWord_2774028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774028).length < 2 ^ (prefixWord ++ tailWord_2774028).sum := by decide
  have hdescent : baseEnd_2774028 < baseStart_2774028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774045 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 6]
def baseStart_2774045 : Nat := 118140960795 + 2774045 * 2 ^ 59
def prefixEnd_2774045 : Nat := 4983230072969 + 3 ^ 40 * 2774045 * 2
def baseEnd_2774045 : Nat := 316537431600378726639979

theorem tailTrace_2774045 : CollatzResearch.WordTrace tailWord_2774045 prefixEnd_2774045 316537431600378726639979 := by
  unfold tailWord_2774045
  simp only [CollatzResearch.WordTrace]
  refine ⟨101177733235116209012419589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67451822156744139341613059 101177733235116209012419589)
  ·
    refine ⟨18970824981584289189828673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101177733235116209012419589 18970824981584289189828673)
    ·
      refine ⟨14228118736188216892371505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18970824981584289189828673 14228118736188216892371505)
      ·
        refine ⟨10671089052141162669278629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14228118736188216892371505 10671089052141162669278629)
        ·
          refine ⟨2000829197276468000489743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10671089052141162669278629 2000829197276468000489743)
          ·
            refine ⟨3001243795914702000734615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000829197276468000489743 3001243795914702000734615)
            ·
              refine ⟨4501865693872053001101923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001243795914702000734615 4501865693872053001101923)
              ·
                refine ⟨6752798540808079501652885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4501865693872053001101923 6752798540808079501652885)
                ·
                  refine ⟨316537431600378726639979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6752798540808079501652885 316537431600378726639979)
                  ·
                    rfl

theorem cell22_2774045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_2774045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774045 prefixEnd_2774045 := by exact prefixLift 2774045
  have htrace : WordTrace (prefixWord ++ tailWord_2774045) baseStart_2774045 baseEnd_2774045 := by
    simpa [prefixWord, tailWord_2774045, baseEnd_2774045] using wordTrace_append hprefix tailTrace_2774045
  have hstable : (prefixWord ++ tailWord_2774045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774045).length < 2 ^ (prefixWord ++ tailWord_2774045).sum := by decide
  have hdescent : baseEnd_2774045 < baseStart_2774045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774071 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 5, 3]
def baseStart_2774071 : Nat := 118140960795 + 2774071 * 2 ^ 59
def prefixEnd_2774071 : Nat := 4983230072969 + 3 ^ 40 * 2774071 * 2
def baseEnd_2774071 : Nat := 949621195132480778769857

theorem tailTrace_2774071 : CollatzResearch.WordTrace tailWord_2774071 prefixEnd_2774071 949621195132480778769857 := by
  unfold tailWord_2774071
  simp only [CollatzResearch.WordTrace]
  refine ⟨101178681533022015452866067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67452454355348010301910711 101178681533022015452866067)
  ·
    refine ⟨151768022299533023179299101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101178681533022015452866067 151768022299533023179299101)
    ·
      refine ⟨56913008362324883692237163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151768022299533023179299101 56913008362324883692237163)
      ·
        refine ⟨85369512543487325538355745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56913008362324883692237163 85369512543487325538355745)
        ·
          refine ⟨64027134407615494153766809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85369512543487325538355745 64027134407615494153766809)
          ·
            refine ⟨48020350805711620615325107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64027134407615494153766809 48020350805711620615325107)
            ·
              refine ⟨72030526208567430922987661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48020350805711620615325107 72030526208567430922987661)
              ·
                refine ⟨27011447328212786596120373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72030526208567430922987661 27011447328212786596120373)
                ·
                  refine ⟨2532323187019948743386285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27011447328212786596120373 2532323187019948743386285)
                  ·
                    refine ⟨949621195132480778769857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532323187019948743386285 949621195132480778769857)
                    ·
                      rfl

theorem cell22_2774071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_2774071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774071 prefixEnd_2774071 := by exact prefixLift 2774071
  have htrace : WordTrace (prefixWord ++ tailWord_2774071) baseStart_2774071 baseEnd_2774071 := by
    simpa [prefixWord, tailWord_2774071, baseEnd_2774071] using wordTrace_append hprefix tailTrace_2774071
  have hstable : (prefixWord ++ tailWord_2774071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774071).length < 2 ^ (prefixWord ++ tailWord_2774071).sum := by decide
  have hdescent : baseEnd_2774071 < baseStart_2774071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774152 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_2774152 : Nat := 118140960795 + 2774152 * 2 ^ 59
def prefixEnd_2774152 : Nat := 4983230072969 + 3 ^ 40 * 2774152 * 2
def baseEnd_2774152 : Nat := 316549641029274522498203

theorem tailTrace_2774152 : CollatzResearch.WordTrace tailWord_2774152 prefixEnd_2774152 316549641029274522498203 := by
  unfold tailWord_2774152
  simp only [CollatzResearch.WordTrace]
  refine ⟨50590817922864283143282355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67454423897152377524376473 50590817922864283143282355)
  ·
    refine ⟨75886226884296424714923533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50590817922864283143282355 75886226884296424714923533)
    ·
      refine ⟨28457335081611159268096325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75886226884296424714923533 28457335081611159268096325)
      ·
        refine ⟨5335750327802092362768061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28457335081611159268096325 5335750327802092362768061)
        ·
          refine ⟨2000906372925784636038023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5335750327802092362768061 2000906372925784636038023)
          ·
            refine ⟨3001359559388676954057035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000906372925784636038023 3001359559388676954057035)
            ·
              refine ⟨4502039339083015431085553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001359559388676954057035 4502039339083015431085553)
              ·
                refine ⟨3376529504312261573314165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502039339083015431085553 3376529504312261573314165)
                ·
                  refine ⟨316549641029274522498203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3376529504312261573314165 316549641029274522498203)
                  ·
                    rfl

theorem cell22_2774152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_2774152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774152 prefixEnd_2774152 := by exact prefixLift 2774152
  have htrace : WordTrace (prefixWord ++ tailWord_2774152) baseStart_2774152 baseEnd_2774152 := by
    simpa [prefixWord, tailWord_2774152, baseEnd_2774152] using wordTrace_append hprefix tailTrace_2774152
  have hstable : (prefixWord ++ tailWord_2774152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774152).length < 2 ^ (prefixWord ++ tailWord_2774152).sum := by decide
  have hdescent : baseEnd_2774152 < baseStart_2774152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774163 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 4]
def baseStart_2774163 : Nat := 118140960795 + 2774163 * 2 ^ 59
def prefixEnd_2774163 : Nat := 4983230072969 + 3 ^ 40 * 2774163 * 2
def baseEnd_2774163 : Nat := 316550896204207735156525

theorem tailTrace_2774163 : CollatzResearch.WordTrace tailWord_2774163 prefixEnd_2774163 316550896204207735156525 := by
  unfold tailWord_2774163
  simp only [CollatzResearch.WordTrace]
  refine ⟨101182037048688715165215143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67454691365792476776810095 101182037048688715165215143)
  ·
    refine ⟨151773055573033072747822715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101182037048688715165215143 151773055573033072747822715)
    ·
      refine ⟨227659583359549609121734073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151773055573033072747822715 227659583359549609121734073)
      ·
        refine ⟨170744687519662206841300555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227659583359549609121734073 170744687519662206841300555)
        ·
          refine ⟨256117031279493310261950833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170744687519662206841300555 256117031279493310261950833)
          ·
            refine ⟨192087773459619982696463125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256117031279493310261950833 192087773459619982696463125)
            ·
              refine ⟨9004114380919686688896709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192087773459619982696463125 9004114380919686688896709)
              ·
                refine ⟨1688271446422441254168133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9004114380919686688896709 1688271446422441254168133)
                ·
                  refine ⟨316550896204207735156525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688271446422441254168133 316550896204207735156525)
                  ·
                    rfl

theorem cell22_2774163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 4].length) (baseStart_2774163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774163 prefixEnd_2774163 := by exact prefixLift 2774163
  have htrace : WordTrace (prefixWord ++ tailWord_2774163) baseStart_2774163 baseEnd_2774163 := by
    simpa [prefixWord, tailWord_2774163, baseEnd_2774163] using wordTrace_append hprefix tailTrace_2774163
  have hstable : (prefixWord ++ tailWord_2774163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774163).length < 2 ^ (prefixWord ++ tailWord_2774163).sum := by decide
  have hdescent : baseEnd_2774163 < baseStart_2774163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774176 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_2774176 : Nat := 118140960795 + 2774176 * 2 ^ 59
def prefixEnd_2774176 : Nat := 4983230072969 + 3 ^ 40 * 2774176 * 2
def baseEnd_2774176 : Nat := 949657138778295504894535

theorem tailTrace_2774176 : CollatzResearch.WordTrace tailWord_2774176 prefixEnd_2774176 949657138778295504894535 := by
  unfold tailWord_2774176
  simp only [CollatzResearch.WordTrace]
  refine ⟨50591255598820809192719191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67455007465094412256958921 50591255598820809192719191)
  ·
    refine ⟨75886883398231213789078787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50591255598820809192719191 75886883398231213789078787)
    ·
      refine ⟨113830325097346820683618181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75886883398231213789078787 113830325097346820683618181)
      ·
        refine ⟨21343185955752528878178409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113830325097346820683618181 21343185955752528878178409)
        ·
          refine ⟨16007389466814396658633807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21343185955752528878178409 16007389466814396658633807)
          ·
            refine ⟨24011084200221594987950711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16007389466814396658633807 24011084200221594987950711)
            ·
              refine ⟨36016626300332392481926067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24011084200221594987950711 36016626300332392481926067)
              ·
                refine ⟨54024939450498588722889101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36016626300332392481926067 54024939450498588722889101)
                ·
                  refine ⟨20259352293936970771083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54024939450498588722889101 20259352293936970771083413)
                  ·
                    refine ⟨949657138778295504894535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20259352293936970771083413 949657138778295504894535)
                    ·
                      rfl

theorem cell22_2774176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_2774176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774176 prefixEnd_2774176 := by exact prefixLift 2774176
  have htrace : WordTrace (prefixWord ++ tailWord_2774176) baseStart_2774176 baseEnd_2774176 := by
    simpa [prefixWord, tailWord_2774176, baseEnd_2774176] using wordTrace_append hprefix tailTrace_2774176
  have hstable : (prefixWord ++ tailWord_2774176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774176).length < 2 ^ (prefixWord ++ tailWord_2774176).sum := by decide
  have hdescent : baseEnd_2774176 < baseStart_2774176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774193 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 6]
def baseStart_2774193 : Nat := 118140960795 + 2774193 * 2 ^ 59
def prefixEnd_2774193 : Nat := 4983230072969 + 3 ^ 40 * 2774193 * 2
def baseEnd_2774193 : Nat := 949662958225713127219483

theorem tailTrace_2774193 : CollatzResearch.WordTrace tailWord_2774193 prefixEnd_2774193 949662958225713127219483 := by
  unfold tailWord_2774193
  simp only [CollatzResearch.WordTrace]
  refine ⟨101183131238580030288807233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67455420825720020192538155 101183131238580030288807233)
  ·
    refine ⟨75887348428935022716605425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101183131238580030288807233 75887348428935022716605425)
    ·
      refine ⟨56915511321701267037454069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75887348428935022716605425 56915511321701267037454069)
      ·
        refine ⟨5335829186409493784761319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56915511321701267037454069 5335829186409493784761319)
        ·
          refine ⟨8003743779614240677141979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335829186409493784761319 8003743779614240677141979)
          ·
            refine ⟨12005615669421361015712969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003743779614240677141979 12005615669421361015712969)
            ·
              refine ⟨9004211752066020761784727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12005615669421361015712969 9004211752066020761784727)
              ·
                refine ⟨13506317628099031142677091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004211752066020761784727 13506317628099031142677091)
                ·
                  refine ⟨20259476442148546714015637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13506317628099031142677091 20259476442148546714015637)
                  ·
                    refine ⟨949662958225713127219483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20259476442148546714015637 949662958225713127219483)
                    ·
                      rfl

theorem cell22_2774193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_2774193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774193 prefixEnd_2774193 := by exact prefixLift 2774193
  have htrace : WordTrace (prefixWord ++ tailWord_2774193) baseStart_2774193 baseEnd_2774193 := by
    simpa [prefixWord, tailWord_2774193, baseEnd_2774193] using wordTrace_append hprefix tailTrace_2774193
  have hstable : (prefixWord ++ tailWord_2774193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774193).length < 2 ^ (prefixWord ++ tailWord_2774193).sum := by decide
  have hdescent : baseEnd_2774193 < baseStart_2774193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774208 : List Nat := [2, 1, 1, 2, 6, 2, 8]
def baseStart_2774208 : Nat := 118140960795 + 2774208 * 2 ^ 59
def prefixEnd_2774208 : Nat := 4983230072969 + 3 ^ 40 * 2774208 * 2
def baseEnd_2774208 : Nat := 35172892334528077336831

theorem tailTrace_2774208 : CollatzResearch.WordTrace tailWord_2774208 prefixEnd_2774208 35172892334528077336831 := by
  unfold tailWord_2774208
  simp only [CollatzResearch.WordTrace]
  refine ⟨50591839166762843925301639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67455785555683791900402185 50591839166762843925301639)
  ·
    refine ⟨75887758750144265887952459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50591839166762843925301639 75887758750144265887952459)
    ·
      refine ⟨113831638125216398831928689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75887758750144265887952459 113831638125216398831928689)
      ·
        refine ⟨85373728593912299123946517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113831638125216398831928689 85373728593912299123946517)
        ·
          refine ⟨4001893527839639021434993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85373728593912299123946517 4001893527839639021434993)
          ·
            refine ⟨3001420145879729266076245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4001893527839639021434993 3001420145879729266076245)
            ·
              refine ⟨35172892334528077336831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3001420145879729266076245 35172892334528077336831)
              ·
                rfl

theorem cell22_2774208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 8].length) (baseStart_2774208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774208 prefixEnd_2774208 := by exact prefixLift 2774208
  have htrace : WordTrace (prefixWord ++ tailWord_2774208) baseStart_2774208 baseEnd_2774208 := by
    simpa [prefixWord, tailWord_2774208, baseEnd_2774208] using wordTrace_append hprefix tailTrace_2774208
  have hstable : (prefixWord ++ tailWord_2774208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774208).length < 2 ^ (prefixWord ++ tailWord_2774208).sum := by decide
  have hdescent : baseEnd_2774208 < baseStart_2774208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774223 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 3, 3]
def baseStart_2774223 : Nat := 118140960795 + 2774223 * 2 ^ 59
def prefixEnd_2774223 : Nat := 4983230072969 + 3 ^ 40 * 2774223 * 2
def baseEnd_2774223 : Nat := 949673227838803048969391

theorem tailTrace_2774223 : CollatzResearch.WordTrace tailWord_2774223 prefixEnd_2774223 949673227838803048969391 := by
  unfold tailWord_2774223
  simp only [CollatzResearch.WordTrace]
  refine ⟨101184225428471345412399323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67456150285647563608266215 101184225428471345412399323)
  ·
    refine ⟨151776338142707018118598985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101184225428471345412399323 151776338142707018118598985)
    ·
      refine ⟨113832253607030263588949239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151776338142707018118598985 113832253607030263588949239)
      ·
        refine ⟨170748380410545395383423859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113832253607030263588949239 170748380410545395383423859)
        ·
          refine ⟨256122570615818093075135789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170748380410545395383423859 256122570615818093075135789)
          ·
            refine ⟨96045963980931784903175921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256122570615818093075135789 96045963980931784903175921)
            ·
              refine ⟨72034472985698838677381941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96045963980931784903175921 72034472985698838677381941)
              ·
                refine ⟨6753231842409266126004557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72034472985698838677381941 6753231842409266126004557)
                ·
                  refine ⟨2532461940903474797251709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6753231842409266126004557 2532461940903474797251709)
                  ·
                    refine ⟨949673227838803048969391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532461940903474797251709 949673227838803048969391)
                    ·
                      rfl

theorem cell22_2774223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_2774223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774223 prefixEnd_2774223 := by exact prefixLift 2774223
  have htrace : WordTrace (prefixWord ++ tailWord_2774223) baseStart_2774223 baseEnd_2774223 := by
    simpa [prefixWord, tailWord_2774223, baseEnd_2774223] using wordTrace_append hprefix tailTrace_2774223
  have hstable : (prefixWord ++ tailWord_2774223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774223).length < 2 ^ (prefixWord ++ tailWord_2774223).sum := by decide
  have hdescent : baseEnd_2774223 < baseStart_2774223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774229 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 2, 3]
def baseStart_2774229 : Nat := 118140960795 + 2774229 * 2 ^ 59
def prefixEnd_2774229 : Nat := 4983230072969 + 3 ^ 40 * 2774229 * 2
def baseEnd_2774229 : Nat := 949675281761421033319373

theorem tailTrace_2774229 : CollatzResearch.WordTrace tailWord_2774229 prefixEnd_2774229 949675281761421033319373 := by
  unfold tailWord_2774229
  simp only [CollatzResearch.WordTrace]
  refine ⟨101184444266449608437117741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67456296177633072291411827 101184444266449608437117741)
  ·
    refine ⟨37944166599918603163919153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101184444266449608437117741 37944166599918603163919153)
    ·
      refine ⟨28458124949938952372939365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37944166599918603163919153 28458124949938952372939365)
      ·
        refine ⟨5335898428113553569926131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28458124949938952372939365 5335898428113553569926131)
        ·
          refine ⟨8003847642170330354889197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335898428113553569926131 8003847642170330354889197)
          ·
            refine ⟨3001442865813873883083449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8003847642170330354889197 3001442865813873883083449)
            ·
              refine ⟨2251082149360405412312587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001442865813873883083449 2251082149360405412312587)
              ·
                refine ⟨3376623224040608118468881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251082149360405412312587 3376623224040608118468881)
                ·
                  refine ⟨2532467418030456088851661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376623224040608118468881 2532467418030456088851661)
                  ·
                    refine ⟨949675281761421033319373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532467418030456088851661 949675281761421033319373)
                    ·
                      rfl

theorem cell22_2774229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_2774229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774229 prefixEnd_2774229 := by exact prefixLift 2774229
  have htrace : WordTrace (prefixWord ++ tailWord_2774229) baseStart_2774229 baseEnd_2774229 := by
    simpa [prefixWord, tailWord_2774229, baseEnd_2774229] using wordTrace_append hprefix tailTrace_2774229
  have hstable : (prefixWord ++ tailWord_2774229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774229).length < 2 ^ (prefixWord ++ tailWord_2774229).sum := by decide
  have hdescent : baseEnd_2774229 < baseStart_2774229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774270 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2774270 : Nat := 118140960795 + 2774270 * 2 ^ 59
def prefixEnd_2774270 : Nat := 4983230072969 + 3 ^ 40 * 2774270 * 2
def baseEnd_2774270 : Nat := 316563105633103531014749

theorem tailTrace_2774270 : CollatzResearch.WordTrace tailWord_2774270 prefixEnd_2774270 316563105633103531014749 := by
  unfold tailWord_2774270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648242457412634054920033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67457293106200714959573509 12648242457412634054920033)
  ·
    refine ⟨9486181843059475541190025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12648242457412634054920033 9486181843059475541190025)
    ·
      refine ⟨7114636382294606655892519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9486181843059475541190025 7114636382294606655892519)
      ·
        refine ⟨10671954573441909983838779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7114636382294606655892519 10671954573441909983838779)
        ·
          refine ⟨16007931860162864975758169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10671954573441909983838779 16007931860162864975758169)
          ·
            refine ⟨12005948895122148731818627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16007931860162864975758169 12005948895122148731818627)
            ·
              refine ⟨18008923342683223097727941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005948895122148731818627 18008923342683223097727941)
              ·
                refine ⟨3376673126753104330823989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18008923342683223097727941 3376673126753104330823989)
                ·
                  refine ⟨316563105633103531014749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3376673126753104330823989 316563105633103531014749)
                  ·
                    rfl

theorem cell22_2774270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2774270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774270 prefixEnd_2774270 := by exact prefixLift 2774270
  have htrace : WordTrace (prefixWord ++ tailWord_2774270) baseStart_2774270 baseEnd_2774270 := by
    simpa [prefixWord, tailWord_2774270, baseEnd_2774270] using wordTrace_append hprefix tailTrace_2774270
  have hstable : (prefixWord ++ tailWord_2774270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774270).length < 2 ^ (prefixWord ++ tailWord_2774270).sum := by decide
  have hdescent : baseEnd_2774270 < baseStart_2774270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774283 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 3, 4]
def baseStart_2774283 : Nat := 118140960795 + 2774283 * 2 ^ 59
def prefixEnd_2774283 : Nat := 4983230072969 + 3 ^ 40 * 2774283 * 2
def baseEnd_2774283 : Nat := 949693767064982892469207

theorem tailTrace_2774283 : CollatzResearch.WordTrace tailWord_2774283 prefixEnd_2774283 949693767064982892469207 := by
  unfold tailWord_2774283
  simp only [CollatzResearch.WordTrace]
  refine ⟨101186413808253975659583503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67457609205502650439722335 101186413808253975659583503)
  ·
    refine ⟨151779620712380963489375255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101186413808253975659583503 151779620712380963489375255)
    ·
      refine ⟨227669431068571445234062883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151779620712380963489375255 227669431068571445234062883)
      ·
        refine ⟨341504146602857167851094325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227669431068571445234062883 341504146602857167851094325)
        ·
          refine ⟨32016013744017859486040093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 341504146602857167851094325 32016013744017859486040093)
          ·
            refine ⟨12006005154006697307265035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32016013744017859486040093 12006005154006697307265035)
            ·
              refine ⟨18009007731010045960897553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12006005154006697307265035 18009007731010045960897553)
              ·
                refine ⟨13506755798257534470673165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18009007731010045960897553 13506755798257534470673165)
                ·
                  refine ⟨5065033424346575426502437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13506755798257534470673165 5065033424346575426502437)
                  ·
                    refine ⟨949693767064982892469207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065033424346575426502437 949693767064982892469207)
                    ·
                      rfl

theorem cell22_2774283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 4].length) (baseStart_2774283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774283 prefixEnd_2774283 := by exact prefixLift 2774283
  have htrace : WordTrace (prefixWord ++ tailWord_2774283) baseStart_2774283 baseEnd_2774283 := by
    simpa [prefixWord, tailWord_2774283, baseEnd_2774283] using wordTrace_append hprefix tailTrace_2774283
  have hstable : (prefixWord ++ tailWord_2774283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774283).length < 2 ^ (prefixWord ++ tailWord_2774283).sum := by decide
  have hdescent : baseEnd_2774283 < baseStart_2774283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774298 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_2774298 : Nat := 118140960795 + 2774298 * 2 ^ 59
def prefixEnd_2774298 : Nat := 4983230072969 + 3 ^ 40 * 2774298 * 2
def baseEnd_2774298 : Nat := 316566300623842617781387

theorem tailTrace_2774298 : CollatzResearch.WordTrace tailWord_2774298 prefixEnd_2774298 316566300623842617781387 := by
  unfold tailWord_2774298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25296740225799908305344887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67457973935466422147586365 25296740225799908305344887)
  ·
    refine ⟨37945110338699862458017331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25296740225799908305344887 37945110338699862458017331)
    ·
      refine ⟨56917665508049793687025997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37945110338699862458017331 56917665508049793687025997)
      ·
        refine ⟨21344124565518672632634749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56917665508049793687025997 21344124565518672632634749)
        ·
          refine ⟨8004046712069502237238031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21344124565518672632634749 8004046712069502237238031)
          ·
            refine ⟨12006070068104253355857047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004046712069502237238031 12006070068104253355857047)
            ·
              refine ⟨18009105102156380033785571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12006070068104253355857047 18009105102156380033785571)
              ·
                refine ⟨27013657653234570050678357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18009105102156380033785571 27013657653234570050678357)
                ·
                  refine ⟨316566300623842617781387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27013657653234570050678357 316566300623842617781387)
                  ·
                    rfl

theorem cell22_2774298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_2774298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774298 prefixEnd_2774298 := by exact prefixLift 2774298
  have htrace : WordTrace (prefixWord ++ tailWord_2774298) baseStart_2774298 baseEnd_2774298 := by
    simpa [prefixWord, tailWord_2774298, baseEnd_2774298] using wordTrace_append hprefix tailTrace_2774298
  have hstable : (prefixWord ++ tailWord_2774298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774298).length < 2 ^ (prefixWord ++ tailWord_2774298).sum := by decide
  have hdescent : baseEnd_2774298 < baseStart_2774298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774328 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_2774328 : Nat := 118140960795 + 2774328 * 2 ^ 59
def prefixEnd_2774328 : Nat := 4983230072969 + 3 ^ 40 * 2774328 * 2
def baseEnd_2774328 : Nat := 949709171484617775094069

theorem tailTrace_2774328 : CollatzResearch.WordTrace tailWord_2774328 prefixEnd_2774328 949709171484617775094069 := by
  unfold tailWord_2774328
  simp only [CollatzResearch.WordTrace]
  refine ⟨50594027546545474172485819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67458703395393965563314425 50594027546545474172485819)
  ·
    refine ⟨75891041319818211258728729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50594027546545474172485819 75891041319818211258728729)
    ·
      refine ⟨56918280989863658444046547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75891041319818211258728729 56918280989863658444046547)
      ·
        refine ⟨85377421484795487666069821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56918280989863658444046547 85377421484795487666069821)
        ·
          refine ⟨32016533056798307874776183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85377421484795487666069821 32016533056798307874776183)
          ·
            refine ⟨48024799585197461812164275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32016533056798307874776183 48024799585197461812164275)
            ·
              refine ⟨72037199377796192718246413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48024799585197461812164275 72037199377796192718246413)
              ·
                refine ⟨27013949766673572269342405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72037199377796192718246413 27013949766673572269342405)
                ·
                  refine ⟨5065115581251294800501701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27013949766673572269342405 5065115581251294800501701)
                  ·
                    refine ⟨949709171484617775094069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065115581251294800501701 949709171484617775094069)
                    ·
                      rfl

theorem cell22_2774328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_2774328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774328 prefixEnd_2774328 := by exact prefixLift 2774328
  have htrace : WordTrace (prefixWord ++ tailWord_2774328) baseStart_2774328 baseEnd_2774328 := by
    simpa [prefixWord, tailWord_2774328, baseEnd_2774328] using wordTrace_append hprefix tailTrace_2774328
  have hstable : (prefixWord ++ tailWord_2774328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774328).length < 2 ^ (prefixWord ++ tailWord_2774328).sum := by decide
  have hdescent : baseEnd_2774328 < baseStart_2774328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774330 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_2774330 : Nat := 118140960795 + 2774330 * 2 ^ 59
def prefixEnd_2774330 : Nat := 4983230072969 + 3 ^ 40 * 2774330 * 2
def baseEnd_2774330 : Nat := 949709856125490436544063

theorem tailTrace_2774330 : CollatzResearch.WordTrace tailWord_2774330 prefixEnd_2774330 949709856125490436544063 := by
  unfold tailWord_2774330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25297032009770925671636111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67458752026055801791029629 25297032009770925671636111)
  ·
    refine ⟨37945548014656388507454167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25297032009770925671636111 37945548014656388507454167)
    ·
      refine ⟨56918322021984582761181251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37945548014656388507454167 56918322021984582761181251)
      ·
        refine ⟨85377483032976874141771877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56918322021984582761181251 85377483032976874141771877)
        ·
          refine ⟨16008278068683163901582227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85377483032976874141771877 16008278068683163901582227)
          ·
            refine ⟨24012417103024745852373341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16008278068683163901582227 24012417103024745852373341)
            ·
              refine ⟨9004656413634279694640003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24012417103024745852373341 9004656413634279694640003)
              ·
                refine ⟨13506984620451419541960005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004656413634279694640003 13506984620451419541960005)
                ·
                  refine ⟨2532559616334641164117501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13506984620451419541960005 2532559616334641164117501)
                  ·
                    refine ⟨949709856125490436544063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532559616334641164117501 949709856125490436544063)
                    ·
                      rfl

theorem cell22_2774330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_2774330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774330 prefixEnd_2774330 := by exact prefixLift 2774330
  have htrace : WordTrace (prefixWord ++ tailWord_2774330) baseStart_2774330 baseEnd_2774330 := by
    simpa [prefixWord, tailWord_2774330, baseEnd_2774330] using wordTrace_append hprefix tailTrace_2774330
  have hstable : (prefixWord ++ tailWord_2774330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774330).length < 2 ^ (prefixWord ++ tailWord_2774330).sum := by decide
  have hdescent : baseEnd_2774330 < baseStart_2774330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774486 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2774486 : Nat := 118140960795 + 2774486 * 2 ^ 59
def prefixEnd_2774486 : Nat := 4983230072969 + 3 ^ 40 * 2774486 * 2
def baseEnd_2774486 : Nat := 949763258113558029643585

theorem tailTrace_2774486 : CollatzResearch.WordTrace tailWord_2774486 prefixEnd_2774486 949763258113558029643585 := by
  unfold tailWord_2774486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324613614157408833076457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67462545217679027552815541 6324613614157408833076457)
  ·
    refine ⟨4743460210618056624807343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6324613614157408833076457 4743460210618056624807343)
    ·
      refine ⟨7115190315927084937211015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743460210618056624807343 7115190315927084937211015)
      ·
        refine ⟨10672785473890627405816523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115190315927084937211015 10672785473890627405816523)
        ·
          refine ⟨16009178210835941108724785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10672785473890627405816523 16009178210835941108724785)
          ·
            refine ⟨12006883658126955831543589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16009178210835941108724785 12006883658126955831543589)
            ·
              refine ⟨2251290685898804218414423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12006883658126955831543589 2251290685898804218414423)
              ·
                refine ⟨3376936028848206327621635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251290685898804218414423 3376936028848206327621635)
                ·
                  refine ⟨5065404043272309491432453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376936028848206327621635 5065404043272309491432453)
                  ·
                    refine ⟨949763258113558029643585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5065404043272309491432453 949763258113558029643585)
                    ·
                      rfl

theorem cell22_2774486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2774486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774486 prefixEnd_2774486 := by exact prefixLift 2774486
  have htrace : WordTrace (prefixWord ++ tailWord_2774486) baseStart_2774486 baseEnd_2774486 := by
    simpa [prefixWord, tailWord_2774486, baseEnd_2774486] using wordTrace_append hprefix tailTrace_2774486
  have hstable : (prefixWord ++ tailWord_2774486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774486).length < 2 ^ (prefixWord ++ tailWord_2774486).sum := by decide
  have hdescent : baseEnd_2774486 < baseStart_2774486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774499 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 2, 3]
def baseStart_2774499 : Nat := 118140960795 + 2774499 * 2 ^ 59
def prefixEnd_2774499 : Nat := 4983230072969 + 3 ^ 40 * 2774499 * 2
def baseEnd_2774499 : Nat := 949767708279230329068545

theorem tailTrace_2774499 : CollatzResearch.WordTrace tailWord_2774499 prefixEnd_2774499 949767708279230329068545 := by
  unfold tailWord_2774499
  simp only [CollatzResearch.WordTrace]
  refine ⟨101194291975471444549446551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67462861316980963032964367 101194291975471444549446551)
  ·
    refine ⟨151791437963207166824169827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101194291975471444549446551 151791437963207166824169827)
    ·
      refine ⟨227687156944810750236254741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151791437963207166824169827 227687156944810750236254741)
      ·
        refine ⟨10672835481788003917324441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 227687156944810750236254741 10672835481788003917324441)
        ·
          refine ⟨8004626611341002937993331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10672835481788003917324441 8004626611341002937993331)
          ·
            refine ⟨12006939917011504406989997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8004626611341002937993331 12006939917011504406989997)
            ·
              refine ⟨4502602468879314152621249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12006939917011504406989997 4502602468879314152621249)
              ·
                refine ⟨3376951851659485614465937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502602468879314152621249 3376951851659485614465937)
                ·
                  refine ⟨2532713888744614210849453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3376951851659485614465937 2532713888744614210849453)
                  ·
                    refine ⟨949767708279230329068545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532713888744614210849453 949767708279230329068545)
                    ·
                      rfl

theorem cell22_2774499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 3].length) (baseStart_2774499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774499 prefixEnd_2774499 := by exact prefixLift 2774499
  have htrace : WordTrace (prefixWord ++ tailWord_2774499) baseStart_2774499 baseEnd_2774499 := by
    simpa [prefixWord, tailWord_2774499, baseEnd_2774499] using wordTrace_append hprefix tailTrace_2774499
  have hstable : (prefixWord ++ tailWord_2774499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774499).length < 2 ^ (prefixWord ++ tailWord_2774499).sum := by decide
  have hdescent : baseEnd_2774499 < baseStart_2774499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774529 : List Nat := [1, 2, 4, 1, 4, 2, 2, 6]
def baseStart_2774529 : Nat := 118140960795 + 2774529 * 2 ^ 59
def prefixEnd_2774529 : Nat := 4983230072969 + 3 ^ 40 * 2774529 * 2
def baseEnd_2774529 : Nat := 105530886432480027868717

theorem tailTrace_2774529 : CollatzResearch.WordTrace tailWord_2774529 prefixEnd_2774529 105530886432480027868717 := by
  unfold tailWord_2774529
  simp only [CollatzResearch.WordTrace]
  refine ⟨101195386165362759673038641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67463590776908506448692427 101195386165362759673038641)
  ·
    refine ⟨75896539624022069754778981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101195386165362759673038641 75896539624022069754778981)
    ·
      refine ⟨14230601179504138079021059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75896539624022069754778981 14230601179504138079021059)
      ·
        refine ⟨21345901769256207118531589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14230601179504138079021059 21345901769256207118531589)
        ·
          refine ⟨4002356581735538834724673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21345901769256207118531589 4002356581735538834724673)
          ·
            refine ⟨3001767436301654126043505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002356581735538834724673 3001767436301654126043505)
            ·
              refine ⟨2251325577226240594532629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001767436301654126043505 2251325577226240594532629)
              ·
                refine ⟨105530886432480027868717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2251325577226240594532629 105530886432480027868717)
                ·
                  rfl

theorem cell22_2774529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 6].length) (baseStart_2774529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774529 prefixEnd_2774529 := by exact prefixLift 2774529
  have htrace : WordTrace (prefixWord ++ tailWord_2774529) baseStart_2774529 baseEnd_2774529 := by
    simpa [prefixWord, tailWord_2774529, baseEnd_2774529] using wordTrace_append hprefix tailTrace_2774529
  have hstable : (prefixWord ++ tailWord_2774529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774529).length < 2 ^ (prefixWord ++ tailWord_2774529).sum := by decide
  have hdescent : baseEnd_2774529 < baseStart_2774529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774557 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 5]
def baseStart_2774557 : Nat := 118140960795 + 2774557 * 2 ^ 59
def prefixEnd_2774557 : Nat := 4983230072969 + 3 ^ 40 * 2774557 * 2
def baseEnd_2774557 : Nat := 316595854288179170372789

theorem tailTrace_2774557 : CollatzResearch.WordTrace tailWord_2774557 prefixEnd_2774557 316595854288179170372789 := by
  unfold tailWord_2774557
  simp only [CollatzResearch.WordTrace]
  refine ⟨101196407409261320455057925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67464271606174213636705283 101196407409261320455057925)
  ·
    refine ⟨18974326389236497585323361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101196407409261320455057925 18974326389236497585323361)
    ·
      refine ⟨14230744791927373188992521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18974326389236497585323361 14230744791927373188992521)
      ·
        refine ⟨10673058593945529891744391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14230744791927373188992521 10673058593945529891744391)
        ·
          refine ⟨16009587890918294837616587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10673058593945529891744391 16009587890918294837616587)
          ·
            refine ⟨24014381836377442256424881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16009587890918294837616587 24014381836377442256424881)
            ·
              refine ⟨18010786377283081692318661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24014381836377442256424881 18010786377283081692318661)
              ·
                refine ⟨3377022445740577817309749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18010786377283081692318661 3377022445740577817309749)
                ·
                  refine ⟨316595854288179170372789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3377022445740577817309749 316595854288179170372789)
                  ·
                    rfl

theorem cell22_2774557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_2774557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774557 prefixEnd_2774557 := by exact prefixLift 2774557
  have htrace : WordTrace (prefixWord ++ tailWord_2774557) baseStart_2774557 baseEnd_2774557 := by
    simpa [prefixWord, tailWord_2774557, baseEnd_2774557] using wordTrace_append hprefix tailTrace_2774557
  have hstable : (prefixWord ++ tailWord_2774557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774557).length < 2 ^ (prefixWord ++ tailWord_2774557).sum := by decide
  have hdescent : baseEnd_2774557 < baseStart_2774557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774574 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_2774574 : Nat := 118140960795 + 2774574 * 2 ^ 59
def prefixEnd_2774574 : Nat := 4983230072969 + 3 ^ 40 * 2774574 * 2
def baseEnd_2774574 : Nat := 316597794103985044481105

theorem tailTrace_2774574 : CollatzResearch.WordTrace tailWord_2774574 prefixEnd_2774574 316597794103985044481105 := by
  unfold tailWord_2774574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12649628431274966544803347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67464684966799821572284517 12649628431274966544803347)
  ·
    refine ⟨18974442646912449817205021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12649628431274966544803347 18974442646912449817205021)
    ·
      refine ⟨7115415992592168681451883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18974442646912449817205021 7115415992592168681451883)
      ·
        refine ⟨10673123988888253022177825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115415992592168681451883 10673123988888253022177825)
        ·
          refine ⟨8004842991666189766633369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10673123988888253022177825 8004842991666189766633369)
          ·
            refine ⟨6003632243749642324975027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8004842991666189766633369 6003632243749642324975027)
            ·
              refine ⟨9005448365624463487462541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003632243749642324975027 9005448365624463487462541)
              ·
                refine ⟨3377043137109173807798453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9005448365624463487462541 3377043137109173807798453)
                ·
                  refine ⟨316597794103985044481105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3377043137109173807798453 316597794103985044481105)
                  ·
                    rfl

theorem cell22_2774574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_2774574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774574 prefixEnd_2774574 := by exact prefixLift 2774574
  have htrace : WordTrace (prefixWord ++ tailWord_2774574) baseStart_2774574 baseEnd_2774574 := by
    simpa [prefixWord, tailWord_2774574, baseEnd_2774574] using wordTrace_append hprefix tailTrace_2774574
  have hstable : (prefixWord ++ tailWord_2774574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774574).length < 2 ^ (prefixWord ++ tailWord_2774574).sum := by decide
  have hdescent : baseEnd_2774574 < baseStart_2774574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774617 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_2774617 : Nat := 118140960795 + 2774617 * 2 ^ 59
def prefixEnd_2774617 : Nat := 4983230072969 + 3 ^ 40 * 2774617 * 2
def baseEnd_2774617 : Nat := 949808102090717354618183

theorem tailTrace_2774617 : CollatzResearch.WordTrace tailWord_2774617 prefixEnd_2774617 949808102090717354618183 := by
  unfold tailWord_2774617
  simp only [CollatzResearch.WordTrace]
  refine ⟨101198595789043950702242105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67465730526029300468161403 101198595789043950702242105)
  ·
    refine ⟨75898946841782963026681579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101198595789043950702242105 75898946841782963026681579)
    ·
      refine ⟨113848420262674444540022369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75898946841782963026681579 113848420262674444540022369)
      ·
        refine ⟨85386315197005833405016777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113848420262674444540022369 85386315197005833405016777)
        ·
          refine ⟨64039736397754375053762583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85386315197005833405016777 64039736397754375053762583)
          ·
            refine ⟨96059604596631562580643875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64039736397754375053762583 96059604596631562580643875)
            ·
              refine ⟨144089406894947343870965813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96059604596631562580643875 144089406894947343870965813)
              ·
                refine ⟨13508381896401313487903045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144089406894947343870965813 13508381896401313487903045)
                ·
                  refine ⟨2532821605575246278981821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13508381896401313487903045 2532821605575246278981821)
                  ·
                    refine ⟨949808102090717354618183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532821605575246278981821 949808102090717354618183)
                    ·
                      rfl

theorem cell22_2774617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_2774617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774617 prefixEnd_2774617 := by exact prefixLift 2774617
  have htrace : WordTrace (prefixWord ++ tailWord_2774617) baseStart_2774617 baseEnd_2774617 := by
    simpa [prefixWord, tailWord_2774617, baseEnd_2774617] using wordTrace_append hprefix tailTrace_2774617
  have hstable : (prefixWord ++ tailWord_2774617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774617).length < 2 ^ (prefixWord ++ tailWord_2774617).sum := by decide
  have hdescent : baseEnd_2774617 < baseStart_2774617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774634 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2774634 : Nat := 118140960795 + 2774634 * 2 ^ 59
def prefixEnd_2774634 : Nat := 4983230072969 + 3 ^ 40 * 2774634 * 2
def baseEnd_2774634 : Nat := 949813921538134976943131

theorem tailTrace_2774634 : CollatzResearch.WordTrace tailWord_2774634 prefixEnd_2774634 949813921538134976943131 := by
  unfold tailWord_2774634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25299803957495590651402739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67466143886654908403740637 25299803957495590651402739)
  ·
    refine ⟨37949705936243385977104109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25299803957495590651402739 37949705936243385977104109)
    ·
      refine ⟨14231139726091269741414041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37949705936243385977104109 14231139726091269741414041)
      ·
        refine ⟨10673354794568452306060531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14231139726091269741414041 10673354794568452306060531)
        ·
          refine ⟨16010032191852678459090797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10673354794568452306060531 16010032191852678459090797)
          ·
            refine ⟨6003762071944754422159049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16010032191852678459090797 6003762071944754422159049)
            ·
              refine ⟨4502821553958565816619287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6003762071944754422159049 4502821553958565816619287)
              ·
                refine ⟨6754232330937848724928931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502821553958565816619287 6754232330937848724928931)
                ·
                  refine ⟨10131348496406773087393397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754232330937848724928931 10131348496406773087393397)
                  ·
                    refine ⟨949813921538134976943131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10131348496406773087393397 949813921538134976943131)
                    ·
                      rfl

theorem cell22_2774634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2774634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774634 prefixEnd_2774634 := by exact prefixLift 2774634
  have htrace : WordTrace (prefixWord ++ tailWord_2774634) baseStart_2774634 baseEnd_2774634 := by
    simpa [prefixWord, tailWord_2774634, baseEnd_2774634] using wordTrace_append hprefix tailTrace_2774634
  have hstable : (prefixWord ++ tailWord_2774634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774634).length < 2 ^ (prefixWord ++ tailWord_2774634).sum := by decide
  have hdescent : baseEnd_2774634 < baseStart_2774634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774664 : List Nat := [2, 1, 3, 5, 1, 1, 9]
def baseStart_2774664 : Nat := 118140960795 + 2774664 * 2 ^ 59
def prefixEnd_2774664 : Nat := 4983230072969 + 3 ^ 40 * 2774664 * 2
def baseEnd_2774664 : Nat := 35178673746341662914557

theorem tailTrace_2774664 : CollatzResearch.WordTrace tailWord_2774664 prefixEnd_2774664 35178673746341662914557 := by
  unfold tailWord_2774664
  simp only [CollatzResearch.WordTrace]
  refine ⟨50600155009936838864601523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67466873346582451819468697 50600155009936838864601523)
  ·
    refine ⟨75900232514905258296902285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50600155009936838864601523 75900232514905258296902285)
    ·
      refine ⟨28462587193089471861338357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75900232514905258296902285 28462587193089471861338357)
      ·
        refine ⟨2668367549352137987000471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28462587193089471861338357 2668367549352137987000471)
        ·
          refine ⟨4002551324028206980500707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668367549352137987000471 4002551324028206980500707)
          ·
            refine ⟨6003826986042310470751061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002551324028206980500707 6003826986042310470751061)
            ·
              refine ⟨35178673746341662914557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6003826986042310470751061 35178673746341662914557)
              ·
                rfl

theorem cell22_2774664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 9].length) (baseStart_2774664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774664 prefixEnd_2774664 := by exact prefixLift 2774664
  have htrace : WordTrace (prefixWord ++ tailWord_2774664) baseStart_2774664 baseEnd_2774664 := by
    simpa [prefixWord, tailWord_2774664, baseEnd_2774664] using wordTrace_append hprefix tailTrace_2774664
  have hstable : (prefixWord ++ tailWord_2774664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774664).length < 2 ^ (prefixWord ++ tailWord_2774664).sum := by decide
  have hdescent : baseEnd_2774664 < baseStart_2774664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774679 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 3, 3]
def baseStart_2774679 : Nat := 118140960795 + 2774679 * 2 ^ 59
def prefixEnd_2774679 : Nat := 4983230072969 + 3 ^ 40 * 2774679 * 2
def baseEnd_2774679 : Nat := 949829325957769859567993

theorem tailTrace_2774679 : CollatzResearch.WordTrace tailWord_2774679 prefixEnd_2774679 949829325957769859567993 := by
  unfold tailWord_2774679
  simp only [CollatzResearch.WordTrace]
  refine ⟨101200857114819335290999091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67467238076546223527332727 101200857114819335290999091)
  ·
    refine ⟨151801285672229002936498637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101200857114819335290999091 151801285672229002936498637)
    ·
      refine ⟨56925482127085876101186989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151801285672229002936498637 56925482127085876101186989)
      ·
        refine ⟨21347055797657203537945121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56925482127085876101186989 21347055797657203537945121)
        ·
          refine ⟨16010291848242902653458841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21347055797657203537945121 16010291848242902653458841)
          ·
            refine ⟨12007718886182176990094131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16010291848242902653458841 12007718886182176990094131)
            ·
              refine ⟨18011578329273265485141197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12007718886182176990094131 18011578329273265485141197)
              ·
                refine ⟨6754341873477474556927949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18011578329273265485141197 6754341873477474556927949)
                ·
                  refine ⟨2532878202554052958847981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6754341873477474556927949 2532878202554052958847981)
                  ·
                    refine ⟨949829325957769859567993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532878202554052958847981 949829325957769859567993)
                    ·
                      rfl

theorem cell22_2774679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_2774679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774679 prefixEnd_2774679 := by exact prefixLift 2774679
  have htrace : WordTrace (prefixWord ++ tailWord_2774679) baseStart_2774679 baseEnd_2774679 := by
    simpa [prefixWord, tailWord_2774679, baseEnd_2774679] using wordTrace_append hprefix tailTrace_2774679
  have hstable : (prefixWord ++ tailWord_2774679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774679).length < 2 ^ (prefixWord ++ tailWord_2774679).sum := by decide
  have hdescent : baseEnd_2774679 < baseStart_2774679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774730 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2774730 : Nat := 118140960795 + 2774730 * 2 ^ 59
def prefixEnd_2774730 : Nat := 4983230072969 + 3 ^ 40 * 2774730 * 2
def baseEnd_2774730 : Nat := 949846784300022726542837

theorem tailTrace_2774730 : CollatzResearch.WordTrace tailWord_2774730 prefixEnd_2774730 949846784300022726542837 := by
  unfold tailWord_2774730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25300679309408642750276411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67468478158423047334070429 25300679309408642750276411)
  ·
    refine ⟨37951018964112964125414617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25300679309408642750276411 37951018964112964125414617)
    ·
      refine ⟨28463264223084723094060963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37951018964112964125414617 28463264223084723094060963)
      ·
        refine ⟨42694896334627084641091445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28463264223084723094060963 42694896334627084641091445)
        ·
          refine ⟨4002646531371289185102323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42694896334627084641091445 4002646531371289185102323)
          ·
            refine ⟨6003969797056933777653485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002646531371289185102323 6003969797056933777653485)
            ·
              refine ⟨2251488673896350166620057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6003969797056933777653485 2251488673896350166620057)
              ·
                refine ⟨1688616505422262624965043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251488673896350166620057 1688616505422262624965043)
                ·
                  refine ⟨2532924758133393937447565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688616505422262624965043 2532924758133393937447565)
                  ·
                    refine ⟨949846784300022726542837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2532924758133393937447565 949846784300022726542837)
                    ·
                      rfl

theorem cell22_2774730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2774730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774730 prefixEnd_2774730 := by exact prefixLift 2774730
  have htrace : WordTrace (prefixWord ++ tailWord_2774730) baseStart_2774730 baseEnd_2774730 := by
    simpa [prefixWord, tailWord_2774730, baseEnd_2774730] using wordTrace_append hprefix tailTrace_2774730
  have hstable : (prefixWord ++ tailWord_2774730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774730).length < 2 ^ (prefixWord ++ tailWord_2774730).sum := by decide
  have hdescent : baseEnd_2774730 < baseStart_2774730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774769 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 1, 5]
def baseStart_2774769 : Nat := 118140960795 + 2774769 * 2 ^ 59
def prefixEnd_2774769 : Nat := 4983230072969 + 3 ^ 40 * 2774769 * 2
def baseEnd_2774769 : Nat := 949860134797039624817717

theorem tailTrace_2774769 : CollatzResearch.WordTrace tailWord_2774769 prefixEnd_2774769 949860134797039624817717 := by
  unfold tailWord_2774769
  simp only [CollatzResearch.WordTrace]
  refine ⟨101204139684493280661775361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67469426456328853774516907 101204139684493280661775361)
  ·
    refine ⟨75903104763369960496331521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101204139684493280661775361 75903104763369960496331521)
    ·
      refine ⟨56927328572527470372248641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75903104763369960496331521 56927328572527470372248641)
      ·
        refine ⟨42695496429395602779186481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56927328572527470372248641 42695496429395602779186481)
        ·
          refine ⟨32021622322046702084389861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42695496429395602779186481 32021622322046702084389861)
          ·
            refine ⟨6004054185383756640823099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32021622322046702084389861 6004054185383756640823099)
            ·
              refine ⟨9006081278075634961234649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004054185383756640823099 9006081278075634961234649)
              ·
                refine ⟨6754560958556726220925987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006081278075634961234649 6754560958556726220925987)
                ·
                  refine ⟨10131841437835089331388981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754560958556726220925987 10131841437835089331388981)
                  ·
                    refine ⟨949860134797039624817717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10131841437835089331388981 949860134797039624817717)
                    ·
                      rfl

theorem cell22_2774769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_2774769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774769 prefixEnd_2774769 := by exact prefixLift 2774769
  have htrace : WordTrace (prefixWord ++ tailWord_2774769) baseStart_2774769 baseEnd_2774769 := by
    simpa [prefixWord, tailWord_2774769, baseEnd_2774769] using wordTrace_append hprefix tailTrace_2774769
  have hstable : (prefixWord ++ tailWord_2774769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774769).length < 2 ^ (prefixWord ++ tailWord_2774769).sum := by decide
  have hdescent : baseEnd_2774769 < baseStart_2774769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774788 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_2774788 : Nat := 118140960795 + 2774788 * 2 ^ 59
def prefixEnd_2774788 : Nat := 4983230072969 + 3 ^ 40 * 2774788 * 2
def baseEnd_2774788 : Nat := 316622212961776636197553

theorem tailTrace_2774788 : CollatzResearch.WordTrace tailWord_2774788 prefixEnd_2774788 316622212961776636197553 := by
  unfold tailWord_2774788
  simp only [CollatzResearch.WordTrace]
  refine ⟨50602416335712223453358509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67469888447616297937811345 50602416335712223453358509)
  ·
    refine ⟨18975906125892083795009441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50602416335712223453358509 18975906125892083795009441)
    ·
      refine ⟨14231929594419062846257081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18975906125892083795009441 14231929594419062846257081)
      ·
        refine ⟨10673947195814297134692811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14231929594419062846257081 10673947195814297134692811)
        ·
          refine ⟨16010920793721445702039217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10673947195814297134692811 16010920793721445702039217)
          ·
            refine ⟨12008190595291084276529413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16010920793721445702039217 12008190595291084276529413)
            ·
              refine ⟨2251535736617078301849265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12008190595291084276529413 2251535736617078301849265)
              ·
                refine ⟨1688651802462808726386949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251535736617078301849265 1688651802462808726386949)
                ·
                  refine ⟨316622212961776636197553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688651802462808726386949 316622212961776636197553)
                  ·
                    rfl

theorem cell22_2774788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_2774788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774788 prefixEnd_2774788 := by exact prefixLift 2774788
  have htrace : WordTrace (prefixWord ++ tailWord_2774788) baseStart_2774788 baseEnd_2774788 := by
    simpa [prefixWord, tailWord_2774788, baseEnd_2774788] using wordTrace_append hprefix tailTrace_2774788
  have hstable : (prefixWord ++ tailWord_2774788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774788).length < 2 ^ (prefixWord ++ tailWord_2774788).sum := by decide
  have hdescent : baseEnd_2774788 < baseStart_2774788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774882 : List Nat := [3, 3, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_2774882 : Nat := 118140960795 + 2774882 * 2 ^ 59
def prefixEnd_2774882 : Nat := 4983230072969 + 3 ^ 40 * 2774882 * 2
def baseEnd_2774882 : Nat := 949898817006344996742371

theorem tailTrace_2774882 : CollatzResearch.WordTrace tailWord_2774882 prefixEnd_2774882 949898817006344996742371 := by
  unfold tailWord_2774882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25302065283270975240159725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67472174088722600640425933 25302065283270975240159725)
  ·
    refine ⟨9488274481226615715059897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25302065283270975240159725 9488274481226615715059897)
    ·
      refine ⟨7116205860919961786294923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9488274481226615715059897 7116205860919961786294923)
      ·
        refine ⟨10674308791379942679442385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7116205860919961786294923 10674308791379942679442385)
        ·
          refine ⟨8005731593534957009581789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10674308791379942679442385 8005731593534957009581789)
          ·
            refine ⟨3002149347575608878593171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8005731593534957009581789 3002149347575608878593171)
            ·
              refine ⟨4503224021363413317889757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002149347575608878593171 4503224021363413317889757)
              ·
                refine ⟨1688709008011279994208659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4503224021363413317889757 1688709008011279994208659)
                ·
                  refine ⟨2533063512016919991312989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688709008011279994208659 2533063512016919991312989)
                  ·
                    refine ⟨949898817006344996742371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533063512016919991312989 949898817006344996742371)
                    ·
                      rfl

theorem cell22_2774882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_2774882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774882 prefixEnd_2774882 := by exact prefixLift 2774882
  have htrace : WordTrace (prefixWord ++ tailWord_2774882) baseStart_2774882 baseEnd_2774882 := by
    simpa [prefixWord, tailWord_2774882, baseEnd_2774882] using wordTrace_append hprefix tailTrace_2774882
  have hstable : (prefixWord ++ tailWord_2774882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774882).length < 2 ^ (prefixWord ++ tailWord_2774882).sum := by decide
  have hdescent : baseEnd_2774882 < baseStart_2774882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774906 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_2774906 : Nat := 118140960795 + 2774906 * 2 ^ 59
def prefixEnd_2774906 : Nat := 4983230072969 + 3 ^ 40 * 2774906 * 2
def baseEnd_2774906 : Nat := 316635677565605644714099

theorem tailTrace_2774906 : CollatzResearch.WordTrace tailWord_2774906 prefixEnd_2774906 316635677565605644714099 := by
  unfold tailWord_2774906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25302284121249238264878143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67472757656664635373008381 25302284121249238264878143)
  ·
    refine ⟨37953426181873857397317215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25302284121249238264878143 37953426181873857397317215)
    ·
      refine ⟨56930139272810786095975823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37953426181873857397317215 56930139272810786095975823)
      ·
        refine ⟨85395208909216179143963735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56930139272810786095975823 85395208909216179143963735)
        ·
          refine ⟨128092813363824268715945603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85395208909216179143963735 128092813363824268715945603)
          ·
            refine ⟨192139220045736403073918405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128092813363824268715945603 192139220045736403073918405)
            ·
              refine ⟨36026103758575575576359701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192139220045736403073918405 36026103758575575576359701)
              ·
                refine ⟨1688723613683230105141861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36026103758575575576359701 1688723613683230105141861)
                ·
                  refine ⟨316635677565605644714099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688723613683230105141861 316635677565605644714099)
                  ·
                    rfl

theorem cell22_2774906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_2774906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774906 prefixEnd_2774906 := by exact prefixLift 2774906
  have htrace : WordTrace (prefixWord ++ tailWord_2774906) baseStart_2774906 baseEnd_2774906 := by
    simpa [prefixWord, tailWord_2774906, baseEnd_2774906] using wordTrace_append hprefix tailTrace_2774906
  have hstable : (prefixWord ++ tailWord_2774906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774906).length < 2 ^ (prefixWord ++ tailWord_2774906).sum := by decide
  have hdescent : baseEnd_2774906 < baseStart_2774906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774996 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2774996 : Nat := 118140960795 + 2774996 * 2 ^ 59
def prefixEnd_2774996 : Nat := 4983230072969 + 3 ^ 40 * 2774996 * 2
def baseEnd_2774996 : Nat := 316645947178695566464007

theorem tailTrace_2774996 : CollatzResearch.WordTrace tailWord_2774996 prefixEnd_2774996 316645947178695566464007 := by
  unfold tailWord_2774996
  simp only [CollatzResearch.WordTrace]
  refine ⟨50606209527335449215144421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67474946036447265620192561 50606209527335449215144421)
  ·
    refine ⟨9488664286375396727839579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50606209527335449215144421 9488664286375396727839579)
    ·
      refine ⟨14232996429563095091759369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9488664286375396727839579 14232996429563095091759369)
      ·
        refine ⟨10674747322172321318819527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14232996429563095091759369 10674747322172321318819527)
        ·
          refine ⟨16012120983258481978229291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10674747322172321318819527 16012120983258481978229291)
          ·
            refine ⟨24018181474887722967343937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012120983258481978229291 24018181474887722967343937)
            ·
              refine ⟨18013636106165792225507953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24018181474887722967343937 18013636106165792225507953)
              ·
                refine ⟨13510227079624344169130965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18013636106165792225507953 13510227079624344169130965)
                ·
                  refine ⟨316645947178695566464007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13510227079624344169130965 316645947178695566464007)
                  ·
                    rfl

theorem cell22_2774996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2774996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2774996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2774996 prefixEnd_2774996 := by exact prefixLift 2774996
  have htrace : WordTrace (prefixWord ++ tailWord_2774996) baseStart_2774996 baseEnd_2774996 := by
    simpa [prefixWord, tailWord_2774996, baseEnd_2774996] using wordTrace_append hprefix tailTrace_2774996
  have hstable : (prefixWord ++ tailWord_2774996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774996).length < 2 ^ (prefixWord ++ tailWord_2774996).sum := by decide
  have hdescent : baseEnd_2774996 < baseStart_2774996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775000 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 1, 3]
def baseStart_2775000 : Nat := 118140960795 + 2775000 * 2 ^ 59
def prefixEnd_2775000 : Nat := 4983230072969 + 3 ^ 40 * 2775000 * 2
def baseEnd_2775000 : Nat := 949939210817832022292009

theorem tailTrace_2775000 : CollatzResearch.WordTrace tailWord_2775000 prefixEnd_2775000 949939210817832022292009 := by
  unfold tailWord_2775000
  simp only [CollatzResearch.WordTrace]
  refine ⟨50606282473328203556717227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67475043297770938075622969 50606282473328203556717227)
  ·
    refine ⟨75909423709992305335075841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50606282473328203556717227 75909423709992305335075841)
    ·
      refine ⟨56932067782494229001306881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75909423709992305335075841 56932067782494229001306881)
      ·
        refine ⟨42699050836870671750980161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56932067782494229001306881 42699050836870671750980161)
        ·
          refine ⟨32024288127653003813235121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42699050836870671750980161 32024288127653003813235121)
          ·
            refine ⟨24018216095739752859926341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32024288127653003813235121 24018216095739752859926341)
            ·
              refine ⟨4503415517951203661236189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24018216095739752859926341 4503415517951203661236189)
              ·
                refine ⟨1688780819231701372963571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4503415517951203661236189 1688780819231701372963571)
                ·
                  refine ⟨2533171228847552059445357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1688780819231701372963571 2533171228847552059445357)
                  ·
                    refine ⟨949939210817832022292009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2533171228847552059445357 949939210817832022292009)
                    ·
                      rfl

theorem cell22_2775000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_2775000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2775000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2775000 prefixEnd_2775000 := by exact prefixLift 2775000
  have htrace : WordTrace (prefixWord ++ tailWord_2775000) baseStart_2775000 baseEnd_2775000 := by
    simpa [prefixWord, tailWord_2775000, baseEnd_2775000] using wordTrace_append hprefix tailTrace_2775000
  have hstable : (prefixWord ++ tailWord_2775000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775000).length < 2 ^ (prefixWord ++ tailWord_2775000).sum := by decide
  have hdescent : baseEnd_2775000 < baseStart_2775000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
